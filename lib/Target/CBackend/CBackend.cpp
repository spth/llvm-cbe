//===-- CBackend.cpp - Library for converting LLVM code to C --------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This library converts LLVM code to C code, compilable by GCC and other C
// compilers.
//
//===----------------------------------------------------------------------===//

#include "CBackend.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Support/Host.h"
#include "llvm/Config/llvm-config.h"
#include <algorithm>
#include <cstdio>

// Some ms header decided to define setjmp as _setjmp, undo this for this file
// since we don't need it
#undef setjmp

using namespace CBackend;
using namespace llvm;
using std::string;

extern "C" void LLVMInitializeCBackendTarget() {
  // Register the target.
  RegisterTargetMachine<CTargetMachine> X(TheCBackendTarget);
}

char CWriter::ID = 0;

static bool isEmptyType(Type *Ty) {
    if (StructType *STy = dyn_cast<StructType>(Ty))
        return STy->getNumElements() == 0 ||
            std::all_of(STy->element_begin(), STy->element_end(), [](Type *T){ return isEmptyType(T); });
    if (VectorType *VTy = dyn_cast<VectorType>(Ty))
        return VTy->getNumElements() == 0 ||
            isEmptyType(VTy->getElementType());
    if (ArrayType *ATy = dyn_cast<ArrayType>(Ty))
        return ATy->getNumElements() == 0 ||
            isEmptyType(ATy->getElementType());
    return Ty->isVoidTy();
}

bool CWriter::isEmptyType(Type *Ty) const {
    return ::isEmptyType(Ty);
}

/// isAddressExposed - Return true if the specified value's name needs to
/// have its address taken in order to get a C value of the correct type.
/// This happens for global variables, byval parameters, and direct allocas.
bool CWriter::isAddressExposed(Value *V) const {
  if (Argument *A = dyn_cast<Argument>(V))
    return ByValParams.count(A);
  return isa<GlobalVariable>(V) || isDirectAlloca(V);
}

// isInlinableInst - Attempt to inline instructions into their uses to build
// trees as much as possible.  To do this, we have to consistently decide
// what is acceptable to inline, so that variable declarations don't get
// printed and an extra copy of the expr is not emitted.
//
bool CWriter::isInlinableInst(Instruction &I) const {
  // Always inline cmp instructions, even if they are shared by multiple
  // expressions.  GCC generates horrible code if we don't.
  if (isa<CmpInst>(I))
    return true;

  // Must be an expression, must be used exactly once.  If it is dead, we
  // emit it inline where it would go.
  if (isEmptyType(I.getType()) || !I.hasOneUse() ||
      isa<TerminatorInst>(I) || isa<CallInst>(I) || isa<PHINode>(I) ||
      isa<LoadInst>(I) || isa<VAArgInst>(I) || isa<InsertElementInst>(I) ||
      isa<InsertValueInst>(I) || isa<AllocaInst>(I))
    // Don't inline a load across a store or other bad things!
    return false;

  // Must not be used in inline asm, extractelement, or shufflevector.
  if (I.hasOneUse()) {
    Instruction &User = cast<Instruction>(*I.user_back());
    if (isInlineAsm(User))
      return false;
  }

  // Only inline instruction it if it's use is in the same BB as the inst.
  return I.getParent() == cast<Instruction>(I.user_back())->getParent();
}

// isDirectAlloca - Define fixed sized allocas in the entry block as direct
// variables which are accessed with the & operator.  This causes GCC to
// generate significantly better code than to emit alloca calls directly.
//
AllocaInst *CWriter::isDirectAlloca(Value *V) const {
  AllocaInst *AI = dyn_cast<AllocaInst>(V);
  if (!AI) return 0;
  if (AI->isArrayAllocation())
    return 0;   // FIXME: we can also inline fixed size array allocas!
  if (AI->getParent() != &AI->getParent()->getParent()->getEntryBlock())
    return 0;
  return AI;
}

// isInlineAsm - Check if the instruction is a call to an inline asm chunk.
bool CWriter::isInlineAsm(Instruction& I) const {
  if (CallInst *CI = dyn_cast<CallInst>(&I))
    return isa<InlineAsm>(CI->getCalledValue());
  return false;
}

bool CWriter::runOnFunction(Function &F) {
 // Do not codegen any 'available_externally' functions at all, they have
 // definitions outside the translation unit.
 if (F.hasAvailableExternallyLinkage())
   return false;

  LI = &getAnalysis<LoopInfoWrapperPass>().getLoopInfo();

  // Get rid of intrinsics we can't handle.
  lowerIntrinsics(F);

  // Output all floating point constants that cannot be printed accurately.
  printFloatingPointConstants(F);

  printFunction(F);

  LI = NULL;

  return true; // may have lowered an IntrinsicCall
}

static string CBEMangle(const string &S) {
  string Result;

  for (unsigned i = 0, e = S.size(); i != e; ++i)
    if (isalnum(S[i]) || S[i] == '_') {
      Result += S[i];
    } else {
      Result += '_';
      Result += 'A'+(S[i]&15);
      Result += 'A'+((S[i]>>4)&15);
      Result += '_';
    }
  return Result;
}

raw_ostream &
CWriter::printTypeString(raw_ostream &Out, Type *Ty, bool isSigned) {
  if (StructType *ST = dyn_cast<StructType>(Ty)) {
    assert(!isEmptyType(ST));
    TypedefDeclTypes.insert(Ty);

    if (!ST->isLiteral() && !ST->getName().empty())
      return Out << "struct_" << CBEMangle(ST->getName());

    unsigned &id = UnnamedStructIDs[ST];
    if (id == 0)
      id = ++NextAnonStructNumber;
    return Out << "unnamed_" + utostr(id);
  }

  if (Ty->isPointerTy()) {
    Out << "p";
    return printTypeString(Out, Ty->getPointerElementType(), isSigned);
  }

  switch (Ty->getTypeID()) {
  case Type::VoidTyID:   return Out << "void";
  case Type::IntegerTyID: {
    unsigned NumBits = cast<IntegerType>(Ty)->getBitWidth();
    if (NumBits == 1)
      return Out << "bool";
    else {
      assert(NumBits <= 128 && "Bit widths > 128 not implemented yet");
      return Out << (isSigned?"i":"u") << NumBits;
    }
  }
  case Type::FloatTyID:    return Out << "f32";
  case Type::DoubleTyID:   return Out << "f64";
  case Type::X86_FP80TyID: return Out << "f80";
  case Type::PPC_FP128TyID:
  case Type::FP128TyID:    return Out << "f128";

  case Type::X86_MMXTyID:
    return Out << (isSigned ? "i32y2" : "u32y2");

  case Type::VectorTyID: {
    TypedefDeclTypes.insert(Ty);
    VectorType *VTy = cast<VectorType>(Ty);
    assert(VTy->getNumElements() != 0);
    printTypeString(Out, VTy->getElementType(), isSigned);
    return Out << "x" << VTy->getNumElements();
  }

  case Type::ArrayTyID: {
    TypedefDeclTypes.insert(Ty);
    ArrayType *ATy = cast<ArrayType>(Ty);
    assert(ATy->getNumElements() != 0);
    printTypeString(Out, ATy->getElementType(), isSigned);
    return Out << "a" << ATy->getNumElements();
  }

  default:
#ifndef NDEBUG
    errs() << "Unknown primitive type: " << *Ty << "\n";
#endif
    llvm_unreachable(0);
  }
}

string CWriter::getStructName(StructType *ST) {
  assert(ST->getNumElements() != 0);
  if (!ST->isLiteral() && !ST->getName().empty())
    return "struct l_struct_" + CBEMangle(ST->getName().str());

  unsigned &id = UnnamedStructIDs[ST];
  if (id == 0)
    id = ++NextAnonStructNumber;
  return "struct l_unnamed_" + utostr(id);
}

string CWriter::getFunctionName(FunctionType *FT, std::pair<AttributeSet, CallingConv::ID> PAL) {
  unsigned &id = UnnamedFunctionIDs[std::make_pair(FT, PAL)];
  if (id == 0)
      id = ++NextFunctionNumber;
  return "l_fptr_" + utostr(id);
}

string CWriter::getArrayName(ArrayType *AT) {
    string astr;
    raw_string_ostream ArrayInnards(astr);
    // Arrays are wrapped in structs to allow them to have normal
    // value semantics (avoiding the array "decay").
    assert(!isEmptyType(AT));
    printTypeName(ArrayInnards, AT->getElementType(), false);
    return "struct l_array_" + utostr(AT->getNumElements()) + '_' + CBEMangle(ArrayInnards.str());
}

string CWriter::getVectorName(VectorType *VT, bool Aligned) {
    string astr;
    raw_string_ostream VectorInnards(astr);
    // Vectors are handled like arrays
    assert(!isEmptyType(VT));
    if (Aligned)
      Out << "__MSALIGN__(" << TD->getABITypeAlignment(VT) << ") ";
    printTypeName(VectorInnards, VT->getElementType(), false);
    return "struct l_vector_" + utostr(VT->getNumElements()) + '_' + CBEMangle(VectorInnards.str());
}


string CBackend::getCmpPredicateName(CmpInst::Predicate P) {
  switch (P) {
  case FCmpInst::FCMP_FALSE: return "0";
  case FCmpInst::FCMP_OEQ: return "oeq";
  case FCmpInst::FCMP_OGT: return "ogt";
  case FCmpInst::FCMP_OGE: return "oge";
  case FCmpInst::FCMP_OLT: return "olt";
  case FCmpInst::FCMP_OLE: return "ole";
  case FCmpInst::FCMP_ONE: return "one";
  case FCmpInst::FCMP_ORD: return "ord";
  case FCmpInst::FCMP_UNO: return "uno";
  case FCmpInst::FCMP_UEQ: return "ueq";
  case FCmpInst::FCMP_UGT: return "ugt";
  case FCmpInst::FCMP_UGE: return "uge";
  case FCmpInst::FCMP_ULT: return "ult";
  case FCmpInst::FCMP_ULE: return "ule";
  case FCmpInst::FCMP_UNE: return "une";
  case FCmpInst::FCMP_TRUE: return "1";
  case ICmpInst::ICMP_EQ:  return "eq";
  case ICmpInst::ICMP_NE:  return "ne";
  case ICmpInst::ICMP_ULE: return "ule";
  case ICmpInst::ICMP_SLE: return "sle";
  case ICmpInst::ICMP_UGE: return "uge";
  case ICmpInst::ICMP_SGE: return "sge";
  case ICmpInst::ICMP_ULT: return "ult";
  case ICmpInst::ICMP_SLT: return "slt";
  case ICmpInst::ICMP_UGT: return "ugt";
  case ICmpInst::ICMP_SGT: return "sgt";
  default:
#ifndef NDEBUG
    errs() << "Invalid icmp predicate!" << P;
#endif
    llvm_unreachable(0);
  }
}


raw_ostream &
CWriter::printSimpleType(raw_ostream &Out, Type *Ty, bool isSigned) {
  assert((Ty->isSingleValueType() || Ty->isVoidTy()) &&
         "Invalid type for printSimpleType");
  switch (Ty->getTypeID()) {
  case Type::VoidTyID:   return Out << "void";
  case Type::IntegerTyID: {
    unsigned NumBits = cast<IntegerType>(Ty)->getBitWidth();
    if (NumBits == 1)
      return Out << "bool";
    else if (NumBits <= 8)
      return Out << (isSigned?"int8_t":"uint8_t");
    else if (NumBits <= 16)
      return Out << (isSigned?"int16_t":"uint16_t");
    else if (NumBits <= 32)
      return Out << (isSigned?"int32_t":"uint32_t");
    else if (NumBits <= 64)
      return Out << (isSigned?"int64_t":"uint64_t");
    else {
      UsesInt128 = true;
      assert(NumBits <= 128 && "Bit widths > 128 not implemented yet");
      return Out << (isSigned?"int128_t":"uint128_t");
    }
  }
  case Type::FloatTyID:  return Out << "float";
  case Type::DoubleTyID: return Out << "double";
  // Lacking emulation of FP80 on PPC, etc., we assume whichever of these is
  // present matches host 'long double'.
  case Type::X86_FP80TyID:
  case Type::PPC_FP128TyID:
  case Type::FP128TyID:  return Out << "long double";

  case Type::X86_MMXTyID:
    return Out << (isSigned?"int32_t":"uint32_t") << " __attribute__((vector_size(8)))";

  default:
#ifndef NDEBUG
    errs() << "Unknown primitive type: " << *Ty << "\n";
#endif
    llvm_unreachable(0);
  }
}

// Pass the Type* and the variable name and this prints out the variable
// declaration.
//
raw_ostream &CWriter::printTypeName(raw_ostream &Out, Type *Ty, bool isSigned, std::pair<AttributeSet, CallingConv::ID> PAL) {
  if (Ty->isSingleValueType() || Ty->isVoidTy()) {
    if (!Ty->isPointerTy() && !Ty->isVectorTy())
      return printSimpleType(Out, Ty, isSigned);
  }

  if (isEmptyType(Ty))
    return Out << "void";

  switch (Ty->getTypeID()) {
  case Type::FunctionTyID: {
    FunctionType *FTy = cast<FunctionType>(Ty);
    return Out << getFunctionName(FTy, PAL);
  }
  case Type::StructTyID: {
    TypedefDeclTypes.insert(Ty);
    return Out << getStructName(cast<StructType>(Ty));
  }

  case Type::PointerTyID: {
    Type *ElTy = Ty->getPointerElementType();
    return printTypeName(Out, ElTy, false) << '*';
  }

  case Type::ArrayTyID: {
    TypedefDeclTypes.insert(Ty);
    return Out << getArrayName(cast<ArrayType>(Ty));
  }

  case Type::VectorTyID: {
    TypedefDeclTypes.insert(Ty);
    return Out << getVectorName(cast<VectorType>(Ty), true);
  }

  default:
#ifndef NDEBUG
    errs() << "Unexpected type: " << *Ty << "\n";
#endif
    llvm_unreachable(0);
  }
}

raw_ostream &CWriter::printTypeNameUnaligned(raw_ostream &Out, Type *Ty, bool isSigned) {
  if (VectorType *VTy = dyn_cast<VectorType>(Ty)) {
    // MSVC doesn't handle __declspec(align) on parameters,
    // but we specify it for Vector (hoping the compiler will vectorize it)
    // so we need to avoid it sometimes
    TypedefDeclTypes.insert(VTy);
    return Out << getVectorName(VTy, false);
  }
  return printTypeName(Out, Ty, isSigned);
}

raw_ostream &CWriter::printStructDeclaration(raw_ostream &Out, StructType *STy) {
  if (STy->isPacked())
    Out << "#ifdef _MSC_VER\n#pragma pack(push, 1)\n#endif\n";
  Out << getStructName(STy) << " {\n";
  unsigned Idx = 0;
  for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
    Out << "  ";
    bool empty = isEmptyType(*I);
    if (empty)
        Out << "/* "; // skip zero-sized types
    printTypeName(Out, *I, false) << " field" << utostr(Idx);
    if (empty)
        Out << " */"; // skip zero-sized types
    else
        Out << ";\n";
  }
  Out << '}';
  if (STy->isPacked())
    Out << " __attribute__ ((packed))";
  Out << ";\n";
  if (STy->isPacked())
    Out << "#ifdef _MSC_VER\n#pragma pack(pop)\n#endif\n";
  return Out;
}

raw_ostream &CWriter::printFunctionDeclaration(raw_ostream &Out, FunctionType *Ty,
                                               std::pair<AttributeSet, CallingConv::ID> PAL) {
  Out << "typedef ";
  printFunctionProto(Out, Ty, PAL, getFunctionName(Ty, PAL), NULL);
  return Out << ";\n";
}

raw_ostream &CWriter::printFunctionProto(raw_ostream &Out, FunctionType *FTy,
                                         std::pair<AttributeSet, CallingConv::ID> Attrs,
                                         const string &Name,
                                         Function::ArgumentListType *ArgList) {
  AttributeSet &PAL = Attrs.first;

  if (PAL.hasAttribute(AttributeSet::FunctionIndex, Attribute::NoReturn))
    Out << "__noreturn ";

  // Should this function actually return a struct by-value?
  bool isStructReturn = PAL.hasAttribute(1, Attribute::StructRet) ||
                        PAL.hasAttribute(2, Attribute::StructRet);
  // Get the return type for the function.
  Type *RetTy;
  if (!isStructReturn)
    RetTy = FTy->getReturnType();
  else {
    // If this is a struct-return function, print the struct-return type.
    RetTy = cast<PointerType>(FTy->getParamType(0))->getElementType();
  }
  printTypeName(Out, RetTy,
    /*isSigned=*/PAL.hasAttribute(AttributeSet::ReturnIndex, Attribute::SExt));

  switch (Attrs.second) {
   case CallingConv::C:
    break;
   case CallingConv::X86_StdCall:
    Out << " __stdcall";
    break;
   case CallingConv::X86_FastCall:
    Out << " __fastcall";
    break;
   case CallingConv::X86_ThisCall:
    Out << " __thiscall";
    break;
   default:
    assert(0 && "Encountered Unhandled Calling Convention");
    break;
  }
  Out << ' ' << Name << '(';

  unsigned Idx = 1;
  bool PrintedArg = false;
  FunctionType::param_iterator I = FTy->param_begin(), E = FTy->param_end();
  Function::arg_iterator ArgName = ArgList ? ArgList->begin() : Function::arg_iterator();

  // If this is a struct-return function, don't print the hidden
  // struct-return argument.
  if (isStructReturn) {
    assert(I != E && "Invalid struct return function!");
    ++I;
    ++Idx;
    if (ArgList) ++ArgName;
  }

  for (; I != E; ++I) {
    Type *ArgTy = *I;
    if (PAL.hasAttribute(Idx, Attribute::ByVal)) {
      assert(ArgTy->isPointerTy());
      ArgTy = cast<PointerType>(ArgTy)->getElementType();
    }
    if (PrintedArg)
      Out << ", ";
    printTypeNameUnaligned(Out, ArgTy,
      /*isSigned=*/PAL.hasAttribute(Idx, Attribute::SExt));
    PrintedArg = true;
    ++Idx;
    if (ArgList) {
      Out << ' ' << GetValueName(&(*ArgName));
      ++ArgName;
    }
  }

  if (FTy->isVarArg()) {
    if (!PrintedArg) {
      Out << "int"; //dummy argument for empty vaarg functs
      if (ArgList) Out << " vararg_dummy_arg";
    }
    Out << ", ...";
  } else if (!PrintedArg) {
    Out << "void";
  }
  Out << ")";
  return Out;
}

raw_ostream &CWriter::printArrayDeclaration(raw_ostream &Out, ArrayType *ATy) {
  assert(!isEmptyType(ATy));
  // Arrays are wrapped in structs to allow them to have normal
  // value semantics (avoiding the array "decay").
  Out << getArrayName(ATy) << " {\n  ";
  printTypeName(Out, ATy->getElementType());
  Out << " array[" << utostr(ATy->getNumElements()) << "];\n};\n";
  return Out;
}

raw_ostream &CWriter::printVectorDeclaration(raw_ostream &Out, VectorType *VTy) {
  assert(!isEmptyType(VTy));
  // Vectors are printed like arrays
  Out << getVectorName(VTy, false) << " {\n  ";
  printTypeName(Out, VTy->getElementType());
  Out << " vector[" << utostr(VTy->getNumElements()) << "];\n} __attribute__((aligned(" << TD->getABITypeAlignment(VTy) << ")));\n";
  return Out;
}

void CWriter::printConstantArray(ConstantArray *CPA, enum OperandContext Context) {
  printConstant(cast<Constant>(CPA->getOperand(0)), Context);
  for (unsigned i = 1, e = CPA->getNumOperands(); i != e; ++i) {
    Out << ", ";
    printConstant(cast<Constant>(CPA->getOperand(i)), Context);
  }
}

void CWriter::printConstantVector(ConstantVector *CP, enum OperandContext Context) {
  printConstant(cast<Constant>(CP->getOperand(0)), Context);
  for (unsigned i = 1, e = CP->getNumOperands(); i != e; ++i) {
    Out << ", ";
    printConstant(cast<Constant>(CP->getOperand(i)), Context);
  }
}

void CWriter::printConstantDataSequential(ConstantDataSequential *CDS, enum OperandContext Context) {
  printConstant(CDS->getElementAsConstant(0), Context);
  for (unsigned i = 1, e = CDS->getNumElements(); i != e; ++i) {
    Out << ", ";
    printConstant(CDS->getElementAsConstant(i), Context);
  }
}

bool CWriter::printConstantString(Constant *C, enum OperandContext Context) {
  // As a special case, print the array as a string if it is an array of
  // ubytes or an array of sbytes with positive values.
  ConstantDataSequential *CDS = dyn_cast<ConstantDataSequential>(C);
  if (!CDS || !CDS->isCString()) return false;
  if (Context != ContextStatic) return false; // TODO

  Out << "{ \"";
  // Keep track of whether the last number was a hexadecimal escape.
  bool LastWasHex = false;

  StringRef Bytes = CDS->getAsString();

  // Do not include the last character, which we know is null
  for (unsigned i = 0, e = Bytes.size() - 1; i < e; ++i) {
    unsigned char C = Bytes[i];

    // Print it out literally if it is a printable character.  The only thing
    // to be careful about is when the last letter output was a hex escape
    // code, in which case we have to be careful not to print out hex digits
    // explicitly (the C compiler thinks it is a continuation of the previous
    // character, sheesh...)
    //
    if (isprint(C) && (!LastWasHex || !isxdigit(C))) {
      LastWasHex = false;
      if (C == '"' || C == '\\')
        Out << "\\" << (char)C;
      else
        Out << (char)C;
    } else {
      LastWasHex = false;
      switch (C) {
        case '\n': Out << "\\n"; break;
        case '\t': Out << "\\t"; break;
        case '\r': Out << "\\r"; break;
        case '\v': Out << "\\v"; break;
        case '\a': Out << "\\a"; break;
        case '\"': Out << "\\\""; break;
        case '\'': Out << "\\\'"; break;
        default:
          Out << "\\x";
          Out << (char)(( C/16  < 10) ? ( C/16 +'0') : ( C/16 -10+'A'));
          Out << (char)(((C&15) < 10) ? ((C&15)+'0') : ((C&15)-10+'A'));
          LastWasHex = true;
          break;
      }
    }
  }
  Out << "\" }";
  return true;
}


// isFPCSafeToPrint - Returns true if we may assume that CFP may be written out
// textually as a double (rather than as a reference to a stack-allocated
// variable). We decide this by converting CFP to a string and back into a
// double, and then checking whether the conversion results in a bit-equal
// double to the original value of CFP. This depends on us and the target C
// compiler agreeing on the conversion process (which is pretty likely since we
// only deal in IEEE FP).
//

// TODO copied from CppBackend, new code should use raw_ostream
static inline string ftostr(const APFloat& V) {
  string Buf;
  if (&V.getSemantics() == &APFloat::IEEEdouble) {
    raw_string_ostream(Buf) << V.convertToDouble();
    return Buf;
  } else if (&V.getSemantics() == &APFloat::IEEEsingle) {
    raw_string_ostream(Buf) << (double)V.convertToFloat();
    return Buf;
  }
  return "<unknown format in ftostr>"; // error
}

static bool isFPCSafeToPrint(const ConstantFP *CFP) {
  bool ignored;
  // Do long doubles in hex for now.
  if (CFP->getType() != Type::getFloatTy(CFP->getContext()) &&
      CFP->getType() != Type::getDoubleTy(CFP->getContext()))
    return false;
  APFloat APF = APFloat(CFP->getValueAPF());  // copy
  if (CFP->getType() == Type::getFloatTy(CFP->getContext()))
    APF.convert(APFloat::IEEEdouble, APFloat::rmNearestTiesToEven, &ignored);
#if HAVE_PRINTF_A && ENABLE_CBE_PRINTF_A
  char Buffer[100];
  sprintf(Buffer, "%a", APF.convertToDouble());
  if (!strncmp(Buffer, "0x", 2) ||
      !strncmp(Buffer, "-0x", 3) ||
      !strncmp(Buffer, "+0x", 3))
    return APF.bitwiseIsEqual(APFloat(atof(Buffer)));
  return false;
#else
  string StrVal = ftostr(APF);

  while (StrVal[0] == ' ')
    StrVal.erase(StrVal.begin());

  // Check to make sure that the stringized number is not some string like "Inf"
  // or NaN.  Check that the string matches the "[-+]?[0-9]" regex.
  if ((StrVal[0] >= '0' && StrVal[0] <= '9') ||
      ((StrVal[0] == '-' || StrVal[0] == '+') &&
       (StrVal[1] >= '0' && StrVal[1] <= '9')))
    // Reparse stringized version!
    return APF.bitwiseIsEqual(APFloat(atof(StrVal.c_str())));
  return false;
#endif
}

/// Print out the casting for a cast operation. This does the double casting
/// necessary for conversion to the destination type, if necessary.
/// @brief Print a cast
void CWriter::printCast(unsigned opc, Type *SrcTy, Type *DstTy) {
  // Print the destination type cast
  switch (opc) {
    case Instruction::UIToFP:
    case Instruction::SIToFP:
    case Instruction::IntToPtr:
    case Instruction::Trunc:
    case Instruction::BitCast:
    case Instruction::FPExt:
    case Instruction::FPTrunc: // For these the DstTy sign doesn't matter
      Out << '(';
      printTypeName(Out, DstTy);
      Out << ')';
      break;
    case Instruction::ZExt:
    case Instruction::PtrToInt:
    case Instruction::FPToUI: // For these, make sure we get an unsigned dest
      Out << '(';
      printSimpleType(Out, DstTy, false);
      Out << ')';
      break;
    case Instruction::SExt:
    case Instruction::FPToSI: // For these, make sure we get a signed dest
      Out << '(';
      printSimpleType(Out, DstTy, true);
      Out << ')';
      break;
    default:
      llvm_unreachable("Invalid cast opcode");
  }

  // Print the source type cast
  switch (opc) {
    case Instruction::UIToFP:
    case Instruction::ZExt:
      Out << '(';
      printSimpleType(Out, SrcTy, false);
      Out << ')';
      break;
    case Instruction::SIToFP:
    case Instruction::SExt:
      Out << '(';
      printSimpleType(Out, SrcTy, true);
      Out << ')';
      break;
    case Instruction::IntToPtr:
    case Instruction::PtrToInt:
      // Avoid "cast to pointer from integer of different size" warnings
      Out << "(uintptr_t)";
      break;
    case Instruction::Trunc:
    case Instruction::BitCast:
    case Instruction::FPExt:
    case Instruction::FPTrunc:
    case Instruction::FPToSI:
    case Instruction::FPToUI:
      break; // These don't need a source cast.
    default:
      llvm_unreachable("Invalid cast opcode");
  }
}

// printConstant - The LLVM Constant to C Constant converter.
void CWriter::printConstant(Constant *CPV, enum OperandContext Context) {
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(CPV)) {
    assert(CE->getType()->isIntegerTy() || CE->getType()->isFloatingPointTy() || CE->getType()->isPointerTy()); // TODO: VectorType are valid here, but not supported
    switch (CE->getOpcode()) {
    case Instruction::Trunc:
    case Instruction::ZExt:
    case Instruction::SExt:
    case Instruction::FPTrunc:
    case Instruction::FPExt:
    case Instruction::UIToFP:
    case Instruction::SIToFP:
    case Instruction::FPToUI:
    case Instruction::FPToSI:
    case Instruction::PtrToInt:
    case Instruction::IntToPtr:
    case Instruction::BitCast:
      Out << "(";
      printCast(CE->getOpcode(), CE->getOperand(0)->getType(), CE->getType());
      if (CE->getOpcode() == Instruction::SExt &&
          CE->getOperand(0)->getType() == Type::getInt1Ty(CPV->getContext())) {
        // Make sure we really sext from bool here by subtracting from 0
        Out << "0-";
      }
      printConstant(CE->getOperand(0), ContextCasted);
      if (CE->getType() == Type::getInt1Ty(CPV->getContext()) &&
          (CE->getOpcode() == Instruction::Trunc ||
           CE->getOpcode() == Instruction::FPToUI ||
           CE->getOpcode() == Instruction::FPToSI ||
           CE->getOpcode() == Instruction::PtrToInt)) {
        // Make sure we really truncate to bool here by anding with 1
        Out << "&1u";
      }
      Out << ')';
      return;

    case Instruction::GetElementPtr:
      Out << "(";
      printGEPExpression(CE->getOperand(0), gep_type_begin(CPV), gep_type_end(CPV));
      Out << ")";
      return;
    case Instruction::Select:
      Out << '(';
      printConstant(CE->getOperand(0), ContextCasted);
      Out << '?';
      printConstant(CE->getOperand(1), ContextNormal);
      Out << ':';
      printConstant(CE->getOperand(2), ContextNormal);
      Out << ')';
      return;
    case Instruction::Add:
    case Instruction::FAdd:
    case Instruction::Sub:
    case Instruction::FSub:
    case Instruction::Mul:
    case Instruction::FMul:
    case Instruction::SDiv:
    case Instruction::UDiv:
    case Instruction::FDiv:
    case Instruction::URem:
    case Instruction::SRem:
    case Instruction::FRem:
    case Instruction::And:
    case Instruction::Or:
    case Instruction::Xor:
    case Instruction::ICmp:
    case Instruction::Shl:
    case Instruction::LShr:
    case Instruction::AShr:
    {
      Out << '(';
      bool NeedsClosingParens = printConstExprCast(CE);
      printConstantWithCast(CE->getOperand(0), CE->getOpcode());
      switch (CE->getOpcode()) {
      case Instruction::Add:
      case Instruction::FAdd: Out << " + "; break;
      case Instruction::Sub:
      case Instruction::FSub: Out << " - "; break;
      case Instruction::Mul:
      case Instruction::FMul: Out << " * "; break;
      case Instruction::URem:
      case Instruction::SRem:
      case Instruction::FRem: Out << " % "; break;
      case Instruction::UDiv:
      case Instruction::SDiv:
      case Instruction::FDiv: Out << " / "; break;
      case Instruction::And: Out << " & "; break;
      case Instruction::Or:  Out << " | "; break;
      case Instruction::Xor: Out << " ^ "; break;
      case Instruction::Shl: Out << " << "; break;
      case Instruction::LShr:
      case Instruction::AShr: Out << " >> "; break;
      case Instruction::ICmp:
        switch (CE->getPredicate()) {
          case ICmpInst::ICMP_EQ: Out << " == "; break;
          case ICmpInst::ICMP_NE: Out << " != "; break;
          case ICmpInst::ICMP_SLT:
          case ICmpInst::ICMP_ULT: Out << " < "; break;
          case ICmpInst::ICMP_SLE:
          case ICmpInst::ICMP_ULE: Out << " <= "; break;
          case ICmpInst::ICMP_SGT:
          case ICmpInst::ICMP_UGT: Out << " > "; break;
          case ICmpInst::ICMP_SGE:
          case ICmpInst::ICMP_UGE: Out << " >= "; break;
          default: llvm_unreachable("Illegal ICmp predicate");
        }
        break;
      default: llvm_unreachable("Illegal opcode here!");
      }
      printConstantWithCast(CE->getOperand(1), CE->getOpcode());
      if (NeedsClosingParens)
        Out << "))";
      Out << ')';
      return;
    }
    case Instruction::FCmp: {
      Out << '(';
      bool NeedsClosingParens = printConstExprCast(CE);
      if (CE->getPredicate() == FCmpInst::FCMP_FALSE)
        Out << "0";
      else if (CE->getPredicate() == FCmpInst::FCMP_TRUE)
        Out << "1";
      else {
        Out << "llvm_fcmp_" << getCmpPredicateName((CmpInst::Predicate)CE->getPredicate()) << "(";
        printConstant(CE->getOperand(0), ContextCasted);
        Out << ", ";
        printConstant(CE->getOperand(1), ContextCasted);
        Out << ")";
      }
      if (NeedsClosingParens)
        Out << "))";
      Out << ')';
      return;
    }
    default:
#ifndef NDEBUG
      errs() << "CWriter Error: Unhandled constant expression: "
           << *CE << "\n";
#endif
      llvm_unreachable(0);
    }
  } else if (isa<UndefValue>(CPV) && CPV->getType()->isSingleValueType()) {
    if (CPV->getType()->isVectorTy()) {
      if (Context == ContextStatic) {
        Out << "{}";
        return;
      }
      VectorType *VT = cast<VectorType>(CPV->getType());
      assert(!isEmptyType(VT));
      CtorDeclTypes.insert(VT);
      Out << "/*undef*/llvm_ctor_";
      printTypeString(Out, VT, false);
      Out << "(";
      Constant *Zero = Constant::getNullValue(VT->getElementType());
      unsigned NumElts = VT->getNumElements();
      for (unsigned i = 0; i != NumElts; ++i) {
        if (i) Out << ", ";
        printConstant(Zero, ContextCasted);
      }
      Out << ")";

    } else {
      Constant *Zero = Constant::getNullValue(CPV->getType());
      Out << "/*UNDEF*/";
      return printConstant(Zero, Context);
    }
    return;
  }

  if (ConstantInt *CI = dyn_cast<ConstantInt>(CPV)) {
    Type* Ty = CI->getType();
    unsigned ActiveBits = CI->getValue().getMinSignedBits();
    if (Ty == Type::getInt1Ty(CPV->getContext())) {
      Out << (CI->getZExtValue() ? '1' : '0');
    } else if (Context != ContextNormal &&
              ActiveBits < 64 &&
              Ty->getPrimitiveSizeInBits() < 64 &&
              ActiveBits < Ty->getPrimitiveSizeInBits()) {
      if (ActiveBits >= 32)
        Out << "INT64_C(";
      Out << CI->getSExtValue(); // most likely a shorter representation
      if (ActiveBits >= 32)
        Out << ")";
    } else if (Ty->getPrimitiveSizeInBits() < 32 && Context == ContextNormal) {
      Out << "((";
      printSimpleType(Out, Ty, false) << ')';
      if (CI->isMinValue(true))
        Out << CI->getZExtValue() << 'u';
      else
        Out << CI->getSExtValue();
      Out << ')';
    } else if (Ty->getPrimitiveSizeInBits() <= 32) {
      Out << CI->getZExtValue() << 'u';
    } else if (Ty->getPrimitiveSizeInBits() <= 64) {
      Out << "UINT64_C(" << CI->getZExtValue() << ")";
    } else if (Ty->getPrimitiveSizeInBits() <= 128) {
      const APInt &V = CI->getValue();
      const APInt &Vlo = V.getLoBits(64);
      const APInt &Vhi = V.getHiBits(64);
      Out << (Context == ContextStatic ? "UINT128_C" : "llvm_ctor_u128");
      Out << "(UINT64_C(" << Vhi.getZExtValue() << "), UINT64_C(" << Vlo.getZExtValue() << "))";
    }
    return;
  }

  switch (CPV->getType()->getTypeID()) {
  case Type::FloatTyID:
  case Type::DoubleTyID:
  case Type::X86_FP80TyID:
  case Type::PPC_FP128TyID:
  case Type::FP128TyID: {
    ConstantFP *FPC = cast<ConstantFP>(CPV);
    auto I = FPConstantMap.find(FPC);
    if (I != FPConstantMap.end()) {
      // Because of FP precision problems we must load from a stack allocated
      // value that holds the value in hex.
      Out << "(*(" << (FPC->getType() == Type::getFloatTy(CPV->getContext()) ?
                       "float" :
                       FPC->getType() == Type::getDoubleTy(CPV->getContext()) ?
                       "double" :
                       "long double")
          << "*)&FPConstant" << I->second << ')';
    } else {
      double V;
      if (FPC->getType() == Type::getFloatTy(CPV->getContext()))
        V = FPC->getValueAPF().convertToFloat();
      else if (FPC->getType() == Type::getDoubleTy(CPV->getContext()))
        V = FPC->getValueAPF().convertToDouble();
      else {
        // Long double.  Convert the number to double, discarding precision.
        // This is not awesome, but it at least makes the CBE output somewhat
        // useful.
        APFloat Tmp = FPC->getValueAPF();
        bool LosesInfo;
        Tmp.convert(APFloat::IEEEdouble, APFloat::rmTowardZero, &LosesInfo);
        V = Tmp.convertToDouble();
      }

      if (std::isnan(V)) {
        // The value is NaN

        // FIXME the actual NaN bits should be emitted.
        // The prefix for a quiet NaN is 0x7FF8. For a signalling NaN,
        // it's 0x7ff4.
        const unsigned long QuietNaN = 0x7ff8UL;
        //const unsigned long SignalNaN = 0x7ff4UL;

        // We need to grab the first part of the FP #
        char Buffer[100];

        uint64_t ll = DoubleToBits(V);
        sprintf(Buffer, "0x%llx", static_cast<long long>(ll));

        string Num(&Buffer[0], &Buffer[6]);
        unsigned long Val = strtoul(Num.c_str(), 0, 16);

        if (FPC->getType() == Type::getFloatTy(FPC->getContext()))
          Out << "LLVM_NAN" << (Val == QuietNaN ? "" : "S") << "F(\""
              << Buffer << "\") /*nan*/ ";
        else
          Out << "LLVM_NAN" << (Val == QuietNaN ? "" : "S") << "(\""
              << Buffer << "\") /*nan*/ ";
      } else if (std::isinf(V)) {
        // The value is Inf
        if (V < 0) Out << '-';
        Out << "LLVM_INF" <<
            (FPC->getType() == Type::getFloatTy(FPC->getContext()) ? "F" : "")
            << " /*inf*/ ";
      } else {
        string Num;
#if HAVE_PRINTF_A && ENABLE_CBE_PRINTF_A
        // Print out the constant as a floating point number.
        char Buffer[100];
        sprintf(Buffer, "%a", V);
        Num = Buffer;
#else
        Num = ftostr(FPC->getValueAPF());
#endif
       Out << Num;
      }
    }
    break;
  }

  case Type::ArrayTyID: {
    if (printConstantString(CPV, Context)) break;
    ArrayType *AT = cast<ArrayType>(CPV->getType());
    assert(AT->getNumElements() != 0 && !isEmptyType(AT));
    if (Context != ContextStatic) {
      CtorDeclTypes.insert(AT);
      Out << "llvm_ctor_";
      printTypeString(Out, AT, false);
      Out << "(";
      Context = ContextCasted;
    } else {
      Out << "{ { "; // Arrays are wrapped in struct types.
    }
    if (ConstantArray *CA = dyn_cast<ConstantArray>(CPV)) {
      printConstantArray(CA, Context);
    } else if (ConstantDataSequential *CDS =
                 dyn_cast<ConstantDataSequential>(CPV)) {
      printConstantDataSequential(CDS, Context);
    } else {
      assert(isa<ConstantAggregateZero>(CPV) || isa<UndefValue>(CPV));
      Constant *CZ = Constant::getNullValue(AT->getElementType());
      printConstant(CZ, Context);
      for (unsigned i = 1, e = AT->getNumElements(); i != e; ++i) {
        Out << ", ";
        printConstant(CZ, Context);
      }
    }
    Out << (Context == ContextStatic ? " } }" : ")"); // Arrays are wrapped in struct types.
    break;
  }

  case Type::VectorTyID: {
    VectorType *VT = cast<VectorType>(CPV->getType());
    assert(VT->getNumElements() != 0 && !isEmptyType(VT));
    if (Context != ContextStatic) {
      CtorDeclTypes.insert(VT);
      Out << "llvm_ctor_";
      printTypeString(Out, VT, false);
      Out << "(";
      Context = ContextCasted;
    } else {
      Out << "{ ";
    }
    if (ConstantVector *CV = dyn_cast<ConstantVector>(CPV)) {
      printConstantVector(CV, Context);
    } else if (ConstantDataSequential *CDS =
               dyn_cast<ConstantDataSequential>(CPV)) {
      printConstantDataSequential(CDS, Context);
    } else {
      assert(isa<ConstantAggregateZero>(CPV) || isa<UndefValue>(CPV));
      Constant *CZ = Constant::getNullValue(VT->getElementType());
      printConstant(CZ, Context);
      for (unsigned i = 1, e = VT->getNumElements(); i != e; ++i) {
        Out << ", ";
        printConstant(CZ, Context);
      }
    }
    Out << (Context == ContextStatic ? " }" : ")");
    break;
  }

  case Type::StructTyID: {
    StructType *ST = cast<StructType>(CPV->getType());
    assert(!isEmptyType(ST));
    if (Context != ContextStatic) {
      CtorDeclTypes.insert(ST);
      Out << "llvm_ctor_";
      printTypeString(Out, ST, false);
      Out << "(";
      Context = ContextCasted;
    } else {
      Out << "{ ";
    }

    if (isa<ConstantAggregateZero>(CPV) || isa<UndefValue>(CPV)) {
      bool printed = false;
      for (unsigned i = 0, e = ST->getNumElements(); i != e; ++i) {
        Type *ElTy = ST->getElementType(i);
        if (isEmptyType(ElTy)) continue;
        if (printed) Out << ", ";
        printConstant(Constant::getNullValue(ElTy), Context);
        printed = true;
      }
      assert(printed);
    } else {
      bool printed = false;
      for (unsigned i = 0, e = CPV->getNumOperands(); i != e; ++i) {
        Constant *C = cast<Constant>(CPV->getOperand(i));
        if (isEmptyType(C->getType())) continue;
        if (printed) Out << ", ";
        printConstant(C, Context);
        printed = true;
      }
      assert(printed);
    }
    Out << (Context == ContextStatic ? " }" : ")");
    break;
  }

  case Type::PointerTyID:
    if (isa<ConstantPointerNull>(CPV)) {
      Out << "((";
      printTypeName(Out, CPV->getType()); // sign doesn't matter
      Out << ")/*NULL*/0)";
      break;
    } else if (GlobalValue *GV = dyn_cast<GlobalValue>(CPV)) {
      writeOperand(GV);
      break;
    }
    // FALL THROUGH
  default:
#ifndef NDEBUG
    errs() << "Unknown constant type: " << *CPV << "\n";
#endif
    llvm_unreachable(0);
  }
}

// Some constant expressions need to be casted back to the original types
// because their operands were casted to the expected type. This function takes
// care of detecting that case and printing the cast for the ConstantExpr.
bool CWriter::printConstExprCast(ConstantExpr* CE) {
  bool NeedsExplicitCast = false;
  Type *Ty = CE->getOperand(0)->getType();
  bool TypeIsSigned = false;
  switch (CE->getOpcode()) {
  case Instruction::Add:
  case Instruction::Sub:
  case Instruction::Mul:
    // We need to cast integer arithmetic so that it is always performed
    // as unsigned, to avoid undefined behavior on overflow.
  case Instruction::LShr:
  case Instruction::URem:
  case Instruction::UDiv: NeedsExplicitCast = true; break;
  case Instruction::AShr:
  case Instruction::SRem:
  case Instruction::SDiv: NeedsExplicitCast = true; TypeIsSigned = true; break;
  case Instruction::SExt:
    Ty = CE->getType();
    NeedsExplicitCast = true;
    TypeIsSigned = true;
    break;
  case Instruction::ZExt:
  case Instruction::Trunc:
  case Instruction::FPTrunc:
  case Instruction::FPExt:
  case Instruction::UIToFP:
  case Instruction::SIToFP:
  case Instruction::FPToUI:
  case Instruction::FPToSI:
  case Instruction::PtrToInt:
  case Instruction::IntToPtr:
  case Instruction::BitCast:
    Ty = CE->getType();
    NeedsExplicitCast = true;
    break;
  default: break;
  }
  if (NeedsExplicitCast) {
    Out << "((";
      printTypeName(Out, Ty, TypeIsSigned); // not integer, sign doesn't matter
    Out << ")(";
  }
  return NeedsExplicitCast;
}

//  Print a constant assuming that it is the operand for a given Opcode. The
//  opcodes that care about sign need to cast their operands to the expected
//  type before the operation proceeds. This function does the casting.
void CWriter::printConstantWithCast(Constant* CPV, unsigned Opcode) {

  // Extract the operand's type, we'll need it.
  Type* OpTy = CPV->getType();
  assert(OpTy->isIntegerTy() || OpTy->isFloatingPointTy()); // TODO: VectorType are valid here, but not supported

  // Indicate whether to do the cast or not.
  bool shouldCast;
  bool typeIsSigned;
  opcodeNeedsCast(Opcode, shouldCast, typeIsSigned);

  // Write out the casted constant if we should, otherwise just write the
  // operand.
  if (shouldCast) {
    Out << "((";
    printSimpleType(Out, OpTy, typeIsSigned);
    Out << ")";
    printConstant(CPV, ContextCasted);
    Out << ")";
  } else
    printConstant(CPV, ContextCasted);
}

string CWriter::GetValueName(Value *Operand) {

  // Resolve potential alias.
  if (GlobalAlias *GA = dyn_cast<GlobalAlias>(Operand)) {
    Operand = GA->getAliasee();
  }

  string Name = Operand->getName();
  if (Name.empty()) { // Assign unique names to local temporaries.
    unsigned &No = AnonValueNumbers[Operand];
    if (No == 0)
      No = ++NextAnonValueNumber;
    Name = "tmp__" + utostr(No);
  }

  // Mangle globals with the standard mangler interface for LLC compatibility.
  if (isa<GlobalValue>(Operand)) {
    return CBEMangle(Name);
  }

  string VarName;
  VarName.reserve(Name.capacity());

  for (auto I = Name.begin(), E = Name.end(); I != E; ++I) {
    unsigned char ch = *I;

    if (!((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') ||
          (ch >= '0' && ch <= '9') || ch == '_')) {
      char buffer[5];
      sprintf(buffer, "_%x_", ch);
      VarName += buffer;
    } else
      VarName += ch;
  }

  return "llvm_cbe_" + VarName;
}

/// writeInstComputationInline - Emit the computation for the specified
/// instruction inline, with no destination provided.
void CWriter::writeInstComputationInline(Instruction &I) {
  // C can't handle non-power-of-two integer types
  unsigned mask = 0;
  Type *Ty = I.getType();
  if (Ty->isIntegerTy()) {
     IntegerType *ITy = static_cast<IntegerType*>(Ty);
     if (!ITy->isPowerOf2ByteWidth())
       mask = ITy->getBitMask();
  }

  // If this is a non-trivial bool computation, make sure to truncate down to
  // a 1 bit value.  This is important because we want "add i1 x, y" to return
  // "0" when x and y are true, not "2" for example.
  // Also truncate odd bit sizes
  if (mask)
    Out << "((";

  visit(&I);

  if (mask)
    Out << ")&" << mask << ")";
}


void CWriter::writeOperandInternal(Value *Operand, enum OperandContext Context) {
  if (Instruction *I = dyn_cast<Instruction>(Operand))
    // Should we inline this instruction to build a tree?
    if (isInlinableInst(*I) && !isDirectAlloca(I)) {
      Out << '(';
      writeInstComputationInline(*I);
      Out << ')';
      return;
    }

  Constant* CPV = dyn_cast<Constant>(Operand);

  if (CPV && !isa<GlobalValue>(CPV))
    printConstant(CPV, Context);
  else
    Out << GetValueName(Operand);
}

void CWriter::writeOperand(Value *Operand, enum OperandContext Context) {
  bool isAddressImplicit = isAddressExposed(Operand);
  if (isAddressImplicit)
    Out << "(&";  // Global variables are referenced as their addresses by llvm

  writeOperandInternal(Operand, Context);

  if (isAddressImplicit)
    Out << ')';
}

/// writeOperandDeref - Print the result of dereferencing the specified
/// operand with '*'.  This is equivalent to printing '*' then using
/// writeOperand, but avoids excess syntax in some cases.
void CWriter::writeOperandDeref(Value *Operand) {
  if (isAddressExposed(Operand)) {
    // Already something with an address exposed.
    writeOperandInternal(Operand);
  } else {
    Out << "*(";
    writeOperand(Operand);
    Out << ")";
  }
}

// Some instructions need to have their result value casted back to the
// original types because their operands were casted to the expected type.
// This function takes care of detecting that case and printing the cast
// for the Instruction.
bool CWriter::writeInstructionCast(Instruction &I) {
  Type *Ty = I.getOperand(0)->getType();
  switch (I.getOpcode()) {
  case Instruction::Add:
  case Instruction::Sub:
  case Instruction::Mul:
    // We need to cast integer arithmetic so that it is always performed
    // as unsigned, to avoid undefined behavior on overflow.
  case Instruction::LShr:
  case Instruction::URem:
  case Instruction::UDiv:
    Out << "((";
    printSimpleType(Out, Ty, false);
    Out << ")(";
    return true;
  case Instruction::AShr:
  case Instruction::SRem:
  case Instruction::SDiv:
    Out << "((";
    printSimpleType(Out, Ty, true);
    Out << ")(";
    return true;
  default: break;
  }
  return false;
}

// Write the operand with a cast to another type based on the Opcode being used.
// This will be used in cases where an instruction has specific type
// requirements (usually signedness) for its operands.
void CWriter::opcodeNeedsCast(unsigned Opcode,
      // Indicate whether to do the cast or not.
      bool &shouldCast,
      // Indicate whether the cast should be to a signed type or not.
      bool &castIsSigned) {

  // Based on the Opcode for which this Operand is being written, determine
  // the new type to which the operand should be casted by setting the value
  // of OpTy. If we change OpTy, also set shouldCast to true.
  switch (Opcode) {
    default:
      // for most instructions, it doesn't matter
      shouldCast = false;
      castIsSigned = false;
      break;
    case Instruction::Add:
    case Instruction::Sub:
    case Instruction::Mul:
      // We need to cast integer arithmetic so that it is always performed
      // as unsigned, to avoid undefined behavior on overflow.
    case Instruction::LShr:
    case Instruction::UDiv:
    case Instruction::URem: // Cast to unsigned first
      shouldCast = true;
      castIsSigned = false;
      break;
    case Instruction::GetElementPtr:
    case Instruction::AShr:
    case Instruction::SDiv:
    case Instruction::SRem: // Cast to signed first
      shouldCast = true;
      castIsSigned = true;
      break;
  }
}

void CWriter::writeOperandWithCast(Value* Operand, unsigned Opcode) {
  // Write out the casted operand if we should, otherwise just write the
  // operand.

  // Extract the operand's type, we'll need it.
  bool shouldCast;
  bool castIsSigned;
  opcodeNeedsCast(Opcode, shouldCast, castIsSigned);

  Type* OpTy = Operand->getType();
  if (shouldCast) {
    Out << "((";
    printSimpleType(Out, OpTy, castIsSigned);
    Out << ")";
    writeOperand(Operand, ContextCasted);
    Out << ")";
  } else
    writeOperand(Operand, ContextCasted);
}

// Write the operand with a cast to another type based on the icmp predicate
// being used.
void CWriter::writeOperandWithCast(Value* Operand, ICmpInst &Cmp) {
  // This has to do a cast to ensure the operand has the right signedness.
  // Also, if the operand is a pointer, we make sure to cast to an integer when
  // doing the comparison both for signedness and so that the C compiler doesn't
  // optimize things like "p < NULL" to false (p may contain an integer value
  // f.e.).
  bool shouldCast = Cmp.isRelational();

  // Write out the casted operand if we should, otherwise just write the
  // operand.
  if (!shouldCast) {
    writeOperand(Operand);
    return;
  }

  // Should this be a signed comparison?  If so, convert to signed.
  bool castIsSigned = Cmp.isSigned();

  // If the operand was a pointer, convert to a large integer type.
  Type* OpTy = Operand->getType();
  if (OpTy->isPointerTy())
    OpTy = TD->getIntPtrType(Operand->getContext());

  Out << "((";
  printSimpleType(Out, OpTy, castIsSigned);
  Out << ")";
  writeOperand(Operand);
  Out << ")";
}

static void generateAllocaCode(raw_ostream& Out) {
  // Alloca is hard to get, and we don't want to include stdlib.h here.
  Out << "/* get a declaration for alloca */\n"
    << "#if defined(__CYGWIN__) || defined(__MINGW32__)\n"
    << "#define  alloca(x) __builtin_alloca((x))\n"
    << "#define _alloca(x) __builtin_alloca((x))\n"
    << "#elif defined(__APPLE__)\n"
    << "extern void *__builtin_alloca(unsigned long);\n"
    << "#define alloca(x) __builtin_alloca(x)\n"
    << "#define longjmp _longjmp\n"
    << "#define setjmp _setjmp\n"
    << "#elif defined(__sun__)\n"
    << "#if defined(__sparcv9)\n"
    << "extern void *__builtin_alloca(unsigned long);\n"
    << "#else\n"
    << "extern void *__builtin_alloca(unsigned int);\n"
    << "#endif\n"
    << "#define alloca(x) __builtin_alloca(x)\n"
    << "#elif defined(__FreeBSD__) || defined(__NetBSD__) || defined(__OpenBSD__) || defined(__DragonFly__) || defined(__arm__)\n"
    << "#define alloca(x) __builtin_alloca(x)\n"
    << "#elif defined(_MSC_VER)\n"
    << "#define alloca(x) _alloca(x)\n"
    << "#else\n"
    << "#include <alloca.h>\n"
    << "#endif\n\n";
}

static void generateInt128Code(raw_ostream& Out) {
  // Output typedefs for 128-bit integers
  Out << "#if defined(__GNUC__) && defined(__LP64__) /* 128-bit integer types */\n"
    << "typedef int __attribute__((mode(TI))) int128_t;\n"
    << "typedef unsigned __attribute__((mode(TI))) uint128_t;\n"
    << "#define UINT128_C(hi, lo) (((uint128_t)(hi) << 64) | (uint128_t)(lo))\n"
    << "static inline uint128_t llvm_ctor_u128(uint64_t hi, uint64_t lo) {"
    << " return UINT128_C(hi, lo); }\n"
    << "static inline bool llvm_icmp_eq_u128(uint128_t l, uint128_t r) {"
    << " return l == r; }\n"
    << "static inline bool llvm_icmp_ne_u128(uint128_t l, uint128_t r) {"
    << " return l != r; }\n"
    << "static inline bool llvm_icmp_ule_u128(uint128_t l, uint128_t r) {"
    << " return l <= r; }\n"
    << "static inline bool llvm_icmp_sle_i128(int128_t l, int128_t r) {"
    << " return l <= r; }\n"
    << "static inline bool llvm_icmp_uge_u128(uint128_t l, uint128_t r) {"
    << " return l >= r; }\n"
    << "static inline bool llvm_icmp_sge_i128(int128_t l, int128_t r) {"
    << " return l >= r; }\n"
    << "static inline bool llvm_icmp_ult_u128(uint128_t l, uint128_t r) {"
    << " return l < r; }\n"
    << "static inline bool llvm_icmp_slt_i128(int128_t l, int128_t r) {"
    << " return l < r; }\n"
    << "static inline bool llvm_icmp_ugt_u128(uint128_t l, uint128_t r) {"
    << " return l > r; }\n"
    << "static inline bool llvm_icmp_sgt_i128(int128_t l, int128_t r) {"
    << " return l > r; }\n"

    << "#else /* manual 128-bit types */\n"
    // TODO: field order should be reversed for big-endian
    << "typedef struct { uint64_t lo; uint64_t hi; } uint128_t;\n"
    << "typedef uint128_t int128_t;\n"
    << "#define UINT128_C(hi, lo) {(lo), (hi)}\n" // only use in Static context
    << "static inline uint128_t llvm_ctor_u128(uint64_t hi, uint64_t lo) {"
    << " uint128_t r; r.lo = lo; r.hi = hi; return r; }\n"
    << "static inline bool llvm_icmp_eq_u128(uint128_t l, uint128_t r) {"
    << " return l.hi == r.hi && l.lo == r.lo; }\n"
    << "static inline bool llvm_icmp_ne_u128(uint128_t l, uint128_t r) {"
    << " return l.hi != r.hi || l.lo != r.lo; }\n"
    << "static inline bool llvm_icmp_ule_u128(uint128_t l, uint128_t r) {"
    << " return l.hi < r.hi ? 1 : (l.hi == r.hi ? l.lo <= l.lo : 0); }\n"
    << "static inline bool llvm_icmp_sle_i128(int128_t l, int128_t r) {"
    << " return (int64_t)l.hi < (int64_t)r.hi ? 1 : (l.hi == r.hi ? (int64_t)l.lo <= (int64_t)l.lo : 0); }\n"
    << "static inline bool llvm_icmp_uge_u128(uint128_t l, uint128_t r) {"
    << " return l.hi > r.hi ? 1 : (l.hi == r.hi ? l.lo >= l.hi : 0); }\n"
    << "static inline bool llvm_icmp_sge_i128(int128_t l, int128_t r) {"
    << " return (int64_t)l.hi > (int64_t)r.hi ? 1 : (l.hi == r.hi ? (int64_t)l.lo >= (int64_t)l.lo : 0); }\n"
    << "static inline bool llvm_icmp_ult_u128(uint128_t l, uint128_t r) {"
    << " return l.hi < r.hi ? 1 : (l.hi == r.hi ? l.lo < l.hi : 0); }\n"
    << "static inline bool llvm_icmp_slt_i128(int128_t l, int128_t r) {"
    << " return (int64_t)l.hi < (int64_t)r.hi ? 1 : (l.hi == r.hi ? (int64_t)l.lo < (int64_t)l.lo : 0); }\n"
    << "static inline bool llvm_icmp_ugt_u128(uint128_t l, uint128_t r) {"
    << " return l.hi > r.hi ? 1 : (l.hi == r.hi ? l.lo > l.hi : 0); }\n"
    << "static inline bool llvm_icmp_sgt_i128(int128_t l, int128_t r) {"
    << " return (int64_t)l.hi > (int64_t)r.hi ? 1 : (l.hi == r.hi ? (int64_t)l.lo > (int64_t)l.lo : 0); }\n"
    << "#define __emulate_i128\n"
    << "#endif\n\n";
}

// generateCompilerSpecificCode - This is where we add conditional compilation
// directives to cater to specific compilers as need be.
//
static void generateCompilerSpecificCode(raw_ostream& Out,
                                         const DataLayout *TD) {
  // On Mac OS X, "external weak" is spelled "__attribute__((weak_import))".
  Out << "#if defined(__GNUC__) && defined(__APPLE_CC__)\n"
      << "#define __EXTERNAL_WEAK__ __attribute__((weak_import))\n"
      << "#elif defined(__GNUC__)\n"
      << "#define __EXTERNAL_WEAK__ __attribute__((weak))\n"
      << "#else\n"
      << "#define __EXTERNAL_WEAK__\n"
      << "#endif\n\n";

  // For now, turn off the weak linkage attribute on Mac OS X. (See above.)
  Out << "#if defined(__GNUC__) && defined(__APPLE_CC__)\n"
      << "#define __ATTRIBUTE_WEAK__\n"
      << "#elif defined(__GNUC__)\n"
      << "#define __ATTRIBUTE_WEAK__ __attribute__((weak))\n"
      << "#else\n"
      << "#define __ATTRIBUTE_WEAK__\n"
      << "#endif\n\n";

  // Add hidden visibility support. FIXME: APPLE_CC?
  Out << "#if defined(__GNUC__)\n"
      << "#define __HIDDEN__ __attribute__((visibility(\"hidden\")))\n"
      << "#endif\n\n";

  // Define unaligned-load helper macro
  Out << "#ifdef _MSC_VER\n";
  Out << "#define __UNALIGNED_LOAD__(type, align, op) *((type __unaligned*)op)\n";
  Out << "#else\n";
  Out << "#define __UNALIGNED_LOAD__(type, align, op) ((struct { type data __attribute__((packed, aligned(align))); }*)op)->data\n";
  Out << "#endif\n\n";

  // Define unaligned-load helper macro
  Out << "#ifdef _MSC_VER\n";
  Out << "#define __MSALIGN__(X) __declspec(align(X))\n";
  Out << "#else\n";
  Out << "#define __MSALIGN__(X)\n";
  Out << "#endif\n\n";

  // Define compatibility macro to help msvc look more like gcc/clang
  Out << "#ifdef _MSC_VER\n";
  Out << "#define __builtin_unreachable() __assume(0)\n";
  Out << "#endif\n\n";

  // Compability macro for C compilers that do not support ISO C11
  Out << "#if __STDC_VERSION__ >= 201112L\n";
  Out << "#define __noreturn _Noreturn\n";
  Out << "#else\n";
  Out << "#define __noreturn\n";
  Out << "#endif\n\n";


  // Define NaN and Inf as GCC builtins if using GCC
  // From the GCC documentation:
  //
  //   double __builtin_nan (const char *str)
  //
  // This is an implementation of the ISO C99 function nan.
  //
  // Since ISO C99 defines this function in terms of strtod, which we do
  // not implement, a description of the parsing is in order. The string is
  // parsed as by strtol; that is, the base is recognized by leading 0 or
  // 0x prefixes. The number parsed is placed in the significand such that
  // the least significant bit of the number is at the least significant
  // bit of the significand. The number is truncated to fit the significand
  // field provided. The significand is forced to be a quiet NaN.
  //
  // This function, if given a string literal, is evaluated early enough
  // that it is considered a compile-time constant.
  //
  //   float __builtin_nanf (const char *str)
  //
  // Similar to __builtin_nan, except the return type is float.
  //
  //   double __builtin_inf (void)
  //
  // Similar to __builtin_huge_val, except a warning is generated if the
  // target floating-point format does not support infinities. This
  // function is suitable for implementing the ISO C99 macro INFINITY.
  //
  //   float __builtin_inff (void)
  //
  // Similar to __builtin_inf, except the return type is float.
  Out << "#ifdef __GNUC__\n"
      << "#define LLVM_NAN(NanStr)   __builtin_nan(NanStr)   /* Double */\n"
      << "#define LLVM_NANF(NanStr)  __builtin_nanf(NanStr)  /* Float */\n"
      << "#define LLVM_NANS(NanStr)  __builtin_nans(NanStr)  /* Double */\n"
      << "#define LLVM_NANSF(NanStr) __builtin_nansf(NanStr) /* Float */\n"
      << "#define LLVM_INF           __builtin_inf()         /* Double */\n"
      << "#define LLVM_INFF          __builtin_inff()        /* Float */\n"
      << "#define LLVM_PREFETCH(addr,rw,locality) "
                              "__builtin_prefetch(addr,rw,locality)\n"
      << "#define __ATTRIBUTE_CTOR__ __attribute__((constructor))\n"
      << "#define __ATTRIBUTE_DTOR__ __attribute__((destructor))\n"
      << "#else\n"
      << "#define LLVM_NAN(NanStr)   ((double)NAN)           /* Double */\n"
      << "#define LLVM_NANF(NanStr)  ((float)NAN))           /* Float */\n"
      << "#define LLVM_NANS(NanStr)  ((double)NAN)           /* Double */\n"
      << "#define LLVM_NANSF(NanStr) ((single)NAN)           /* Float */\n"
      << "#define LLVM_INF           ((double)INFINITY)      /* Double */\n"
      << "#define LLVM_INFF          ((float)INFINITY)       /* Float */\n"
      << "#define LLVM_PREFETCH(addr,rw,locality)            /* PREFETCH */\n"
      << "#define __ATTRIBUTE_CTOR__ \"__attribute__((constructor)) not supported on this compiler\"\n"
      << "#define __ATTRIBUTE_DTOR__ \"__attribute__((destructor)) not supported on this compiler\"\n"
      << "#endif\n\n";

  Out << "#if !defined(__GNUC__) || __GNUC__ < 4 /* Old GCC's, or compilers not GCC */ \n"
      << "#define __builtin_stack_save() 0   /* not implemented */\n"
      << "#define __builtin_stack_restore(X) /* noop */\n"
      << "#endif\n\n";

  // We output GCC specific attributes to preserve 'linkonce'ness on globals.
  // If we aren't being compiled with GCC, just drop these attributes.
  Out << "#ifdef _MSC_VER  /* Can only support \"linkonce\" vars with GCC */\n"
      << "#define __attribute__(X)\n"
      << "#endif\n\n";
}

/// FindStaticTors - Given a static ctor/dtor list, unpack its contents into
/// the StaticTors set.
static void FindStaticTors(GlobalVariable *GV, std::set<Function*> &StaticTors){
  ConstantArray *InitList = dyn_cast<ConstantArray>(GV->getInitializer());
  if (!InitList) return;

  for (unsigned i = 0, e = InitList->getNumOperands(); i != e; ++i)
    if (ConstantStruct *CS = dyn_cast<ConstantStruct>(InitList->getOperand(i))){
      if (CS->getNumOperands() != 2) return;  // Not array of 2-element structs.

      if (CS->getOperand(1)->isNullValue())
        return;  // Found a null terminator, exit printing.
      Constant *FP = CS->getOperand(1);
      if (ConstantExpr *CE = dyn_cast<ConstantExpr>(FP))
        if (CE->isCast())
          FP = CE->getOperand(0);
      if (Function *F = dyn_cast<Function>(FP))
        StaticTors.insert(F);
    }
}

enum SpecialGlobalClass {
  NotSpecial = 0,
  GlobalCtors, GlobalDtors,
  NotPrinted
};

/// getGlobalVariableClass - If this is a global that is specially recognized
/// by LLVM, return a code that indicates how we should handle it.
static SpecialGlobalClass getGlobalVariableClass(GlobalVariable *GV) {
  // If this is a global ctors/dtors list, handle it now.
  if (GV->hasAppendingLinkage() && GV->use_empty()) {
    if (GV->getName() == "llvm.global_ctors")
      return GlobalCtors;
    else if (GV->getName() == "llvm.global_dtors")
      return GlobalDtors;
  }

  // Otherwise, if it is other metadata, don't print it.  This catches things
  // like debug information.
  if (StringRef(GV->getSection()) == "llvm.metadata")
    return NotPrinted;

  return NotSpecial;
}

// PrintEscapedString - Print each character of the specified string, escaping
// it if it is not printable or if it is an escape char.
static void PrintEscapedString(const char *Str, unsigned Length,
                               raw_ostream &Out) {
  for (unsigned i = 0; i != Length; ++i) {
    unsigned char C = Str[i];
    if (isprint(C) && C != '\\' && C != '"')
      Out << C;
    else if (C == '\\')
      Out << "\\\\";
    else if (C == '\"')
      Out << "\\\"";
    else if (C == '\t')
      Out << "\\t";
    else
      Out << "\\x" << hexdigit(C >> 4) << hexdigit(C & 0x0F);
  }
}

// PrintEscapedString - Print each character of the specified string, escaping
// it if it is not printable or if it is an escape char.
static void PrintEscapedString(const string &Str, raw_ostream &Out) {
  PrintEscapedString(Str.c_str(), Str.size(), Out);
}

bool CWriter::doInitialization(Module &M) {
  TheModule = &M;

  TD = new DataLayout(&M);
  IL = new IntrinsicLowering(*TD);
  IL->AddPrototypes(M);

#if 0
  string Triple = TheModule->getTargetTriple();
  if (Triple.empty())
    Triple = llvm::sys::getDefaultTargetTriple();

  string E;
  if (const Target *Match = TargetRegistry::lookupTarget(Triple, E))
    TAsm = Match->createMCAsmInfo(Triple);
#endif
  TAsm = new CBEMCAsmInfo();
  MRI  = new MCRegisterInfo();
  TCtx = new MCContext(TAsm, MRI, NULL);
  return false;
}

bool CWriter::doFinalization(Module &M) {
  // Output all code to the file
  string methods = Out.str();
  _Out.clear();
  generateHeader(M);
  string header = Out.str();
  _Out.clear();
  FileOut << header << methods;

  // Free memory...
  delete IL;
  delete TD;
  delete TCtx;
  delete TAsm;
  delete MRI;
  delete MOFI;
  FPConstantMap.clear();
  ByValParams.clear();
  AnonValueNumbers.clear();
  UnnamedStructIDs.clear();
  UnnamedFunctionIDs.clear();
  TypedefDeclTypes.clear();
  SelectDeclTypes.clear();
  CmpDeclTypes.clear();
  CastOpDeclTypes.clear();
  InlineOpDeclTypes.clear();
  CtorDeclTypes.clear();
  prototypesToGen.clear();

  // reset all state
  FPCounter = 0;
  OpaqueCounter = 0;
  NextAnonValueNumber = 0;
  NextAnonStructNumber = 0;
  NextFunctionNumber = 0;
  UsesInt128 = false;
  UsesAlloca = false;
  return true; // may have lowered an IntrinsicCall
}

void CWriter::generateHeader(Module &M) {
  // Keep track of which functions are static ctors/dtors so they can have
  // an attribute added to their prototypes.
  std::set<Function*> StaticCtors, StaticDtors;
  for (auto it = M.global_begin(), E = M.global_end(); it != E; ++it) {
    auto I = &*it;
    switch (getGlobalVariableClass(I)) {
    default: break;
    case GlobalCtors:
      FindStaticTors(I, StaticCtors);
      break;
    case GlobalDtors:
      FindStaticTors(I, StaticDtors);
      break;
    }
  }

  // get declaration for alloca
  Out << "/* Provide Declarations */\n";
  Out << "#include <stdarg.h>\n";      // Varargs support
  Out << "#include <setjmp.h>\n";      // Unwind support
  Out << "#include <limits.h>\n";      // With overflow intrinsics support.
  Out << "#include <stdint.h>\n";      // Sized integer support
  Out << "#include <math.h>\n";        // definitions for some math functions and numeric constants
  // Provide a definition for `bool' if not compiling with a C++ compiler.
  Out << "#ifndef __cplusplus\ntypedef unsigned char bool;\n#endif\n";
  Out << "\n";

  if(UsesAlloca)
    generateAllocaCode(Out);

  generateCompilerSpecificCode(Out, TD);

  if(UsesInt128)
    generateInt128Code(Out);

  Out << "\n\n/* Support for floating point constants */\n"
      << "typedef uint64_t ConstantDoubleTy;\n"
      << "typedef uint32_t ConstantFloatTy;\n"
      << "typedef struct { uint64_t f1; uint16_t f2; "
         "uint16_t pad[3]; } ConstantFP80Ty;\n"
      // This is used for both kinds of 128-bit long double; meaning differs.
      << "typedef struct { uint64_t f1; uint64_t f2; }"
         " ConstantFP128Ty;\n"
      << "\n\n/* Global Declarations */\n";

  // First output all the declarations for the program, because C requires
  // Functions & globals to be declared before they are used.
  if (!M.getModuleInlineAsm().empty()) {
    Out << "\n/* Module asm statements */\n"
        << "__asm__ (";

    // Split the string into lines, to make it easier to read the .ll file.
    string Asm = M.getModuleInlineAsm();
    size_t CurPos = 0;
    size_t NewLine = Asm.find_first_of('\n', CurPos);
    while (NewLine != string::npos) {
      // We found a newline, print the portion of the asm string from the
      // last newline up to this newline.
      Out << "\"";
      PrintEscapedString(string(Asm.begin()+CurPos, Asm.begin()+NewLine),
                         Out);
      Out << "\\n\"\n";
      CurPos = NewLine+1;
      NewLine = Asm.find_first_of('\n', CurPos);
    }
    Out << "\"";
    PrintEscapedString(string(Asm.begin()+CurPos, Asm.end()), Out);
    Out << "\");\n"
        << "/* End Module asm statements */\n";
  }

  // collect any remaining types
  raw_null_ostream NullOut;
  for (auto it = M.global_begin(), E = M.global_end(); it != E; ++it) {
    auto I = &*it;

    // Ignore special globals, such as debug info.
    if (getGlobalVariableClass(I))
      continue;
    printTypeName(NullOut, I->getType()->getElementType(), false);
  }
  printModuleTypes(Out);

  // Global variable declarations...
  if (!M.global_empty()) {
    Out << "\n/* External Global Variable Declarations */\n";
    for (auto& gv : M.globals()) {
      auto I = &gv;

      if (isEmptyType(I->getType()->getPointerElementType()))
        continue;

      if (I->hasDLLImportStorageClass())
        Out << "__declspec(dllimport) ";
      else if (I->hasDLLExportStorageClass())
        Out << "__declspec(dllexport) ";

      if (I->hasExternalLinkage() || I->hasExternalWeakLinkage() ||
          I->hasCommonLinkage())
        Out << "extern ";
      else
        continue; // Internal Global

      // Thread Local Storage
      if (I->isThreadLocal())
        Out << "__thread ";

      Type *ElTy = I->getType()->getElementType();
      unsigned Alignment = I->getAlignment();
      bool IsOveraligned = Alignment &&
        Alignment > TD->getABITypeAlignment(ElTy);
      if (IsOveraligned)
        Out << "__MSALIGN__(" << Alignment << ") ";
      printTypeName(Out, ElTy, false) << ' ' << GetValueName(I);
      if (IsOveraligned)
        Out << " __attribute__((aligned(" << Alignment << ")))";

      if (I->hasExternalWeakLinkage())
         Out << " __EXTERNAL_WEAK__";
      Out << ";\n";
    }
  }

  // Function declarations
  Out << "\n/* Function Declarations */\n";

  // Store the intrinsics which will be declared/defined below.
  SmallVector<Function*, 16> intrinsicsToDefine;

  for (auto it = M.begin(), E = M.end(); it != E; ++it) {
    auto I = &(*it);
    // Don't print declarations for intrinsic functions.
    // Store the used intrinsics, which need to be explicitly defined.
    if (I->isIntrinsic()) {
      switch (I->getIntrinsicID()) {
        default:
          continue;
        case Intrinsic::uadd_with_overflow:
        case Intrinsic::sadd_with_overflow:
        case Intrinsic::usub_with_overflow:
        case Intrinsic::ssub_with_overflow:
        case Intrinsic::umul_with_overflow:
        case Intrinsic::smul_with_overflow:
        case Intrinsic::bswap:
        case Intrinsic::ceil:
        case Intrinsic::ctlz:
        case Intrinsic::ctpop:
        case Intrinsic::cttz:
        case Intrinsic::fabs:
        case Intrinsic::floor:
        case Intrinsic::fma:
        case Intrinsic::fmuladd:
        case Intrinsic::pow:
        case Intrinsic::powi:
        case Intrinsic::rint:
        case Intrinsic::sqrt:
        case Intrinsic::trunc:
          intrinsicsToDefine.push_back(I);
          continue;
      }
    }

    // Skip a few functions that have already been defined in headers
    if (I->getName() == "setjmp" ||
        I->getName() == "longjmp" ||
        I->getName() == "_setjmp" ||
        I->getName() == "siglongjmp" ||
        I->getName() == "sigsetjmp" ||
        I->getName() == "pow" ||
        I->getName() == "powf" ||
        I->getName() == "sqrt" ||
        I->getName() == "sqrtf" ||
        I->getName() == "trunc" ||
        I->getName() == "truncf" ||
        I->getName() == "rint" ||
        I->getName() == "rintf" ||
        I->getName() == "floor" ||
        I->getName() == "floorf" ||
        I->getName() == "ceil" ||
        I->getName() == "ceilf" ||
        I->getName() == "alloca" ||
        I->getName() == "_alloca" ||
        I->getName() == "_chkstk" ||
        I->getName() == "__chkstk" ||
        I->getName() == "___chkstk_ms")
      continue;

    if (I->hasDLLImportStorageClass())
      Out << "__declspec(dllimport) ";
    else if (I->hasDLLExportStorageClass())
      Out << "__declspec(dllexport) ";

    if (I->hasLocalLinkage())
      Out << "static ";
    if (I->hasExternalWeakLinkage())
      Out << "extern ";
    printFunctionProto(Out, I);
    if (I->hasWeakLinkage() || I->hasLinkOnceLinkage())
      Out << " __ATTRIBUTE_WEAK__";
    if (I->hasExternalWeakLinkage())
      Out << " __EXTERNAL_WEAK__";
    if (StaticCtors.count(I))
      Out << " __ATTRIBUTE_CTOR__";
    if (StaticDtors.count(I))
      Out << " __ATTRIBUTE_DTOR__";
    if (I->hasHiddenVisibility())
      Out << " __HIDDEN__";

    if (I->hasName() && I->getName()[0] == 1)
      Out << " __asm__ (\"" << I->getName().substr(1) << "\")";

    Out << ";\n";
  }

  // Output the global variable definitions and contents...
  if (!M.global_empty()) {
    std::set<GlobalVariable*> vars;
    Out << "\n\n/* Global Variable Declarations*/\n";
    for (auto& I : M.globals())
      declareOneGlobalVariable(&I, false);

    Out << "\n\n/* Global Variable Definitions and Initialization */\n";
    for (auto& I : M.globals())
      declareOneGlobalVariable(&I, true);
  }

  // Alias declarations...
  if (!M.alias_empty()) {
    Out << "\n/* External Alias Declarations */\n";
    for (auto I = M.alias_begin(), E = M.alias_end(); I != E; ++I) {
      assert(!I->isDeclaration() && !isEmptyType(I->getType()->getPointerElementType()));
      if (I->hasLocalLinkage())
        continue; // Internal Global

      if (I->hasDLLImportStorageClass())
        Out << "__declspec(dllimport) ";
      else if (I->hasDLLExportStorageClass())
        Out << "__declspec(dllexport) ";

      // Thread Local Storage
      if (I->isThreadLocal())
        Out << "__thread ";

      Type *ElTy = I->getType()->getElementType();
      unsigned Alignment = I->getAlignment();
      bool IsOveraligned = Alignment &&
        Alignment > TD->getABITypeAlignment(ElTy);
      if (IsOveraligned)
        Out << "__MSALIGN__(" << Alignment << ") ";
      // GetValueName would resolve the alias, which is not what we want,
      // so use getName directly instead (assuming that the Alias has a name...)
      printTypeName(Out, ElTy, false) << " *" << I->getName();
      if (IsOveraligned)
        Out << " __attribute__((aligned(" << Alignment << ")))";

      if (I->hasExternalWeakLinkage())
         Out << " __EXTERNAL_WEAK__";
      Out << " = ";
      writeOperand(I->getAliasee(), ContextStatic);
      Out << ";\n";
    }
  }

  Out << "\n\n/* LLVM Intrinsic Builtin Function Bodies */\n";

  // Emit some helper functions for dealing with FCMP instruction's
  // predicates
  Out << "static inline int llvm_fcmp_ord(double X, double Y) { ";
  Out << "return X == X && Y == Y; }\n";
  Out << "static inline int llvm_fcmp_uno(double X, double Y) { ";
  Out << "return X != X || Y != Y; }\n";
  Out << "static inline int llvm_fcmp_ueq(double X, double Y) { ";
  Out << "return X == Y || llvm_fcmp_uno(X, Y); }\n";
  Out << "static inline int llvm_fcmp_une(double X, double Y) { ";
  Out << "return X != Y; }\n";
  Out << "static inline int llvm_fcmp_ult(double X, double Y) { ";
  Out << "return X <  Y || llvm_fcmp_uno(X, Y); }\n";
  Out << "static inline int llvm_fcmp_ugt(double X, double Y) { ";
  Out << "return X >  Y || llvm_fcmp_uno(X, Y); }\n";
  Out << "static inline int llvm_fcmp_ule(double X, double Y) { ";
  Out << "return X <= Y || llvm_fcmp_uno(X, Y); }\n";
  Out << "static inline int llvm_fcmp_uge(double X, double Y) { ";
  Out << "return X >= Y || llvm_fcmp_uno(X, Y); }\n";
  Out << "static inline int llvm_fcmp_oeq(double X, double Y) { ";
  Out << "return X == Y ; }\n";
  Out << "static inline int llvm_fcmp_one(double X, double Y) { ";
  Out << "return X != Y && llvm_fcmp_ord(X, Y); }\n";
  Out << "static inline int llvm_fcmp_olt(double X, double Y) { ";
  Out << "return X <  Y ; }\n";
  Out << "static inline int llvm_fcmp_ogt(double X, double Y) { ";
  Out << "return X >  Y ; }\n";
  Out << "static inline int llvm_fcmp_ole(double X, double Y) { ";
  Out << "return X <= Y ; }\n";
  Out << "static inline int llvm_fcmp_oge(double X, double Y) { ";
  Out << "return X >= Y ; }\n";
  Out << "static inline int llvm_fcmp_0(double X, double Y) { ";
  Out << "return 0; }\n";
  Out << "static inline int llvm_fcmp_1(double X, double Y) { ";
  Out << "return 1; }\n";

  // Loop over all select operations
  for (auto it = SelectDeclTypes.begin(), end = SelectDeclTypes.end(); it != end; ++it) {
    // static inline Rty llvm_select_u8x4(<bool x 4> condition, <u8 x 4> iftrue, <u8 x 4> ifnot) {
    //   Rty r = {
    //     condition[0] ? iftrue[0] : ifnot[0],
    //     condition[1] ? iftrue[1] : ifnot[1],
    //     condition[2] ? iftrue[2] : ifnot[2],
    //     condition[3] ? iftrue[3] : ifnot[3]
    //   };
    //   return r;
    // }
    Out << "static inline ";
    printTypeNameUnaligned(Out, *it, false);
    Out << " llvm_select_";
    printTypeString(Out, *it, false);
    Out << "(";
    if (isa<VectorType>(*it))
      printTypeNameUnaligned(Out, VectorType::get(Type::getInt1Ty((*it)->getContext()), (*it)->getVectorNumElements()), false);
    else
      Out << "bool";
    Out << " condition, ";
    printTypeNameUnaligned(Out, *it, false);
    Out << " iftrue, ";
    printTypeNameUnaligned(Out, *it, false);
    Out << " ifnot) {\n  ";
    printTypeNameUnaligned(Out, *it, false);
    Out << " r;\n";
    if (isa<VectorType>(*it)) {
      unsigned n, l = (*it)->getVectorNumElements();
      for (n = 0; n < l; n++) {
        Out << "  r.vector[" << n << "] = condition.vector[" << n << "] ? iftrue.vector[" << n << "] : ifnot.vector[" << n << "];\n";
      }
    }
    else {
      Out << "  r = condition ? iftrue : ifnot;\n";
    }
    Out << "  return r;\n}\n";
  }

  // Loop over all compare operations
  for (auto it = CmpDeclTypes.begin(), end = CmpDeclTypes.end(); it != end; ++it) {
    // static inline <bool x 4> llvm_icmp_ge_u8x4(<u8 x 4> l, <u8 x 4> r) {
    //   Rty c = {
    //     l[0] >= r[0],
    //     l[1] >= r[1],
    //     l[2] >= r[2],
    //     l[3] >= r[3],
    //   };
    //   return c;
    // }
    unsigned n, l = (*it).second->getVectorNumElements();
    VectorType *RTy = VectorType::get(Type::getInt1Ty((*it).second->getContext()), l);
    bool isSigned = CmpInst::isSigned((*it).first);
    Out << "static inline ";
    printTypeName(Out, RTy, isSigned);
    if (CmpInst::isFPPredicate((*it).first))
      Out << " llvm_fcmp_";
    else
      Out << " llvm_icmp_";
    Out << getCmpPredicateName((*it).first) << "_";
    printTypeString(Out, (*it).second, isSigned);
    Out << "(";
    printTypeNameUnaligned(Out, (*it).second, isSigned);
    Out << " l, ";
    printTypeNameUnaligned(Out, (*it).second, isSigned);
    Out << " r) {\n  ";
    printTypeName(Out, RTy, isSigned);
    Out << " c;\n";
    for (n = 0; n < l; n++) {
      Out << "  c.vector[" << n << "] = ";
      if (CmpInst::isFPPredicate((*it).first)) {
        Out << "llvm_fcmp_ " << getCmpPredicateName((*it).first) << "(l.vector[" << n << "], r.vector[" << n << "]);\n";
      } else {
        Out << "l.vector[" << n << "]";
        switch ((*it).first) {
        case CmpInst::ICMP_EQ:  Out << " == "; break;
        case CmpInst::ICMP_NE:  Out << " != "; break;
        case CmpInst::ICMP_ULE:
        case CmpInst::ICMP_SLE: Out << " <= "; break;
        case CmpInst::ICMP_UGE:
        case CmpInst::ICMP_SGE: Out << " >= "; break;
        case CmpInst::ICMP_ULT:
        case CmpInst::ICMP_SLT: Out << " < "; break;
        case CmpInst::ICMP_UGT:
        case CmpInst::ICMP_SGT: Out << " > "; break;
        default:
#ifndef NDEBUG
          errs() << "Invalid icmp predicate!" << (*it).first;
#endif
          llvm_unreachable(0);
        }
        Out << "r.vector[" << n << "];\n";
      }
    }
    Out << "  return c;\n}\n";
  }

  // Loop over all (vector) cast operations
  for (auto it = CastOpDeclTypes.begin(), end = CastOpDeclTypes.end(); it != end; ++it) {
    // static inline <u32 x 4> llvm_ZExt_u8x4_u32x4(<u8 x 4> in) { // Src->isVector == Dst->isVector
    //   Rty out = {
    //     in[0],
    //     in[1],
    //     in[2],
    //     in[3]
    //   };
    //   return out;
    // }
    // static inline u32 llvm_BitCast_u8x4_u32(<u8 x 4> in) { // Src->bitsSize == Dst->bitsSize
    //   union {
    //     <u8 x 4> in;
    //     u32 out;
    //   } cast;
    //   cast.in = in;
    //   return cast.out;
    // }
    CastInst::CastOps opcode = (*it).first;
    Type *SrcTy = (*it).second.first;
    Type *DstTy = (*it).second.second;
    bool SrcSigned, DstSigned;
    switch (opcode) {
    default:
      SrcSigned = false;
      DstSigned = false;
    case Instruction::SIToFP:
      SrcSigned = true;
      DstSigned = false;
    case Instruction::FPToSI:
      SrcSigned = false;
      DstSigned = true;
    case Instruction::SExt:
      SrcSigned = true;
      DstSigned = true;
    }

    Out << "static inline ";
    printTypeName(Out, DstTy, DstSigned);
    Out << " llvm_" << Instruction::getOpcodeName(opcode) << "_";
    printTypeString(Out, SrcTy, false);
    Out << "_";
    printTypeString(Out, DstTy, false);
    Out << "(";
    printTypeNameUnaligned(Out, SrcTy, SrcSigned);
    Out << " in) {\n";
    if (opcode == Instruction::BitCast) {
      Out << "  union {\n    ";
      printTypeName(Out, SrcTy, SrcSigned);
      Out << " in;\n    ";
      printTypeName(Out, DstTy, DstSigned);
      Out << " out;\n  } cast;\n";
      Out << "  cast.in = in;\n  return cast.out;\n}\n";
    } else if (isa<VectorType>(DstTy)) {
      Out << "  ";
      printTypeName(Out, DstTy, DstSigned);
      Out << " out;\n";
      unsigned n, l = DstTy->getVectorNumElements();
      assert(SrcTy->getVectorNumElements() == l);
      for (n = 0; n < l; n++) {
        Out << "  out.vector[" << n << "] = in.vector[" << n << "];\n";
      }
      Out << "  return out;\n}\n";
    } else {
      Out << "#ifndef __emulate_i128\n";
      // easy case first: compiler supports i128 natively
      Out << "  return in;\n";
      Out << "#else\n";
      Out << "  ";
      printTypeName(Out, DstTy, DstSigned);
      Out << " out;\n";
      Out << "  LLVM";
      switch (opcode) {
      case Instruction::UIToFP: Out << "UItoFP"; break;
      case Instruction::SIToFP: Out << "SItoFP"; break;
      case Instruction::Trunc: Out << "Trunc"; break;
      //case Instruction::FPExt:
      //case Instruction::FPTrunc:
      case Instruction::ZExt: Out << "ZExt"; break;
      case Instruction::FPToUI: Out << "FPtoUI"; break;
      case Instruction::SExt: Out << "SExt"; break;
      case Instruction::FPToSI: Out << "FPtoSI"; break;
      default:
        llvm_unreachable("Invalid cast opcode for i128");
      }
      Out << "(" << SrcTy->getPrimitiveSizeInBits() << ", &in, "
                 << DstTy->getPrimitiveSizeInBits() << ", &out);\n";
      Out << "  return out;\n";
      Out << "#endif\n";
      Out << "}\n";
    }
  }

  // Loop over all simple vector operations
  for (auto it = InlineOpDeclTypes.begin(), end = InlineOpDeclTypes.end(); it != end; ++it) {
    // static inline <u32 x 4> llvm_BinOp_u32x4(<u32 x 4> a, <u32 x 4> b) {
    //   Rty r = {
    //      a[0] OP b[0],
    //      a[1] OP b[1],
    //      a[2] OP b[2],
    //      a[3] OP b[3],
    //   };
    //   return r;
    // }
    unsigned opcode = (*it).first;
    Type *OpTy = (*it).second;
    Type *ElemTy = isa<VectorType>(OpTy) ? OpTy->getVectorElementType() : OpTy;
    bool shouldCast;
    bool isSigned;
    opcodeNeedsCast(opcode, shouldCast, isSigned);

    Out << "static inline ";
    printTypeName(Out, OpTy);
    if (opcode == BinaryNeg) {
      Out << " llvm_neg_";
      printTypeString(Out, OpTy, false);
      Out << "(";
      printTypeNameUnaligned(Out, OpTy, isSigned);
      Out << " a) {\n  ";
    } else if (opcode == BinaryNot) {
      Out << " llvm_not_";
      printTypeString(Out, OpTy, false);
      Out << "(";
      printTypeNameUnaligned(Out, OpTy, isSigned);
      Out << " a) {\n  ";
    } else {
      Out << " llvm_" << Instruction::getOpcodeName(opcode) << "_";
      printTypeString(Out, OpTy, false);
      Out << "(";
      printTypeNameUnaligned(Out, OpTy, isSigned);
      Out << " a, ";
      printTypeNameUnaligned(Out, OpTy, isSigned);
      Out << " b) {\n  ";
    }

    printTypeName(Out, OpTy);
    // C can't handle non-power-of-two integer types
    unsigned mask = 0;
    if (ElemTy->isIntegerTy()) {
       IntegerType *ITy = static_cast<IntegerType*>(ElemTy);
       if (!ITy->isPowerOf2ByteWidth())
         mask = ITy->getBitMask();
    }

    if (isa<VectorType>(OpTy)) {
      Out << " r;\n";
      unsigned n, l = OpTy->getVectorNumElements();
      for (n = 0; n < l; n++) {
        Out << "  r.vector[" << n << "] = ";
        if (mask)
          Out << "(";
        if (opcode == BinaryNeg) {
          Out << "-a.vector[" << n << "]";
        } else if (opcode == BinaryNot) {
          Out << "~a.vector[" << n << "]";
        } else if (opcode == Instruction::FRem) {
          // Output a call to fmod/fmodf instead of emitting a%b
          if (ElemTy->isFloatTy())
            Out << "fmodf(a.vector[" << n << "], b.vector[" << n << "])";
          else if (ElemTy->isDoubleTy())
            Out << "fmod(a.vector[" << n << "], b.vector[" << n << "])";
          else  // all 3 flavors of long double
            Out << "fmodl(a.vector[" << n << "], b.vector[" << n << "])";
        } else {
          Out << "a.vector[" << n << "]";
          switch (opcode) {
          case Instruction::Add:
          case Instruction::FAdd: Out << " + "; break;
          case Instruction::Sub:
          case Instruction::FSub: Out << " - "; break;
          case Instruction::Mul:
          case Instruction::FMul: Out << " * "; break;
          case Instruction::URem:
          case Instruction::SRem:
          case Instruction::FRem: Out << " % "; break;
          case Instruction::UDiv:
          case Instruction::SDiv:
          case Instruction::FDiv: Out << " / "; break;
          case Instruction::And:  Out << " & "; break;
          case Instruction::Or:   Out << " | "; break;
          case Instruction::Xor:  Out << " ^ "; break;
          case Instruction::Shl : Out << " << "; break;
          case Instruction::LShr:
          case Instruction::AShr: Out << " >> "; break;
          default:
#ifndef NDEBUG
             errs() << "Invalid operator type!" << opcode;
#endif
             llvm_unreachable(0);
          }
          Out << "b.vector[" << n << "]";
        }
        if (mask)
          Out << ") & " << mask;
        Out << ";\n";
      }

    } else if (OpTy->getPrimitiveSizeInBits() > 64) {
      Out << " r;\n";
      Out << "#ifndef __emulate_i128\n";
      // easy case first: compiler supports i128 natively
      Out << "  r = ";
      if (opcode == BinaryNeg) {
        Out << "-a;\n";
      } else if (opcode == BinaryNot) {
        Out << "~a;\n";
      } else {
        Out << "a";
        switch (opcode) {
        case Instruction::Add: Out << " + "; break;
        case Instruction::Sub: Out << " - "; break;
        case Instruction::Mul: Out << " * "; break;
        case Instruction::URem:
        case Instruction::SRem: Out << " % "; break;
        case Instruction::UDiv:
        case Instruction::SDiv: Out << " / "; break;
        case Instruction::And:  Out << " & "; break;
        case Instruction::Or:   Out << " | "; break;
        case Instruction::Xor:  Out << " ^ "; break;
        case Instruction::Shl:  Out << " << "; break;
        case Instruction::LShr:
        case Instruction::AShr: Out << " >> "; break;
        default:
#ifndef NDEBUG
           errs() << "Invalid operator type!" << opcode;
#endif
           llvm_unreachable(0);
        }
        Out << "b;\n";
      }
      Out << "#else\n";
      // emulated twos-complement i128 math
      if (opcode == BinaryNeg) {
        Out << "  r.hi = ~a.hi;\n";
        Out << "  r.lo = ~a.lo + 1;\n";
        Out << "  if (r.lo == 0) r.hi += 1;\n"; // overflow: carry the one
      } else if (opcode == BinaryNot) {
        Out << "  r.hi = ~a.hi;\n";
        Out << "  r.lo = ~a.lo;\n";
      } else if (opcode == Instruction::And) {
        Out << "  r.hi = a.hi & b.hi;\n";
        Out << "  r.lo = a.lo & b.lo;\n";
      } else if (opcode == Instruction::Or) {
        Out << "  r.hi = a.hi | b.hi;\n";
        Out << "  r.lo = a.lo | b.lo;\n";
      } else if (opcode == Instruction::Xor) {
        Out << "  r.hi = a.hi ^ b.hi;\n";
        Out << "  r.lo = a.lo ^ b.lo;\n";
      } else if (opcode == Instruction::Shl) { // reminder: undef behavior if b >= 128
        Out << "  if (b.lo >= 64) {\n";
        Out << "    r.hi = (a.lo << (b.lo - 64));\n";
        Out << "    r.lo = 0;\n";
        Out << "  } else if (b.lo == 0) {\n";
        Out << "    r.hi = a.hi;\n";
        Out << "    r.lo = a.lo;\n";
        Out << "  } else {\n";
        Out << "    r.hi = (a.hi << b.lo) | (a.lo >> (64 - b.lo));\n";
        Out << "    r.lo = a.lo << b.lo;\n";
        Out << "  }\n";
      } else {
        // everything that hasn't been manually implemented above
        Out << "  LLVM";
        switch (opcode) {
        //case BinaryNeg: Out << "Neg"; break;
        //case BinaryNot: Out << "FlipAllBits"; break;
        case Instruction::Add: Out << "Add"; break;
        case Instruction::Sub: Out << "Sub"; break;
        case Instruction::Mul: Out << "Mul"; break;
        case Instruction::URem: Out << "URem"; break;
        case Instruction::SRem: Out << "SRem"; break;
        case Instruction::UDiv: Out << "UDiv"; break;
        case Instruction::SDiv: Out << "SDiv"; break;
        //case Instruction::And:  Out << "And"; break;
        //case Instruction::Or:   Out << "Or"; break;
        //case Instruction::Xor:  Out << "Xor"; break;
        //case Instruction::Shl: Out << "Shl"; break;
        case Instruction::LShr: Out << "LShr"; break;
        case Instruction::AShr: Out << "AShr"; break;
        default:
#ifndef NDEBUG
           errs() << "Invalid operator type!" << opcode;
#endif
           llvm_unreachable(0);
        }
        Out << "(16, &a, &b, &r);\n";
      }
      Out << "#endif\n";

    } else {
      Out << " r = ";
      if (mask)
        Out << "(";
      if (opcode == BinaryNeg) {
        Out << "-a";
      } else if (opcode == BinaryNot) {
        Out << "~a";
      } else if (opcode == Instruction::FRem) {
        // Output a call to fmod/fmodf instead of emitting a%b
        if (ElemTy->isFloatTy())
          Out << "fmodf(a, b)";
        else if (ElemTy->isDoubleTy())
          Out << "fmod(a, b)";
        else  // all 3 flavors of long double
          Out << "fmodl(a, b)";
      } else {
        Out << "a";
        switch (opcode) {
        case Instruction::Add:
        case Instruction::FAdd: Out << " + "; break;
        case Instruction::Sub:
        case Instruction::FSub: Out << " - "; break;
        case Instruction::Mul:
        case Instruction::FMul: Out << " * "; break;
        case Instruction::URem:
        case Instruction::SRem:
        case Instruction::FRem: Out << " % "; break;
        case Instruction::UDiv:
        case Instruction::SDiv:
        case Instruction::FDiv: Out << " / "; break;
        case Instruction::And:  Out << " & "; break;
        case Instruction::Or:   Out << " | "; break;
        case Instruction::Xor:  Out << " ^ "; break;
        case Instruction::Shl : Out << " << "; break;
        case Instruction::LShr:
        case Instruction::AShr: Out << " >> "; break;
        default:
#ifndef NDEBUG
           errs() << "Invalid operator type!" << opcode;
#endif
           llvm_unreachable(0);
        }
        Out << "b";
        if (mask)
          Out << ") & " << mask;
      }
      Out << ";\n";
    }
    Out << "  return r;\n}\n";
  }

  // Loop over all inline constructors
  for (auto it = CtorDeclTypes.begin(), end = CtorDeclTypes.end(); it != end; ++it) {
    // static inline <u32 x 4> llvm_ctor_u32x4(u32 x1, u32 x2, u32 x3, u32 x4) {
    //   Rty r = {
    //     x1, x2, x3, x4
    //   };
    //   return r;
    // }
    Out << "static inline ";
    printTypeName(Out, *it);
    Out << " llvm_ctor_";
    printTypeString(Out, *it, false);
    Out << "(";
    StructType *STy = dyn_cast<StructType>(*it);
    ArrayType *ATy = dyn_cast<ArrayType>(*it);
    VectorType *VTy = dyn_cast<VectorType>(*it);
    unsigned e = (STy ? STy->getNumElements() : (ATy ? ATy->getNumElements() : VTy->getNumElements()));
    bool printed = false;
    for (unsigned i = 0; i != e; ++i) {
        Type *ElTy = STy ? STy->getElementType(i) : (*it)->getSequentialElementType();
        if (isEmptyType(ElTy))
          Out << " /* ";
        else if (printed)
          Out << ", ";
        printTypeNameUnaligned(Out, ElTy);
        Out << " x" << i;
        if (isEmptyType(ElTy))
          Out << " */";
        else
          printed = true;
    }
    Out << ") {\n  ";
    printTypeName(Out, *it);
    Out << " r;";
    for (unsigned i = 0; i != e; ++i) {
        Type *ElTy = STy ? STy->getElementType(i) : (*it)->getSequentialElementType();
        if (isEmptyType(ElTy))
          continue;
        if (STy)
          Out << "\n  r.field" << i << " = x" << i << ";";
        else if (ATy)
          Out << "\n  r.array[" << i << "] = x" << i << ";";
        else if (VTy)
          Out << "\n  r.vector[" << i << "] = x" << i << ";";
        else
          assert(0);
    }
    Out << "\n  return r;\n}\n";
  }

  // Emit definitions of the intrinsics.
  for (auto I = intrinsicsToDefine.begin(), E = intrinsicsToDefine.end(); I != E; ++I) {
    printIntrinsicDefinition(**I, Out);
  }

  if (!M.empty())
    Out << "\n\n/* Function Bodies */\n";
}

void CWriter::declareOneGlobalVariable(GlobalVariable* I, bool withInitializer) {

  if (I->isDeclaration() || isEmptyType(I->getType()->getPointerElementType()))
    return;

  // Ignore special globals, such as debug info.
  if (getGlobalVariableClass(I))
    return;

  if (I->hasDLLImportStorageClass())
    Out << "__declspec(dllimport) ";
  else if (I->hasDLLExportStorageClass())
    Out << "__declspec(dllexport) ";

  if (I->hasLocalLinkage())
    Out << "static ";

  // Thread Local Storage
  if (I->isThreadLocal())
    Out << "__thread ";

  Type *ElTy = I->getType()->getElementType();
  unsigned Alignment = I->getAlignment();
  bool IsOveraligned = Alignment &&
    Alignment > TD->getABITypeAlignment(ElTy);
  if (IsOveraligned)
    Out << "__MSALIGN__(" << Alignment << ") ";
  printTypeName(Out, ElTy, false) << ' ' << GetValueName(I);
  if (IsOveraligned)
    Out << " __attribute__((aligned(" << Alignment << ")))";

  if (I->hasLinkOnceLinkage())
    Out << " __attribute__((common))";
  else if (I->hasWeakLinkage())
    Out << " __ATTRIBUTE_WEAK__";
  else if (I->hasCommonLinkage())
    Out << " __ATTRIBUTE_WEAK__";

  if (I->hasHiddenVisibility())
    Out << " __HIDDEN__";

  if(withInitializer)
  {
    // If the initializer is not null, emit the initializer.  If it is null,
    // we try to avoid emitting large amounts of zeros.  The problem with
    // this, however, occurs when the variable has weak linkage.  In this
    // case, the assembler will complain about the variable being both weak
    // and common, so we disable this optimization.
    // FIXME common linkage should avoid this problem.
    if (!I->getInitializer()->isNullValue()) {
      Out << " = " ;
      writeOperand(I->getInitializer(), ContextStatic);
    } else if (I->hasWeakLinkage()) {
      // We have to specify an initializer, but it doesn't have to be
      // complete.  If the value is an aggregate, print out { 0 }, and let
      // the compiler figure out the rest of the zeros.
      Out << " = " ;
      if (I->getInitializer()->getType()->isStructTy() ||
          I->getInitializer()->getType()->isVectorTy()) {
        Out << "{ 0 }";
      } else if (I->getInitializer()->getType()->isArrayTy()) {
        // As with structs and vectors, but with an extra set of braces
        // because arrays are wrapped in structs.
        Out << "{ { 0 } }";
      } else {
        // Just print it out normally.
        writeOperand(I->getInitializer(), ContextStatic);
      }
    }
  }
  Out << ";\n";
}

/// Output all floating point constants that cannot be printed accurately...
void CWriter::printFloatingPointConstants(Function &F) {
  // Scan the module for floating point constants.  If any FP constant is used
  // in the function, we want to redirect it here so that we do not depend on
  // the precision of the printed form, unless the printed form preserves
  // precision.
  //
  for (inst_iterator I = inst_begin(&F), E = inst_end(&F); I != E; ++I)
      for (Instruction::op_iterator I_Op = I->op_begin(), E_Op = I->op_end(); I_Op != E_Op; ++I_Op)
          if (const Constant *C = dyn_cast<Constant>(I_Op))
            printFloatingPointConstants(C);
  Out << '\n';
}

void CWriter::printFloatingPointConstants(const Constant *C) {
  // If this is a constant expression, recursively check for constant fp values.
  if (const ConstantExpr *CE = dyn_cast<ConstantExpr>(C)) {
    for (unsigned i = 0, e = CE->getNumOperands(); i != e; ++i)
      printFloatingPointConstants(CE->getOperand(i));
    return;
  }

  // Otherwise, check for a FP constant that we need to print.
  const ConstantFP *FPC = dyn_cast<ConstantFP>(C);
  if (FPC == 0 ||
      // Do not put in FPConstantMap if safe.
      isFPCSafeToPrint(FPC) ||
      // Already printed this constant?
      FPConstantMap.count(FPC))
    return;

  FPConstantMap[FPC] = FPCounter;  // Number the FP constants

  if (FPC->getType() == Type::getDoubleTy(FPC->getContext())) {
    double Val = FPC->getValueAPF().convertToDouble();
    uint64_t i = FPC->getValueAPF().bitcastToAPInt().getZExtValue();
    Out << "static const ConstantDoubleTy FPConstant" << FPCounter++
    << " = 0x" << utohexstr(i)
    << "ULL;    /* " << Val << " */\n";
  } else if (FPC->getType() == Type::getFloatTy(FPC->getContext())) {
    float Val = FPC->getValueAPF().convertToFloat();
    uint32_t i = (uint32_t)FPC->getValueAPF().bitcastToAPInt().
    getZExtValue();
    Out << "static const ConstantFloatTy FPConstant" << FPCounter++
    << " = 0x" << utohexstr(i)
    << "U;    /* " << Val << " */\n";
  } else if (FPC->getType() == Type::getX86_FP80Ty(FPC->getContext())) {
    // api needed to prevent premature destruction
    const APInt api = FPC->getValueAPF().bitcastToAPInt();
    const uint64_t *p = api.getRawData();
    Out << "static const ConstantFP80Ty FPConstant" << FPCounter++
    << " = { 0x" << utohexstr(p[0])
    << "ULL, 0x" << utohexstr((uint16_t)p[1]) << ",{0,0,0}"
    << "}; /* Long double constant */\n";
  } else if (FPC->getType() == Type::getPPC_FP128Ty(FPC->getContext()) ||
             FPC->getType() == Type::getFP128Ty(FPC->getContext())) {
    const APInt api = FPC->getValueAPF().bitcastToAPInt();
    const uint64_t *p = api.getRawData();
    Out << "static const ConstantFP128Ty FPConstant" << FPCounter++
    << " = { 0x"
    << utohexstr(p[0]) << ", 0x" << utohexstr(p[1])
    << "}; /* Long double constant */\n";

  } else {
    llvm_unreachable("Unknown float type!");
  }
}


/// printSymbolTable - Run through symbol table looking for type names.  If a
/// type name is found, emit its declaration...
///
void CWriter::printModuleTypes(raw_ostream &Out) {
  Out << "/* Helper union for bitcasts */\n";
  Out << "typedef union {\n";
  Out << "  uint32_t Int32;\n";
  Out << "  uint64_t Int64;\n";
  Out << "  float Float;\n";
  Out << "  double Double;\n";
  Out << "} llvmBitCastUnion;\n";

  // Keep track of which types have been printed so far.
  std::set<Type*> TypesPrinted;

  // Loop over all structures then push them into the stack so they are
  // printed in the correct order.
  Out << "\n/* Types Declarations */\n";

  // forward-declare all structs here first

  {
    std::set<Type*> TypesPrinted;
    for (auto it = TypedefDeclTypes.begin(), end = TypedefDeclTypes.end(); it != end; ++it) {
      forwardDeclareStructs(Out, *it, TypesPrinted);
    }
  }

  // forward-declare all function pointer typedefs (Issue #2)

  {
    std::set<Type*> TypesPrinted;
    for (auto it = TypedefDeclTypes.begin(), end = TypedefDeclTypes.end(); it != end; ++it) {
      forwardDeclareFunctionTypedefs(Out, *it, TypesPrinted);
    }
  }


  Out << "\n/* Types Definitions */\n";

  for (auto it = TypedefDeclTypes.begin(), end = TypedefDeclTypes.end(); it != end; ++it) {
    printContainedTypes(Out, *it, TypesPrinted);
  }

  Out << "\n/* Function definitions */\n";

  for (auto I = UnnamedFunctionIDs.begin(), E = UnnamedFunctionIDs.end(); I != E; ++I) {
    Out << '\n';
    std::pair<FunctionType*, std::pair<AttributeSet, CallingConv::ID> > F = I->first;
    if (F.second.first == AttributeSet() && F.second.second == CallingConv::C)
        if (!TypesPrinted.insert(F.first).second) continue; // already printed this above
    printFunctionDeclaration(Out, F.first, F.second);
  }

  // We may have collected some intrinsic prototypes to emit.
  // Emit them now, before the function that uses them is emitted
  for (auto I = prototypesToGen.begin(), E = prototypesToGen.end(); I != E; ++I) {
    Out << '\n';
    Function *F = *I;
    printFunctionProto(Out, F);
    Out << ";\n";
  }
}

void CWriter::forwardDeclareStructs(raw_ostream &Out, Type *Ty, std::set<Type*> &TypesPrinted) {
  if (!TypesPrinted.insert(Ty).second) return;
  if (isEmptyType(Ty)) return;

  for (auto I = Ty->subtype_begin(); I != Ty->subtype_end(); ++I) {
    forwardDeclareStructs(Out, *I, TypesPrinted);
  }

  if (StructType *ST = dyn_cast<StructType>(Ty)) {
    Out << getStructName(ST) << ";\n";
  }
}

void CWriter::forwardDeclareFunctionTypedefs(raw_ostream &Out, Type *Ty, std::set<Type*> &TypesPrinted) {
  if (!TypesPrinted.insert(Ty).second) return;
  if (isEmptyType(Ty)) return;

  for (auto I = Ty->subtype_begin(); I != Ty->subtype_end(); ++I) {
    forwardDeclareFunctionTypedefs(Out, *I, TypesPrinted);
  }

  if (FunctionType *FT = dyn_cast<FunctionType>(Ty)) {
    printFunctionDeclaration(Out, FT);
  }
}

// Push the struct onto the stack and recursively push all structs
// this one depends on.
//
void CWriter::printContainedTypes(raw_ostream &Out, Type *Ty,
                                    std::set<Type*> &TypesPrinted) {
  // Check to see if we have already printed this struct.
  if (!TypesPrinted.insert(Ty).second) return;
  // Skip empty structs
  if (isEmptyType(Ty)) return;

  // Print all contained types first.
  for (Type::subtype_iterator I = Ty->subtype_begin(), E = Ty->subtype_end(); I != E; ++I)
    printContainedTypes(Out, *I, TypesPrinted);

  if (StructType *ST = dyn_cast<StructType>(Ty)) {
    // Print structure type out.
    printStructDeclaration(Out, ST);
  } else if (ArrayType *AT = dyn_cast<ArrayType>(Ty)) {
    // Print array type out.
    printArrayDeclaration(Out, AT);
  } else if (VectorType *VT = dyn_cast<VectorType>(Ty)) {
    // Print vector type out.
    printVectorDeclaration(Out, VT);
  }
}

bool CBackend::isFPIntBitCast(Instruction &I) {
  if (!isa<BitCastInst>(I))
    return false;
  Type *SrcTy = I.getOperand(0)->getType();
  Type *DstTy = I.getType();
  return (SrcTy->isFloatingPointTy() && DstTy->isIntegerTy()) ||
         (DstTy->isFloatingPointTy() && SrcTy->isIntegerTy());
}

void CWriter::printFunction(Function &F) {
  /// isStructReturn - Should this function actually return a struct by-value?
  bool isStructReturn = F.hasStructRetAttr();

  // keep track of all the byVal arguments
  for(auto& arg : F.getArgumentList()) {
    if(arg.hasByValAttr())
      ByValParams.insert(&arg);
  }

  assert(!F.isDeclaration());
  if (F.hasDLLImportStorageClass()) Out << "__declspec(dllimport) ";
  if (F.hasDLLExportStorageClass()) Out << "__declspec(dllexport) ";
  if (F.hasLocalLinkage()) Out << "static ";
  printFunctionProto(Out, F.getFunctionType(), std::make_pair(F.getAttributes(), F.getCallingConv()), GetValueName(&F), &F.getArgumentList());

  Out << " {\n";

  // If this is a struct return function, handle the result with magic.
  if (isStructReturn) {
    Type *StructTy =
      cast<PointerType>(F.arg_begin()->getType())->getElementType();
    Out << "  ";
    printTypeName(Out, StructTy, false) << " StructReturn;  /* Struct return temporary */\n";

    Out << "  ";
    printTypeName(Out, F.arg_begin()->getType(), false);
    Out << GetValueName(&*F.arg_begin()) << " = &StructReturn;\n";
  }

  bool PrintedVar = false;

  // print local variable information for the function
  for (inst_iterator I = inst_begin(&F), E = inst_end(&F); I != E; ++I) {
    if (AllocaInst *AI = isDirectAlloca(&*I)) {
      unsigned Alignment = AI->getAlignment();
      bool IsOveraligned = Alignment &&
        Alignment > TD->getABITypeAlignment(AI->getAllocatedType());
      Out << "  ";
      if (IsOveraligned)
        Out << "__MSALIGN__(" << Alignment << ") ";
      printTypeName(Out, AI->getAllocatedType(), false) << ' ';
      Out << GetValueName(AI);
      if (IsOveraligned)
        Out << " __attribute__((aligned(" << Alignment << ")))";
      Out << ";    /* Address-exposed local */\n";
      PrintedVar = true;
    } else if (!isEmptyType(I->getType()) &&
               !isInlinableInst(*I)) {
      Out << "  ";
      printTypeName(Out, I->getType(), false) << ' ' << GetValueName(&*I);
      Out << ";\n";

      if (isa<PHINode>(*I)) {  // Print out PHI node temporaries as well...
        Out << "  ";
        printTypeName(Out, I->getType(), false) << ' ' << (GetValueName(&*I)+"__PHI_TEMPORARY");
        Out << ";\n";
      }
      PrintedVar = true;
    }
    // We need a temporary for the BitCast to use so it can pluck a value out
    // of a union to do the BitCast. This is separate from the need for a
    // variable to hold the result of the BitCast.
    if (isFPIntBitCast(*I)) {
      Out << "  llvmBitCastUnion " << GetValueName(&*I)
          << "__BITCAST_TEMPORARY;\n";
      PrintedVar = true;
    }
  }

  if (PrintedVar)
    Out << '\n';

  // print the basic blocks
  for (auto it = F.begin(), E = F.end(); it != E; ++it) {
    auto BB = &*it;
    if (Loop *L = LI->getLoopFor(BB)) {
      if (L->getHeader() == BB && L->getParentLoop() == 0)
        printLoop(L);
    } else {
      printBasicBlock(BB);
    }
  }

  Out << "}\n\n";
}

void CWriter::printLoop(Loop *L) {
  Out << "  do {     /* Syntactic loop '" << L->getHeader()->getName()
      << "' to make GCC happy */\n";
  for (unsigned i = 0, e = L->getBlocks().size(); i != e; ++i) {
    BasicBlock *BB = L->getBlocks()[i];
    Loop *BBLoop = LI->getLoopFor(BB);
    if (BBLoop == L)
      printBasicBlock(BB);
    else if (BB == BBLoop->getHeader() && BBLoop->getParentLoop() == L)
      printLoop(BBLoop);
  }
  Out << "  } while (1); /* end of syntactic loop '"
      << L->getHeader()->getName() << "' */\n\n";
}

void CWriter::printBasicBlock(BasicBlock *BB) {

  // Don't print the label for the basic block if there are no uses, or if
  // the only terminator use is the predecessor basic block's terminator.
  // We have to scan the use list because PHI nodes use basic blocks too but
  // do not require a label to be generated.
  //
  bool NeedsLabel = false;
  for (pred_iterator PI = pred_begin(BB), E = pred_end(BB); PI != E; ++PI)
    if (isGotoCodeNecessary(*PI, BB)) {
      NeedsLabel = true;
      break;
    }

  if (NeedsLabel) Out << GetValueName(BB) << ":\n";

  // Output all of the instructions in the basic block...
  for (auto it = BB->begin(), E = --BB->end(); it != E; ++it) {
    auto II = &*it;
    if (!isInlinableInst(*II) && !isDirectAlloca(II)) {
      if (!isEmptyType(II->getType()) &&
          !isInlineAsm(*II))
        outputLValue(II);
      else
        Out << "  ";
      writeInstComputationInline(*II);
      Out << ";\n";
    }
  }

  // Don't emit prefix or suffix for the terminator.
  visit(*BB->getTerminator());
}


//===----------------------------------------------------------------------===//
//                       External Interface declaration
//===----------------------------------------------------------------------===//

bool CTargetMachine::addPassesToEmitFile(
    PassManagerBase &PM, raw_pwrite_stream &Out, CodeGenFileType FileType,
    bool DisableVerify, AnalysisID StartBefore,
    AnalysisID StartAfter, AnalysisID StopAfter,
    MachineFunctionInitializer *MFInitializer) {

  if (FileType != TargetMachine::CGFT_AssemblyFile) return true;

  PM.add(createGCLoweringPass());
  PM.add(createLowerInvokePass());
  PM.add(createCFGSimplificationPass());   // clean up after lower invoke.
  PM.add(new CWriter(Out));
  return false;
}
