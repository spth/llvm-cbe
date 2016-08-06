@C = external constant %MyStruct

%MyStruct = type
{
  %NestedStruct*,
  { i64, %MyStruct* }
}

%NestedStruct = type
{
  i64 (%Info*)*
}

%Info = type
{
  %ObjectTypeInfoVtable*,
  i8*
}

%ObjectTypeInfoVtable = type
{
  %MyStruct*,
  i1 (%Info*, i8*, i8*)*,
  i64 (%Info*)*
}
