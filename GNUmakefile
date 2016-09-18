BIN?=bin

SRCS:=\
	tools/llvm-cbe/llvm-cbe.cpp\
	lib/Target/CBackend/CBackend.cpp\
	lib/Target/CBackend/instructions.cpp\
	lib/Target/CBackend/TargetInfo/CBackendTargetInfo.cpp\

OBJS:=$(SRCS:%.cpp=$(BIN)/%.o)

LLVM_CONFIG?=llvm-config

CXXFLAGS+=$(shell $(LLVM_CONFIG) --cflags || echo --llvm-was-not-found)
CXXFLAGS+=-fno-rtti
LIBDIR:=$(shell $(LLVM_CONFIG) --libdir)
LIBS:=$(shell $(LLVM_CONFIG) --libs --system-libs || echo --llvm-was-not-found)

all: $(BIN)/llvm-cbe

clean:
	rm -rf $(BIN)

$(BIN)/llvm-cbe: $(OBJS)
	@mkdir -p $(dir $@)
	$(CXX) -o "$@" $^ -L $(LIBDIR) $(LIBS) $(LDFLAGS)

$(BIN)/%.o: %.cpp
	@mkdir -p $(dir $@)
	$(CXX) -std=c++14 -o "$@" -c $(CXXFLAGS) $<

