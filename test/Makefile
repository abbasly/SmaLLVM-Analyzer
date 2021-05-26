CC=@clang-10
OPT=@opt-10
RM=@rm

EXAMPLE_C_FILES = $(shell find . -type f -name '*.c')
EXAMPLE_LL_FILES = $(patsubst %.c, %.ll, $(EXAMPLE_C_FILES))

all: $(EXAMPLE_LL_FILES)

%.ll: %.c
	$(CC) -c -emit-llvm -S -fno-discard-value-names -O0 -Xclang -disable-O0-optnone -o $*.tmp.ll $< -g
	$(OPT) -mem2reg -S -o $*.ll $*.tmp.ll
	$(RM) -f $*.tmp.ll

clean:
	$(RM) -f *.ll
