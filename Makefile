#
# Makefile for the malloc lab driver
#
# Regular compiler
CC = gcc
# Compiler for mm.c
CLANG = clang
LLVM_PATH = /usr/local/depot/llvm-4.0/bin/

# Change this to -O0 (big-Oh, numeral zero) if you need to use a debugger on your code
COPT = -O3
CFLAGS = -Wall -Wextra -Werror $(COPT) -g -DDRIVER -Wno-unused-function -Wno-unused-parameter
LIBS = -lm -lrt

COBJS = memlib.o fcyc.o clock.o stree.o
NOBJS = mdriver.o mm-native.o $(COBJS)
EOBJS = mdriver-sparse.o mm-emulate.o $(COBJS)

MC = ./macro-check.pl
MCHECK = $(MC)

all: mdriver mdriver-emulate

# Regular driver
mdriver: $(NOBJS)
	$(CC) $(CFLAGS) -o mdriver $(NOBJS) $(LIBS)

# Sparse-mode driver for checking 64-bit capability
mdriver-emulate: $(EOBJS)
	$(CC) $(CFLAGS) -o mdriver-emulate $(EOBJS) $(LIBS)

# Version of memory manager with memory references converted to function calls
mm-emulate.o: mm.c mm.h memlib.h MLabInst.so
	$(LLVM_PATH)$(CLANG) $(CFLAGS) -fno-vectorize -emit-llvm -S mm.c -o mm.bc
	$(LLVM_PATH)opt -load=./MLabInst.so -MLabInst mm.bc -o mm_ct.bc
	$(LLVM_PATH)$(CLANG) -c $(CFLAGS) -o mm-emulate.o mm_ct.bc

mm-native.o: mm.c mm.h memlib.h $(MC)
	$(MCHECK) -f mm.c
	$(LLVM_PATH)$(CLANG) $(CFLAGS) -c mm.c -o mm-native.o

mdriver-sparse.o: mdriver.c fcyc.h clock.h memlib.h config.h mm.h stree.h
	$(CC) -g $(CFLAGS) -DSPARSE_MODE -c mdriver.c -o mdriver-sparse.o

mdriver.o: mdriver.c fcyc.h clock.h memlib.h config.h mm.h stree.h
memlib.o: memlib.c memlib.h
mm.o: mm.c mm.h memlib.h
fcyc.o: fcyc.c fcyc.h
ftimer.o: ftimer.c ftimer.h config.h
clock.o: clock.c clock.h
stree.o: stree.c stree.h

clean:
	rm -f *~ *.o mdriver mdriver-emulate *.bc *.ll stree_test
handin:
	tar -cvf malloclab-handin.tar mm.c
