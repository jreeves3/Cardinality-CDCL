CC=gcc
CXX=g++
TFLAGS =  -DENABLE_TBDD 
#DFLAGS =  -DCACHESTATS -DINSTRUMENT
DFLAGS =  -DCACHESTATS
#OPT = -O2
OPT = -O0
CFLAGS=-g $(OPT) -Wno-nullability-completeness $(DFLAGS)
CXXFLAGS=-std=c++11

FILES = tbdd.o prover.o bddio.o bddop.o bvec.o cache.o fdd.o ilist.o imatrix.o \
	kernel.o pairs.o prime.o reorder.o tree.o cppext.o eval.o

all: tbuddy.a


tbuddy.a: $(FILES)
	ar cr tbuddy.a $(FILES)

ktest: ktest.cpp clause.cpp clause.hpp tbuddy.a
	$(CXX) $(CFLAGS) $(CXXFLAGS) -o ktest ktest.cpp clause.cpp tbuddy.a

.SUFFIXES: .c .cxx .o 

.c.o:
	$(CC) $(CFLAGS) $(TFLAGS) $(INC) -c $< -o $@

.cpp.o:
	$(CXX) $(CFLAGS) $(CXXFLAGS) $(TFLAGS) $(INC) -c $< -o $@

clean:
	 rm -f *.a *.o *~


