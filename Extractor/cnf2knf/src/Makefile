CXX=g++
OPT = -O2
CFLAGS=-g $(OPT) -Wno-nullability-completeness $(DFLAGS)
CXXFLAGS=-std=c++11
INC = -I../tbuddy
LIB = ../tbuddy/tbuddy.a

all: cnf2knf

cnf2knf: cnf2knf.cpp $(LIB) bdd_analyze.cpp parse.cpp cnf2knf.hpp direct_AMO.hpp encoded_AMO.hpp
	$(CXX) $(CFLAGS) $(CXXFLAGS) $(INC) cnf2knf.cpp parse.cpp bdd_analyze.cpp $(LIB) -o cnf2knf

clean:
	rm -f cnf2knf
	rm -f *~

