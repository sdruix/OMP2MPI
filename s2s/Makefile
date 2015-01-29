SOURCE=s2s.cpp
GENERATOR_NAME=omp2mpi
path := $(shell pwd)
CXX=g++ -std=c++0x
CXXFLAGS=-Wall -fPIC -g 
prefix=`cat ../../Makefile | grep ^prefix | awk '{print $$3}'`

all:  
	@$(CXX) $(SOURCE) $(CXXFLAGS) -o $(GENERATOR_NAME)

clean:
	@echo [CLEAN] $(PHASE_NAME_SO)
	@rm -f $(PHASE_NAME_SO)
	@rm -f $(prefix)/$(GENERATOR_NAME)

install:
	@cp $(GENERATOR_NAME) $(prefix)/bin
