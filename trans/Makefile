# This is a template to compile Mercurium phases
# (leave END variable empty)
END=

# IMPORTANT: Do not forget to fill the two variables in Makefile.common
include ../Makefile.common

# IMPORTANT: Fill this with the name of the current phase
PHASE_NAME=trans-phase

# Write here the list of sources (all *.cpp *.cc *.h and *.hpp files you need)
SOURCES=\
	trans_phase.hpp \
	trans_phase.cpp \
    $(END)

prefix=`cat ../../Makefile | grep ^prefix | awk '{print $$3}'`
path := $(shell pwd)

# ------------------------------------------------------------------
# NOTE: Do not modify anything else from this point
# ------------------------------------------------------------------
PHASE_NAME_SO=$(PHASE_NAME).so

# Get the list of headers
HEADERS=$(filter %.h %.hpp, $(SOURCES))
CODE_FILES=$(filter %.cpp %.cc, $(SOURCES))

# This is what mandated .cpp files in SOURCES :)
BASENAME_OBJECTS=$(basename $(CODE_FILES))
OBJECTS=$(addsuffix .o, $(BASENAME_OBJECTS))

# Compiler configuration
CXX=g++
CXXFLAGS=-Wl, -fPIC -g -std=`cat ../../Makefile | grep 'CXXFLAGS' | awk 'BEGIN {FS="std="}{print $$2}' | awk 'BEGIN {FS=" "}{print $$1}'`
LDFLAGS=
MCXX_CXXFLAGS=$(CXXFLAGS) $(tl_cxxflags)
MCXX_LDFLAGS=$(LDFLAGS) $(tl_ldflags)
LINKS=$(prefix)/bin/$(PHASE_NAME)c++ $(prefix)/bin/$(PHASE_NAME)cc $(PHASE_NAME)c++ $(PHASE_NAME)cc

all: $(PHASE_NAME_SO) config.$(PHASE_NAME)

config.$(PHASE_NAME) : config.myphase.in
	@echo [SED] $@
	@sed -e 's|@PWD@|$(path)|' -e 's|@PHASE_NAME@|$(PHASE_NAME)|' config.myphase.in > $@
	@echo "Generating Config Files..."
	@echo "["$(PHASE_NAME)"cc]" > config.$(PHASE_NAME)
	@echo "language = C" >> config.$(PHASE_NAME)
	@echo "options =  " >> config.$(PHASE_NAME)
	@echo "preprocessor_name = gcc ">> config.$(PHASE_NAME)
	@echo "preprocessor_options = -E ">> config.$(PHASE_NAME)
	@echo "compiler_name = gcc " >> config.$(PHASE_NAME)
	@echo "compiler_options =  -lmpi " >> config.$(PHASE_NAME)
	@echo "linker_name = gcc " >> config.$(PHASE_NAME)
	@echo "linker_options =  -lmpi " >> config.$(PHASE_NAME)
	@echo "compiler_phase="$(path)"/trans-phase.so ">> config.$(PHASE_NAME)
	@echo "pragma_prefix=omp" >> config.$(PHASE_NAME)
	@echo "" >> config.$(PHASE_NAME)
	@echo "["$(PHASE_NAME)"c++] ">> config.$(PHASE_NAME)
	@echo "language = C++  ">> config.$(PHASE_NAME)
	@echo "options =  ">> config.$(PHASE_NAME)
	@echo "preprocessor_name = g++  ">> config.$(PHASE_NAME)
	@echo "preprocessor_options = -E ">> config.$(PHASE_NAME)
	@echo "compiler_name = g++  ">> config.$(PHASE_NAME)
	@echo "compiler_options =  -lmpi">> config.$(PHASE_NAME)
	@echo "linker_name = g++  ">> config.$(PHASE_NAME)
	@echo "linker_options =  -lmpi ">> config.$(PHASE_NAME)
	@echo "compiler_phase="$(path)"/"$(PHASE_NAME)".so ">> config.$(PHASE_NAME)
	@echo "pragma_prefix=omp">> config.$(PHASE_NAME)

$(PHASE_NAME_SO): $(OBJECTS)
	@echo [LD] $@
	@$(CXX) -shared -o $@ $+ $(MCXX_LDFLAGS)
	@echo
	@echo Phase generated successfully in file: $@

%.o : %.cpp $(HEADERS)
	@echo [CXX] $@
	@$(CXX) -c $(MCXX_CXXFLAGS) -o $@ $<

%.o : %.cc $(HEADERS)
	@echo [CXX] $<
	@$(CXX) -c $(MCXX_CXXFLAGS) -o $@ $<

.PHONY: clean
clean:
	@echo [CLEAN] $(PHASE_NAME_SO)
	@rm -f $(PHASE_NAME_SO)
	@rm -f config.$(PHASE_NAME)
	@for i in $(OBJECTS); do \
	   echo [CLEAN] $$i; \
	   rm -f $$i; \
	done
	@echo [CLEAN] $(LINKS)
	@rm -f $(LINKS)

install:
	@echo "Copying config.$(PHASE_NAME) file to "$(prefix)"/share/mcxx/config.d/..."
	@cp -i config.$(PHASE_NAME) $(prefix)/share/mcxx/config.d/
	@echo "Rename config.$(PHASE_NAME) file to 10.config."$(PHASE_NAME)"..."
	@mv $(prefix)/share/mcxx/config.d/config.$(PHASE_NAME) $(prefix)/share/mcxx/config.d/10.config.$(PHASE_NAME)
	@echo "Generating softlinks..."
	@ln -fs $(prefix)/bin/mcxx $(prefix)/bin/$(PHASE_NAME)c++
	@ln -fs $(prefix)/bin/mcxx $(prefix)/bin/$(PHASE_NAME)cc

