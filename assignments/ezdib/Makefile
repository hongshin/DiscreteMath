
default_target: all
_END_ := 1

#-------------------------------------------------------------------
# Configure
#-------------------------------------------------------------------

OUTNAME := test_ezdib
OUTTYPE := exe

ifneq ($(findstring debug,$(TGT)),)
	CFG_DBG := 1
endif
		   
ifneq ($(findstring windows,$(TGT)),)
	CFG_WIN := 1
	CFG_SYSTEM := windows
else
	CFG_SYSTEM := posix
endif

ifneq ($(findstring static,$(TGT)),)
	CFG_STATIC := 1
endif

ifdef CFG_WIN
	PR := i586-mingw32msvc-
endif

#-------------------------------------------------------------------
# Input / Output
#-------------------------------------------------------------------

# Create bin output path
BINPATH := ../bin/$(CFG_SYSTEM)
ifdef CFG_STATIC
	BINPATH := $(BINPATH)-static
else
	BINPATH := $(BINPATH)-shared
endif

ifdef CFG_DBG
	BINPATH := $(BINPATH)-debug
endif

# Create intermediate file output path
OBJPATH := $(BINPATH)/_obj/$(OUTNAME)

# Output file
ifdef CFG_WIN
	ifeq ($(OUTTYPE),dll)
		OUTFILE := $(BINPATH)/$(OUTNAME).dll
	else
		OUTFILE := $(BINPATH)/$(OUTNAME).exe
	endif
else
	ifeq ($(OUTTYPE),dll)
		OUTFILE := $(BINPATH)/$(OUTNAME).so
	else
		OUTFILE := $(BINPATH)/$(OUTNAME)
	endif
endif

# Input files
CCFILES := $(wildcard *.c)
PPFILES := $(wildcard *.cpp)

# Object files
DEPENDS := $(foreach f,$(CCFILES),$(OBJPATH)/c/$(f:.c=.obj)) \
		   $(foreach f,$(PPFILES),$(OBJPATH)/cpp/$(f:.cpp=.obj))

#-------------------------------------------------------------------
# Tools
#-------------------------------------------------------------------

# Paths tools
RM := rm -f
MD := mkdir -p

# GCC
PP := $(PR)g++ -c
CC := $(PR)gcc -c
LD := $(PR)g++
AR := $(PR)ar -cr
RC := $(PR)windres

PP_FLAGS :=
CC_FLAGS :=
LD_FLAGS :=

ifdef CFG_STATIC
	PP_FLAGS := $(PP_FLAGS) -static
	CC_FLAGS := $(CC_FLAGS) -static
else
	PP_FLAGS := $(PP_FLAGS) -shared
	CC_FLAGS := $(CC_FLAGS) -shared
endif

ifeq ($(OUTTYPE),dll)
	LD_FLAGS := $(LD_FLAGS) -shared -module
else
	ifdef CFG_STATIC
	LD_FLAGS := $(LD_FLAGS) -static
	endif
endif

ifndef CFG_WIN
	PP_FLAGS := $(PP_FLAGS) -fPIC
	CC_FLAGS := $(CC_FLAGS) -fPIC
	LD_FLAGS := $(LD_FLAGS) -fPIC
endif

ifdef CFG_DBG
	PP_FLAGS := $(PP_FLAGS) -g -DDEBUG -D_DEBUG
	CC_FLAGS := $(CC_FLAGS) -g -DDEBUG -D_DEBUG
	LD_FLAGS := $(LD_FLAGS) -g
else
	PP_FLAGS := $(PP_FLAGS) -O2
	CC_FLAGS := $(CC_FLAGS) -O2
endif


#-------------------------------------------------------------------
# Build
#-------------------------------------------------------------------

# Create 'c++' object file path
$(OBJPATH)/cpp :
	- $(MD) $@

# Create 'c' object file path
$(OBJPATH)/c :
	- $(MD) $@

# How to build a 'c++' file
$(OBJPATH)/cpp/%.obj : %.cpp $(OBJPATH)/cpp
	$(PP) $< $(PP_FLAGS) -o $@

# How to build a 'c' file
$(OBJPATH)/c/%.obj : %.c $(OBJPATH)/c
	$(CC) $< $(CC_FLAGS) -o $@

# Build the output
$(OUTFILE) : $(DEPENDS)
	- $(RM) $@
	$(LD) $(LD_FLAGS) $(DEPENDS) -o "$@"

# Default target
all : $(OUTFILE)

clean :
	- $(RM) -R $(OBJPATH)

rebuild : clean all
