##############################################################
#
#                   DO NOT EDIT THIS FILE!
#
##############################################################

# If the tool is built out of the kit, PIN_ROOT must be specified in the make invocation and point to the kit root.
ROOT := $(abspath $(shell pwd)/../..)

PIN_ROOT := $(ROOT)/third_party/pin-2.14-71313-gcc.4.4.7-linux
# CC := gcc-4.7
# CXX := g++-4.7
#

ifdef PIN_ROOT
CONFIG_ROOT := $(PIN_ROOT)/source/tools/Config
else
CONFIG_ROOT := ../Config
endif


include $(CONFIG_ROOT)/makefile.config
include makefile.rules
include $(TOOLS_ROOT)/Config/makefile.default.rules
TOOL_CXXFLAGS += -I/usr/local/qsym/include

##############################################################
#
#                   DO NOT EDIT THIS FILE!
#
##############################################################
