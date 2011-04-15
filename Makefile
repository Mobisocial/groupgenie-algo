INCLUDES = \
    -Ideps/boost_1_45_0/ \
	-Ideps/json_spirit_v4.03
    
LIBPATHS = \
    -Ldeps/boost_1_45_0/stage/lib

LIBRARIES= \
    -lboost_system \
    -lboost_filesystem \
    -lboost_regex \
	-lboost_program_options
   
topo-download_LIBRARIES= \
	-lcrypto \
	-lssl

topo-basic_SOURCES=topo-basic.cpp
topo-vector_SOURCES=topo-vector.cpp
topo-export_SOURCES=topo-export.cpp
topo-download_SOURCES=topo-download.cpp
topo-import-xobni_SOURCES=topo-import-xobni.cpp
topo-import-enron_SOURCES=topo-import-enron.cpp
topo-med_SOURCES=topo-med.cpp

CFLAGS = $(INCLUDES) -g -O3 -arch i386
CXXFLAGS = $(CFLAGS)
LDFLAGS = $(LIBPATHS) $(LIBRARIES) -arch i386
    
EXECUTABLES=topo-basic topo-vector topo-export topo-download topo-import-xobni topo-import-enron topo-med

define EXECUTABLE_template
$(1): $$($(1)_OBJECTS)
	$$(CXX) $$($(1)_LDFLAGS) $$($(1)_OBJECTS) -o $$@
endef

define LDFLAGS_template
$(1)_LDFLAGS := $(LDFLAGS) $$($(1)_LIBRARIES)
endef


define OBJECTS_template
	$(1)_OBJECTS := $$(patsubst %.c,%.o, $$(patsubst %.cc,%.o, $$(patsubst %.cpp,%.o, $$(patsubst %.m,%.o, $$(patsubst %.mm,%.o, $$($(1)_SOURCES))))))
endef

all: $(SOURCES) $(EXECUTABLES)

.cpp.o:
	$(CXX) -c $(CXXFLAGS) $< -o $@

clean:
	rm -f *.o $(EXECUTABLES)

$(foreach prog,$(EXECUTABLES),$(eval $(call OBJECTS_template,$(prog))))
$(foreach prog,$(EXECUTABLES),$(eval $(call LDFLAGS_template,$(prog))))
$(foreach prog,$(EXECUTABLES),$(eval $(call EXECUTABLE_template,$(prog))))

