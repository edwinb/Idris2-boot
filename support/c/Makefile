LIBTARGET = libidris2_support.a
DYLIBTARGET = libidris2_support.so

.PHONY: build clean install

OBJS = getline.o idris_buffer.o idris_file.o idris_support.o
CFLAGS := -fPIC -O2 ${CFLAGS}

build : $(LIBTARGET) $(DYLIBTARGET)

$(LIBTARGET) : $(OBJS)
	ar rc $(LIBTARGET) $(OBJS)
	ranlib $(LIBTARGET)

$(DYLIBTARGET) : $(OBJS)
	$(CC) -shared $(OBJS) -fPIC -o $(DYLIBTARGET)

install: $(LIBTARGET) $(DYLIBTARGET)
	mkdir -p ${PREFIX}/idris2-${IDRIS2_VERSION}/lib
	install $(LIBTARGET) $(DYLIBTARGET) ${PREFIX}/idris2-${IDRIS2_VERSION}/lib

clean:
	rm -f $(OBJS) $(DYLIBTARGET) $(LIBTARGET)
