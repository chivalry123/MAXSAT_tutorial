CFLAGS = -O3 -m64
TARGET = CCECH_finite

all: ${TARGET} clean

${TARGET}: basis_wpms.h wpms.h paws.h wpms.cpp	
	g++ ${CFLAGS} wpms.cpp -o ${TARGET}

clean:
	rm -f *~

cleanup:
	rm -f ${TARGET}
	rm -f *~
