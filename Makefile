CC = gcc
CFLAGS = -I/usr/local/include -m64 -Wall
LDFLAGS = -L/usr/local/lib 
LDLIBS = -lm

polygonoht: polygonoht.c 
	$(CC) $(CFLAGS) $(LDFLAGS) polygonoht.c -o polygonoht $(LDLIBS)

install:
	cp polygonoht /usr/local/bin

clean:
	rm polygonoht
