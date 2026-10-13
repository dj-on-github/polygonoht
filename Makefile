CC = gcc
CFLAGS = -I/usr/local/include -m64 -Wall
LDFLAGS = -L/usr/local/lib 
LDLIBS = -lm

all: polygonoht polygonoht_exact

polygonoht: polygonoht.c 
	$(CC) $(CFLAGS) $(LDFLAGS) polygonoht.c -o polygonoht $(LDLIBS)

polygonoht_exact: polygonoht_exact.c
	$(CC) $(CFLAGS) $(LDFLAGS) polygonoht_exact.c -o polygonoht_exact $(LDLIBS)

# Exhaustive self-test: sweeps every (count1,count11) pair at 13 entropy
# thresholds, checking the integer testers against ideal arithmetic and
# verifying one-sidedness against the closed-form min-entropy rate.
verify: verify.c polygonoht_exact.c
	$(CC) $(CFLAGS) -O2 -Dmain=pg_main -c polygonoht_exact.c -o pg.o
	$(CC) $(CFLAGS) -O2 verify.c pg.o -o verify $(LDLIBS)
	./verify 2304 12
	./verify 512 12
	./verify 4096 10

install:
	cp polygonoht polygonoht_exact /usr/local/bin

clean:
	rm -f polygonoht polygonoht_exact verify pg.o
