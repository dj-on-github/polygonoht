#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <sys/stat.h>
#include <stdint.h>
#include <math.h>
#include <getopt.h>

// David Johnston
// dj@deadhat.com

// The Polygon Test - Exact Boundary Version
//
// This is an entropy test for binary data whose statistics are captured
// by bias and serial correlation (the 2 parameter Markov model). It
// generalizes polygonoht.c from the fixed (H=0.4, n=2304) image-derived
// polygon to the analytically exact boundary at any entropy threshold H,
// any block size n and any fixed point coefficient precision k, using
// the closed forms derived in "An Exact Analytic Derivation of the
// Polygon Test Boundary for Online Min-Entropy Testing of Binary Data".
//
// With p = 2^-H and working in normalized coordinates
//   x = count1/N, y = count11/N, N = n-1 bit pairs,
// the region of count pairs with min-entropy rate >= H is bounded by:
//   AB : y <= (2-p)x - (1-p)      (P00 <= p)         straight line
//   BC : y <= p x                 (P11 <= p)         straight line
//   CD : y >= 2x - 1              (P01 <= 1)         straight line (exact)
//   DE : (x-y)^2 <= p^2 x(1-x)    (sqrt(P01P10)<=p)  ellipse arc
//   EA : y >= 0                                      automatic for counts
// Above H* = log2(phi) ~ 0.6942 the CD and EA edges are implied by the
// others and never bind (the region becomes a curved triangle).
//
// Two testers are provided:
//
//   inside_polygon(c1, c11, entropy, bitwidth, N)
//     Conservative linear test. The ellipse arc is replaced by its
//     slope-1 chord y >= x - c(H), which lies above the convex arc, so
//     the linearization is one-sided: it can reject data with entropy
//     slightly above H (by at most the chord sagitta), but can never
//     accept data with entropy below H. Comparators:
//       AB : 2^k*count11 <= A1*count1 - A0    A1 = floor((2-p)*2^k)
//                                             A0 = ceil((1-p)*2^k*N)
//       BC : 2^k*count11 <= B1*count1         B1 = floor(p*2^k)
//       DC : count11 >= 2*count1 - N
//       ED : count11 >= count1 - C0           C0 = floor(c(H)*N)
//     All coefficient rounding directions shrink the accept region, so
//     quantization is also one-sided.
//
//   inside_polygon_exact(c1, c11, entropy, bitwidth, N)
//     As above but with the ellipse arc tested exactly using the
//     multiplier based comparison
//       2^k*(count1-count11)^2 <= P2*count1*(N-count1)
//     with P2 = floor(p^2 * 2^k) (floored: conservative direction).
//     This recovers the thin sliver between chord and arc at the cost
//     of two array multiplies (note count1-count11 = count10).
//
// Parameters:
//   entropy  - the min entropy rate bound H, 0 < H <= 1 (double)
//   bitwidth - k, the number of fixed point fraction bits in the scaled
//              coefficients (S = 2^k). k=12 suffices for n=2304 across
//              H = 0.1..0.9; larger n or H near 1 may want more.
//   N        - the number of bits in the tested block (so there are
//              N-1 bit pair positions). polygonoht.c used N=2304.
//
// The integer arithmetic emulates two's complement hardware whose width
// is derived from k and N and reported at startup:
//   linear tests : w_lin  = bits(N-1) + k + 3
//   arc test     : w_arc  = 2*bits(N-1) + k + 3
// All values are wrapped to those widths, and comparisons are performed
// through the sign bit of a subtraction, exactly as a silicon datapath
// would. Operands into the multipliers are nonnegative, so a plain
// multiply-and-mask is bit-identical to the CSD shift-add network that
// would implement the constant multiplies in hardware.

// ------------------------------------------------------------------
// Emulated w-bit two's complement arithmetic (w <= 62)
// ------------------------------------------------------------------

static int64_t sw_wrap(int64_t x, int w) {
    int64_t mask = (((int64_t)1) << w) - 1;
    return x & mask;
}


static int64_t sw_sub(int64_t x, int64_t y, int w) {
    return sw_wrap(x - y, w);
}

// Multiply, wrapped to w bits. For the nonnegative operands used here
// this is identical to the hardware shift-add / CSD network result.
static int64_t sw_mul(int64_t x, int64_t y, int w) {
    return sw_wrap(x * y, w);
}

static int sw_x_lt_y(int64_t x, int64_t y, int w) {
    int64_t msb = ((int64_t)1) << (w - 1);
    if ((sw_sub(x, y, w) & msb) == msb) return 1;
    return 0;
}

static int sw_x_le_y(int64_t x, int64_t y, int w) {
    if (x == y) return 1;
    return sw_x_lt_y(x, y, w);
}

static int sw_x_ge_y(int64_t x, int64_t y, int w) {
    return sw_x_le_y(y, x, w);
}

static int bits64(int64_t v) {
    int b = 0;
    while (v > 0) { b++; v >>= 1; }
    return b;
}

// ------------------------------------------------------------------
// Derived comparator constants for a given (H, k, N)
// ------------------------------------------------------------------

typedef struct {
    // cache key
    double entropy;
    int    k;
    int    nbits;
    // derived values
    int     npairs;     // N-1 bit pair positions
    int64_t S;          // 2^k
    int64_t A1, A0;     // AB line
    int64_t B1;         // BC line
    int64_t C0;         // ED chord
    int64_t P2;         // arc coefficient
    int     dc_active;  // 1 below H* (five edge regime), 0 above (implied)
    int     w_lin;      // emulated width, linear tests
    int     w_arc;      // emulated width, arc test
    int     valid;
} pgc_t;

// Compute the integer comparator constants. Returns 0 on success,
// nonzero on a parameter error (message on stderr).
//
// Rounding directions (all conservative, i.e. shrink the accept region):
//   A1 = floor((2-p)S)   A0 = ceil((1-p)S(N-1))   B1 = floor(pS)
//   C0 = floor(c(H)(N-1))                         P2 = floor(p^2 S)
// Caveat: floor/ceil are evaluated in double precision, leaving ~2^-52
// of ambiguity that matters only if a product lands within that distance
// of an exact integer. For production constant generation evaluate p
// with guard digits (MPFR) to make the roundings unambiguous.
int polygon_constants(double entropy, int bitwidth, int N, pgc_t *pc) {
    double p, p2, c, phi_inv;
    int npairs;

    if (!(entropy > 0.0) || (entropy > 1.0)) {
        fprintf(stderr, "Error: entropy bound must be in (0,1], got %f\n", entropy);
        return 1;
    }
    if ((bitwidth < 1) || (bitwidth > 24)) {
        fprintf(stderr, "Error: bitwidth (fixed point bits k) must be 1..24, got %d\n", bitwidth);
        return 1;
    }
    if (N < 16) {
        fprintf(stderr, "Error: block size N must be at least 16 bits, got %d\n", N);
        return 1;
    }

    npairs = N - 1;

    pc->entropy = entropy;
    pc->k       = bitwidth;
    pc->nbits   = N;
    pc->npairs  = npairs;
    pc->S       = ((int64_t)1) << bitwidth;

    p       = pow(2.0, -entropy);
    p2      = pow(2.0, -2.0 * entropy);
    phi_inv = (sqrt(5.0) - 1.0) / 2.0;

    pc->A1 = (int64_t)floor((2.0 - p) * (double)pc->S);
    pc->A0 = (int64_t)ceil ((1.0 - p) * (double)pc->S * (double)npairs);
    pc->B1 = (int64_t)floor(p * (double)pc->S);
    pc->P2 = (int64_t)floor(p2 * (double)pc->S);

    if (p >= phi_inv) {   // H <= log2(phi): five edge regime, chord E to D
        c = p2 / (1.0 + p2);
        pc->dc_active = 1;
    } else {              // triangle regime, chord A' to C'
        c = p2 * (1.0 - p) / (((1.0 - p) * (1.0 - p)) + p2);
        pc->dc_active = 0;
    }
    pc->C0 = (int64_t)floor(c * (double)npairs);

    // Emulated hardware widths. Products of nonnegative operands are
    // bounded by 2^w_lin-1 / 2^w_arc-1 with one bit of headroom plus
    // the sign bit, so subtraction based comparison cannot alias.
    pc->w_lin = bits64(npairs) + bitwidth + 3;
    pc->w_arc = 2 * bits64(npairs) + bitwidth + 3;

    if (pc->w_arc > 62) {
        fprintf(stderr, "Error: N=%d with k=%d needs %d bit arc arithmetic (max 62).\n",
                N, bitwidth, pc->w_arc);
        return 1;
    }

    pc->valid = 1;
    return 0;
}

// Cache so the inside_polygon(c1,c11,entropy,bitwidth,N) call signature
// does not recompute constants on every block.
static pgc_t *cached_constants(double entropy, int bitwidth, int N) {
    static pgc_t pc = { .valid = 0 };
    if (pc.valid && (pc.entropy == entropy) && (pc.k == bitwidth) && (pc.nbits == N))
        return &pc;
    if (polygon_constants(entropy, bitwidth, N, &pc)) {
        pc.valid = 0;
        return NULL;
    }
    return &pc;
}

// ------------------------------------------------------------------
// The four linear comparators and the arc comparator
// ------------------------------------------------------------------

static int test_ab(const pgc_t *pc, int64_t c1, int64_t c11) {
    int w = pc->w_lin;
    int64_t lhs = sw_wrap(c11 << pc->k, w);                      // 2^k * count11
    int64_t rhs = sw_sub(sw_mul(pc->A1, c1, w), pc->A0, w);      // A1*count1 - A0
    return sw_x_le_y(lhs, rhs, w);
}

static int test_bc(const pgc_t *pc, int64_t c1, int64_t c11) {
    int w = pc->w_lin;
    int64_t lhs = sw_wrap(c11 << pc->k, w);                      // 2^k * count11
    int64_t rhs = sw_mul(pc->B1, c1, w);                         // B1*count1
    return sw_x_le_y(lhs, rhs, w);
}

static int test_dc(const pgc_t *pc, int64_t c1, int64_t c11) {
    int w = pc->w_lin;
    int64_t rhs = sw_sub(sw_wrap(c1 << 1, w), pc->npairs, w);    // 2*count1 - N
    return sw_x_ge_y(c11, rhs, w);
}

static int test_ed_chord(const pgc_t *pc, int64_t c1, int64_t c11) {
    int w = pc->w_lin;
    int64_t rhs = sw_sub(c1, pc->C0, w);                         // count1 - C0
    return sw_x_ge_y(c11, rhs, w);
}

static int test_ed_arc(const pgc_t *pc, int64_t c1, int64_t c11) {
    int w = pc->w_arc;
    int64_t d   = sw_sub(c1, c11, w);                            // = count10, nonnegative
    int64_t lhs = sw_wrap(sw_mul(d, d, w) << pc->k, w);          // 2^k * d^2
    int64_t n0  = sw_sub(pc->npairs, c1, w);                     // N - count1, nonnegative
    int64_t rhs = sw_mul(pc->P2, sw_mul(c1, n0, w), w);          // P2*count1*(N-count1)
    return sw_x_le_y(lhs, rhs, w);
}

// ------------------------------------------------------------------
// The testers
// ------------------------------------------------------------------

// Conservative linear polygon test.
// Returns 1 if the counts show min entropy rate >= entropy, 0 if not,
// -1 on parameter error.
int inside_polygon(int c1, int c11, double entropy, int bitwidth, int N) {
    pgc_t *pc = cached_constants(entropy, bitwidth, N);
    int ab_ok, bc_ok, dc_ok, ed_ok;

    if (pc == NULL) return -1;

    ab_ok = test_ab(pc, c1, c11);
    bc_ok = test_bc(pc, c1, c11);
    dc_ok = test_dc(pc, c1, c11);       // implied above H*, harmless to test
    ed_ok = test_ed_chord(pc, c1, c11);

    if (ab_ok && bc_ok && dc_ok && ed_ok) return 1;
    return 0;
}

// Exact boundary test: as inside_polygon but the ellipse arc is tested
// with the multiplier based comparison. The chord comparison (a single
// extra subtract) is retained in parallel and ORed with the arc result:
// P2 and C0 are floored independently, so at coarse k the integer arc
// boundary can sit fractionally inside the integer chord near the arc
// endpoints. Both comparisons are individually conservative (each accept
// region lies inside the real H >= entropy region), so their union is
// conservative too, and taking it guarantees the exact tester is never
// stricter than inside_polygon().
int inside_polygon_exact(int c1, int c11, double entropy, int bitwidth, int N) {
    pgc_t *pc = cached_constants(entropy, bitwidth, N);
    int ab_ok, bc_ok, dc_ok, ed_ok;

    if (pc == NULL) return -1;

    ab_ok = test_ab(pc, c1, c11);
    bc_ok = test_bc(pc, c1, c11);
    dc_ok = test_dc(pc, c1, c11);
    ed_ok = test_ed_arc(pc, c1, c11) || test_ed_chord(pc, c1, c11);

    if (ab_ok && bc_ok && dc_ok && ed_ok) return 1;
    return 0;
}

// ------------------------------------------------------------------
// Reporting helpers
// ------------------------------------------------------------------

double scc_from_counts(int n, int c1, int c11) {
    double dn  = (double)(n - 1);
    double dc1 = (double)c1;
    double top    = (dn * (double)c11) - (dc1 * dc1);
    double bottom = (dn * dc1) - (dc1 * dc1);
    if (bottom == 0.0) return 0.0;
    return top / bottom;
}

void print_constants(FILE *fp, const pgc_t *pc) {
    fprintf(fp, "# Polygon OHT (exact boundary constants)\n");
    fprintf(fp, "#   H (entropy bound)   = %f\n", pc->entropy);
    fprintf(fp, "#   N (block bits)      = %d  (%d bit pairs)\n", pc->nbits, pc->npairs);
    fprintf(fp, "#   k (fixed point)     = %d  (S = %lld)\n", pc->k, (long long)pc->S);
    fprintf(fp, "#   regime              = %s\n",
            pc->dc_active ? "five edge (H <= log2(phi))" : "triangle (H > log2(phi), DC implied)");
    fprintf(fp, "#   AB : %lld*count11 <= %lld*count1 - %lld\n",
            (long long)pc->S, (long long)pc->A1, (long long)pc->A0);
    fprintf(fp, "#   BC : %lld*count11 <= %lld*count1\n",
            (long long)pc->S, (long long)pc->B1);
    fprintf(fp, "#   DC : count11 >= 2*count1 - %d\n", pc->npairs);
    fprintf(fp, "#   ED : count11 >= count1 - %lld  (chord)\n", (long long)pc->C0);
    fprintf(fp, "#   ED : %lld*(count1-count11)^2 <= %lld*count1*(%d-count1)  (arc)\n",
            (long long)pc->S, (long long)pc->P2, pc->npairs);
    fprintf(fp, "#   arithmetic widths   = %d bits (linear), %d bits (arc)\n",
            pc->w_lin, pc->w_arc);
}

void display_usage() {
    fprintf(stderr,"Usage: polygonoht_exact [-h][-e <entropy>][-k <bitwidth>][-n <blockbits>][-x][-c]\n");
    fprintf(stderr,"                        [-o <out filename>][-q][-b][-l][filename]\n");
    fprintf(stderr,"  [-e <entropy>]  Min entropy rate bound H in (0,1]. Default 0.4\n");
    fprintf(stderr,"  [-k <bitwidth>] Fixed point fraction bits for the coefficients. Default 12\n");
    fprintf(stderr,"  [-n <blockbits>] Bits per tested block (multiple of 8). Default 2304\n");
    fprintf(stderr,"  [-x] Use the exact multiplier based arc test instead of the chord\n");
    fprintf(stderr,"  [-c] Print the derived comparator constants and exit\n");
    fprintf(stderr,"  [-b] Interpret incoming binary data as big endian\n");
    fprintf(stderr,"  [-l] Interpret incoming binary data as little endian (the default)\n");
    fprintf(stderr,"  [-q] Quiet output. Only output the pass rate.\n");
    fprintf(stderr,"  [-o <filename>] Send output text to a file\n");
    fprintf(stderr,"  [-h] Print out this help information\n");
    fprintf(stderr,"\n");
    fprintf(stderr,"Run binary data through the exact boundary polygon OHT.\n");
    fprintf(stderr,"  Author: David Johnston, dj@deadhat.com\n");
    fprintf(stderr,"\n");
}

int main(int argc, char *argv[]) {
    int i;
    int opt;

    FILE *ifp;
    FILE *ofp;
    char filename[1000];
    char infilename[1000];

    int abyte;
    int using_infile;
    int using_outfile;
    int bigend = 0;
    int quiet = 0;
    int exact = 0;
    int dump_constants = 0;

    double entropy = 0.4;
    int bitwidth = 12;
    int n = 2304;

    const unsigned char byte_reverse_table[] = {
      0x00,0x80,0x40,0xC0,0x20,0xA0,0x60,0xE0,0x10,0x90,0x50,0xD0,0x30,0xB0,0x70,0xF0,
      0x08,0x88,0x48,0xC8,0x28,0xA8,0x68,0xE8,0x18,0x98,0x58,0xD8,0x38,0xB8,0x78,0xF8,
      0x04,0x84,0x44,0xC4,0x24,0xA4,0x64,0xE4,0x14,0x94,0x54,0xD4,0x34,0xB4,0x74,0xF4,
      0x0C,0x8C,0x4C,0xCC,0x2C,0xAC,0x6C,0xEC,0x1C,0x9C,0x5C,0xDC,0x3C,0xBC,0x7C,0xFC,
      0x02,0x82,0x42,0xC2,0x22,0xA2,0x62,0xE2,0x12,0x92,0x52,0xD2,0x32,0xB2,0x72,0xF2,
      0x0A,0x8A,0x4A,0xCA,0x2A,0xAA,0x6A,0xEA,0x1A,0x9A,0x5A,0xDA,0x3A,0xBA,0x7A,0xFA,
      0x06,0x86,0x46,0xC6,0x26,0xA6,0x66,0xE6,0x16,0x96,0x56,0xD6,0x36,0xB6,0x76,0xF6,
      0x0E,0x8E,0x4E,0xCE,0x2E,0xAE,0x6E,0xEE,0x1E,0x9E,0x5E,0xDE,0x3E,0xBE,0x7E,0xFE,
      0x01,0x81,0x41,0xC1,0x21,0xA1,0x61,0xE1,0x11,0x91,0x51,0xD1,0x31,0xB1,0x71,0xF1,
      0x09,0x89,0x49,0xC9,0x29,0xA9,0x69,0xE9,0x19,0x99,0x59,0xD9,0x39,0xB9,0x79,0xF9,
      0x05,0x85,0x45,0xC5,0x25,0xA5,0x65,0xE5,0x15,0x95,0x55,0xD5,0x35,0xB5,0x75,0xF5,
      0x0D,0x8D,0x4D,0xCD,0x2D,0xAD,0x6D,0xED,0x1D,0x9D,0x5D,0xDD,0x3D,0xBD,0x7D,0xFD,
      0x03,0x83,0x43,0xC3,0x23,0xA3,0x63,0xE3,0x13,0x93,0x53,0xD3,0x33,0xB3,0x73,0xF3,
      0x0B,0x8B,0x4B,0xCB,0x2B,0xAB,0x6B,0xEB,0x1B,0x9B,0x5B,0xDB,0x3B,0xBB,0x7B,0xFB,
      0x07,0x87,0x47,0xC7,0x27,0xA7,0x67,0xE7,0x17,0x97,0x57,0xD7,0x37,0xB7,0x77,0xF7,
      0x0F,0x8F,0x4F,0xCF,0x2F,0xAF,0x6F,0xEF,0x1F,0x9F,0x5F,0xDF,0x3F,0xBF,0x7F,0xFF
    };

    using_infile = 0;
    using_outfile = 0;
    filename[0] = (char)0;
    infilename[0] = (char)0;

    int longIndex;

    char optString[] = "e:k:n:o:xcblqh";
    static const struct option longOpts[] = {
        { "entropy",   required_argument, NULL, 'e' },
        { "bitwidth",  required_argument, NULL, 'k' },
        { "blockbits", required_argument, NULL, 'n' },
        { "exact",     no_argument,       NULL, 'x' },
        { "constants", no_argument,       NULL, 'c' },
        { "output",    required_argument, NULL, 'o' },
        { "help",      no_argument,       NULL, 'h' },
        { "quiet",     no_argument,       NULL, 'q' },
        { "bigend",    no_argument,       NULL, 'b' },
        { "littleend", no_argument,       NULL, 'l' },
        { NULL,        no_argument,       NULL, 0 }
    };

    opt = getopt_long( argc, argv, optString, longOpts, &longIndex );
    while( opt != -1 ) {
        switch( opt ) {
            case 'e':
                entropy = atof(optarg);
                break;
            case 'k':
                bitwidth = atoi(optarg);
                break;
            case 'n':
                n = atoi(optarg);
                break;
            case 'x':
                exact = 1;
                break;
            case 'c':
                dump_constants = 1;
                break;
            case 'o':
                using_outfile = 1;
                strcpy(filename,optarg);
                break;
            case 'b':
                bigend = 1;
                break;
            case 'l':
                bigend = 0;
                break;
            case 'q':
                quiet = 1;
                break;
            case 'h':   /* fall-through is intentional */
            case '?':
                display_usage();
                exit(0);

            default:
                /* You won't actually get here. */
                break;
        }

        opt = getopt_long( argc, argv, optString, longOpts, &longIndex );
    } // end while

    if (optind < argc) {
        strcpy(infilename,argv[optind]);
        using_infile = 1;
    }

    if ((n % 8) != 0) {
        fprintf(stderr,"Error: block size must be a multiple of 8 bits, got %d\n", n);
        exit(1);
    }

    // Derive the comparator constants up front so parameter errors are
    // reported before any data is read.
    pgc_t pc;
    if (polygon_constants(entropy, bitwidth, n, &pc)) exit(1);

    /* open the output file if needed */

    if (using_outfile==1)
    {
        ofp = fopen(filename, "w");
        if (ofp == NULL) {
            perror("failed to open output file for writing");
            exit(1);
        }
    }
    else ofp = stdout;

    if (dump_constants==1) {
        print_constants(ofp, &pc);
        return 0;
    }

    /* open the input file if needed */
    if (using_infile==1)
    {
        ifp =  fopen(infilename, "rb");

        if (ifp == NULL) {
            perror("failed to open input file for reading");
            exit(1);
        }
    }
    else ifp = stdin;

    int blockbytes = n/8;
    unsigned char *buffer;
    buffer = (unsigned char *)malloc(blockbytes);
    if (buffer==NULL) {
        fprintf(stderr,"Error: could not allocate %d byte block buffer\n",blockbytes);
        exit(1);
    }

    int bitnum;
    int bit;
    int bitpair;
    int lastbit = 0;
    int first;
    size_t len;
    int c1;
    int c11;
    double p1;
    double scc;
    int blocks = 0;
    int pass = 0;
    int fail = 0;
    int good;

    if (quiet==0) print_constants(ofp, &pc);

    do {
        len = fread(buffer, 1, blockbytes, ifp);

        if (len < (size_t)blockbytes) break; // Don't process final block if too small

        c1    = 0;
        c11   = 0;
        first = 1; // The first bit has no predecessor so the first
                   // pair is counted when the second bit arrives.

        for (i=0;i<blockbytes;i++) {
            abyte = buffer[i];
            if (bigend==1) { // reverse the byte if big endian
                abyte = byte_reverse_table[abyte];
            }

            for (bitnum=0;bitnum<8;bitnum++) { // Do the bit counts
                bit = abyte & 0x1;
                bitpair = (bit << 1) + lastbit;
                if (first != 1) {
                    // count1 counts the ones in the left position of
                    // each bit pair, i.e. the first N-1 bits, matching
                    // count1 = count10 + count11 in the derivation.
                    if (lastbit==1) c1++;
                    if (bitpair == 0x3) c11++;
                }
                first = 0;
                lastbit = bit;
                abyte = abyte >> 1;
            } // endfor bitnum
        } // endfor i

        if (exact==1) good = inside_polygon_exact(c1, c11, entropy, bitwidth, n);
        else          good = inside_polygon(c1, c11, entropy, bitwidth, n);

        if (good==1) pass++;
        else         fail++;

        blocks++;
        p1 = (double)c1/(double)(n-1);
        scc = scc_from_counts(n,c1,c11);

        if (quiet==0) {
            if (good==1) fprintf(ofp,"PASS : mean=%0.4f  scc=%0.4f  c1=%d c11=%d\n",p1,scc,c1,c11);
            else         fprintf(ofp,"FAIL : mean=%0.4f  scc=%0.4f  c1=%d c11=%d\n",p1,scc,c1,c11);
        }

    } while (1==1);

    if (quiet==0) {
        fprintf(ofp,"Block Count = %d\n",blocks);
        fprintf(ofp,"     passes = %d\n",pass);
        fprintf(ofp,"      fails = %d\n",fail);
        if (blocks > 0) fprintf(ofp,"  pass rate = %0.2f\n",(double)pass/(double)blocks);
    } else {
        if (blocks > 0) fprintf(ofp,"%0.4f\n",(double)pass/(double)blocks);
        else            fprintf(ofp,"nan\n");
    }

    free(buffer);
    return 0;
}
