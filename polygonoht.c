#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <sys/stat.h>
#include <stdint.h>
#include <getopt.h>

// David Johnston
// dj@deadhat.com

// The Polygon Test
// This is an entropy test for binary data that has any combination of
// bias a serial correlation. The test works on blocks of 2304 bits.
// A block is either passed or failed by the test.
// The test establishes that a a pair of pattern counts from the data
// lands within a polygon shape in the P1/P11 plane. This shows that
// the entropy of the data is above 0.3 bits of min entropy per bit
// of data.
// For data with entropy rate below 0.3, the test should always fail.
// For data with entropy rate above 0.4, the test should always pass.
// Between 0.3 and 0.4, the test may either pass or fail. This is the
// test pass/fail transition region.

// The block size of 2304 bits is due to a two things:
// 1) 2304 bits is enough to get a pass/fail cut off region within
//    an entropy rate space of 0.1.
// 2) 2304 bits is the amount of noise source data necessary to seed
//    a 256 bit CTR DRBG via a 6X extration ratio conditioner.

// The arithmetic is done with 17 bit signed arithmetic intended for
// a hardware implementation in silicon.
//
// Multiplies are done with shifts, adds and subtracts
// 
// Multiplying by 2 involves shifting left, but if it's negative
// you must only shift the positive bits and hold the negative msb where it is.
// If it's positive, just shift right.


int s17_mult_by_2(int x);
int s17_mult_by_5(int x);
int s17_mult_by_10(int x);
int s17_mult_by_15(int x);
int s17_mult_by_20(int x);
int s17_add(int x, int y);
int s17_sub(int x, int y);
int s17_x_lt_y(int x,int y);
int s17_x_gt_y(int x,int y);
int s17_sex(int x);

int s17_mult_by_2(int x) {
    int mask = 0x01FFFF;
    int msb = 0x010000;
    
    if ((x & msb) == 0) return (x << 1); // positive so shift
    return (((x << 1) | 0x010000) & mask); // Negative, so keep the msb==1
}

int s17_mult_by_5(int x) {
    int mask = 0x01FFFF;
    int msb = 0x010000;
    
    // positive
    if ((x & msb) == 0) return s17_add(x,(x << 2)); // x*4 + x = x*5;
    
    // negative
    return s17_add(x,(((x << 1) | 0x10000) & mask));
    
}

int s17_mult_by_10(int x) {
    int mask = 0x01FFFF;
    int msb = 0x010000;
    
    // positive
    if ((x & msb) == 0) return s17_add((x << 1),(x << 3)); // x*8 + x*2 = x*10;
    
    // negative
    return s17_add( (((x << 3) | 0x10000) & mask),(((x << 1) | 0x10000) & mask) );
}

int s17_mult_by_15(int x) {
    int mask = 0x01FFFF;
    int msb = 0x010000;
    
    // positive
    if ((x & msb) == 0) return s17_sub((x << 4),x); // x*16 - x = x*15;
    
    // negative
    return s17_sub( (((x << 4) | 0x10000) & mask), x );
}

int s17_mult_by_20(int x) {
    int mask = 0x01FFFF;
    int msb = 0x010000;
    
    // positive
    if ((x & msb) == 0) return s17_add((x << 4),(x << 2)); // x*16 + x*4 = x*20;
    
    // negative
    return s17_add( (((x << 4) | 0x10000) & mask), (((x << 2) | 0x10000) & mask) );
}

int s17_add(int x, int y) {
    int mask = 0x01FFFF;
    
    return ((x+y) & mask);
}

int s17_sub(int x, int y) {
    int mask = 0x01FFFF;

    return ((x-y) & mask);
}

int s17_x_lt_y(int x,int y) {
    int msb = 0x010000;
    if ((s17_sub(x,y) & msb) == msb) return 1;
    return 0;
}

int s17_x_gt_y(int x,int y) {
    int msb = 0x010000;
    if ((s17_sub(x,y) & msb) == 0) return 1;
    return 0;
}

int inside_polygon(int c1, int c11) {
    int five_c11, fifteen_c11; //, ten_c11;
    int two_c1, five_c1, ten_c1, twenty_c1;
    
    int ab_ok;
    int bc_ok;
    int dc_ok;
    int ed_ok;
    
    five_c11 = s17_mult_by_5(c11);
    five_c1 =  s17_mult_by_5(c1);
    
    fifteen_c11 = s17_mult_by_15(c11);
    two_c1 = s17_mult_by_2(c1);
    ten_c1 = s17_mult_by_10(c1);
    twenty_c1 = s17_mult_by_20(c1);
    ab_ok = s17_x_lt_y(fifteen_c11, (s17_sub(twenty_c1,4*2303)));
    bc_ok = s17_x_lt_y(fifteen_c11, (s17_add(ten_c1,2303)));
    dc_ok = s17_x_gt_y(c11,(s17_sub(two_c1,2303)));
    ed_ok = s17_x_gt_y(five_c11,(s17_sub(five_c1,2*2303)));
    
    if (ab_ok && bc_ok && dc_ok && ed_ok) return 1;
    else return 0;
    
}

void mean_scc_to_p1_p11(double mean, double scc, double *p1, double *p11) {
    //double p01;
    double p10;
    
    p10 = (1.0-mean)*(1.0-scc);
    //p01 = mean*(1.0-scc);
    *p11 = 1.0-p10;
    *p1 = mean;
}

// Sign extend to int for display of negatives
int s17_sex(int x) {
    int msb = 0x010000;
    if ((x & msb)==msb)
        return 0xfffe0000 | x;
    else
        return x;    
}

double scc_from_counts(int n, int c1, int c11) {
        double top;
        double bottom;
        double scc;

        top    = (((n-1.0)*((double)c11))-((double)(c1*c1)));
        bottom = (((n-1.0)*((double)c1 ))-((double)(c1*c1)));
        scc = top/bottom;

        return scc;
}

void display_usage() {
    fprintf(stderr,"Usage: polygonoht [-h][-o <out filename>][-q][-b][-l][filename]\n");
    fprintf(stderr,"  [-b] Interpret incoming binary data as big endian\n");
    fprintf(stderr,"  [-l] Interpret incoming binary data as little endian (the default)\n");
    fprintf(stderr,"  [-q] Quiet output. Only output the pass rate.\n");
    fprintf(stderr,"  [-o <filename>] Send output text to a file\n");
    fprintf(stderr,"  [-h] Print out this help information\n");
    fprintf(stderr,"\n");
    fprintf(stderr,"Run binary data through the polygon OHT with n=2304.\n");
    fprintf(stderr,"  Author: David Johnston, dj@deadhat.com\n");
    fprintf(stderr,"\n");
}

int main(int argc, char *argv[]) {
    int n=2304;
    int i;
    int opt;

    FILE *ifp;
    FILE *ofp;
    char filename[1000];
    char infilename[1000];

    int abyte;
    int using_infile;
    int using_outfile;
    int bigend=0;
    int quiet=0;

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

    using_outfile=0;
    filename[0] = (char)0;
    infilename[0] = (char)0;

    int longIndex;

    char optString[] = "o:blqh";
    static const struct option longOpts[] = {
        { "output", no_argument, NULL, 'o' },
        { "help", no_argument, NULL, 'h' },
        { "quiet", no_argument, NULL, 'q' },
        { "bigend", no_argument, NULL, 'b' },
        { "littleend", no_argument, NULL, 'l' },
        { NULL, no_argument, NULL, 0 }
    };

    opt = getopt_long( argc, argv, optString, longOpts, &longIndex );
    while( opt != -1 ) {
        switch( opt ) {
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
                quiet=1;
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

    /* open the output file if needed */

    if (using_outfile==1)
    {
        ofp = fopen(filename, "w");
        if (ofp == NULL) {
            perror("failed to open output file for writing");
            exit(1);
        }
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

    unsigned char buffer[300];
    int bitnum;
    int bit;
    int bitpair;
    size_t len;
    int c1;
    int c11;
    int lastbit = 0;
    int first = 1;
    double p1;
    double scc;
    int blocks = 0;
    int pass=0;
    int fail=0;
    int good;

    do {
        if (using_infile==1)
            len = fread(buffer, 1, 288 , ifp); // 288 bytes is 2304 bits
        else
            len = fread(buffer, 1, 288 , stdin);

        if (len < 288) break; // Don't process final block if too small
        
        c1    = 0;
        c11   = 0;
        first = 1; // Don't count the first bit pair because
                   // bit -1 doesn't exist.

        for (i=0;i<288;i++) {
            abyte = buffer[i];
            //printf("0x%02x\n",abyte); 
            if (bigend==1) { // reverse the byte if big endian
                abyte = byte_reverse_table[abyte];
               //backbyte=0;
               //for (bitnum=0;bitnum<8;bitnum++) {
               //    bit = abyte & 0x1; 
               //    backbyte = (backbyte << 1)+bit;
               //    abyte = abyte >> 1;
               //}
               //abyte = backbyte;
            }

            for (bitnum=0;bitnum<8;bitnum++) { // Do the bit counts
                bit = abyte & 0x1;
                bitpair = (bit << 1) + lastbit;
                if (first != 1) {
                    if (bit==1) c1++;
                    if (bitpair == 0x3) c11++;
                }
                first = 0;
                lastbit=bit;
                abyte = abyte >> 1;
            } // endfor bitnum
        } // endfor i
        
        good = inside_polygon(c1,c11);
        
        if (good==1) pass++;
        else         fail++;
        
        blocks++;
        p1 = (double)c1/(double)(n-1);
        scc = scc_from_counts(n,c1,c11);

        if (quiet==0) {
            if (good==1) printf("PASS : mean=%0.4f  scc=%0.4f\n",p1,scc);
            else         printf("FAIL : mean=%0.4f  scc=%0.4f\n",p1,scc);
        }

    } while (1==1);

    if (quiet==0) {
        printf("Block Count = %d\n",blocks);
        printf("     passes = %d\n",pass);
        printf("      fails = %d\n",fail);
        printf("  pass rate = %0.2f\n",(double)pass/(double)blocks);
    } else {
        printf("%0.4f\n",(double)pass/(double)blocks);
    }
    return 0;
}

