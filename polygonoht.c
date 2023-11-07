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
    //printf("c11 = %d, fifteen_c11 = %d\n", c11, fifteen_c11);
    
    //ten_c11 = s17_mult_by_10(c11);
    //printf("c11 = %d, ten_c11 = %d\n", c11, ten_c11);
    
    two_c1 = s17_mult_by_2(c1);
    //printf("c1 = %d, two_c1 = %d\n", c1, two_c1);
    
    ten_c1 = s17_mult_by_10(c1);
    //printf("c1 = %d, ten_c1 = %d\n", c1, ten_c1);
    
    twenty_c1 = s17_mult_by_20(c1);
    //printf("c1 = %d, twenty_c1 = %d\n", c1, twenty_c1);
    
    ab_ok = s17_x_lt_y(fifteen_c11, (s17_sub(twenty_c1,4*2303)));
    //printf("s17_sub(twenty_c1,4*2303) = %d\n", s17_sub(twenty_c1,4*2303));

    bc_ok = s17_x_lt_y(fifteen_c11, (s17_add(ten_c1,2303)));
    //printf("s17_add(ten_c1,2303) = %d\n", s17_add(ten_c1,2303));
    
    dc_ok = s17_x_gt_y(c11,(s17_sub(two_c1,2303)));
    //printf("c11=%d > s17_sub(two_c1,2303) = %d\n", c11, s17_sub(two_c1,2303));
    
    ed_ok = s17_x_gt_y(five_c11,(s17_sub(five_c1,2*2303)));
    //printf("s17_sub(ten_c1,2*2303) = %d\n", s17_sub(ten_c1,2*2303));
    
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
    int backbyte;

    do {
        if (using_infile==1)
            len = fread(buffer, 1, 288 , ifp);
        else
            len = fread(buffer, 1, 288 , stdin);

        if (len < 288) break;
        
        c1 =0;
        c11 = 0;
        first = 1;
        for (i=0;i<288;i++) {
            abyte = buffer[i];
            //printf("0x%02x\n",abyte); 
            if (bigend==1) { // reverse the byte if big endian
               backbyte=0;
               for (bitnum=0;bitnum<8;bitnum++) {
                   bit = abyte & 0x1; 
                   backbyte = (backbyte << 1)+bit;
                   abyte = abyte >> 1;
               }
               abyte = backbyte;
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
            }
        } // endfor
        
        good = inside_polygon(c1,c11);
        
        if (good==1) pass++;
        else         fail++;
        
        double top;
        double bottom;

        blocks++;
        p1 = (double)c1/(double)(n-1);
        //p11 = (double)c11/(double)(n-1);
        top    = (((n-1.0)*((double)c11))-((double)(c1*c1)));
        bottom = (((n-1.0)*((double)c1 ))-((double)(c1*c1)));
        scc = top/bottom;

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
