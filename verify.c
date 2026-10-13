// Exhaustive verification harness for polygonoht_exact.c
// - checks the emulated-width integer tests against ideal int64 arithmetic
// - checks one-sidedness: every accepted (c1,c11) has H_inf(x,y) >= H
// - checks arc-accept is a superset of chord-accept
#include <stdio.h>
#include <stdint.h>
#include <math.h>
#include <stdlib.h>

extern int inside_polygon(int c1, int c11, double entropy, int bitwidth, int N);
extern int inside_polygon_exact(int c1, int c11, double entropy, int bitwidth, int N);

static double hinf(int c1, int c11, int npairs) {
    double x = (double)c1 / npairs, y = (double)c11 / npairs;
    double t = 0.0, m = 0.0;
    if (c1 > 0)       { t = y / x;                       if (t > m) m = t; }  // P11
    if (c1 < npairs)  { t = (1.0 - 2.0*x + y)/(1.0 - x); if (t > m) m = t; }  // P00
    if (c1 > 0 && c1 < npairs) {
        t = (x - y)/sqrt(x*(1.0-x));                     if (t > m) m = t;    // sqrt(P01P10)
    }
    if (m <= 0.0) return 99.0;
    return -log2(m);
}

int main(int argc, char **argv) {
    int N = atoi(argv[1]);
    int k = atoi(argv[2]);
    int npairs = N - 1;
    double Hs[] = {0.1,0.2,0.3,0.35,0.4,0.5,0.6,0.65,0.6942,0.7,0.8,0.9,1.0};
    int nH = 13;
    double phi_inv = (sqrt(5.0)-1.0)/2.0;
    long long total_checked = 0;

    for (int hi = 0; hi < nH; hi++) {
        double H = Hs[hi];
        double p = pow(2.0,-H), p2 = pow(2.0,-2.0*H);
        int64_t S  = 1LL << k;
        int64_t A1 = (int64_t)floor((2.0-p)*S);
        int64_t A0 = (int64_t)ceil((1.0-p)*S*npairs);
        int64_t B1 = (int64_t)floor(p*S);
        int64_t P2 = (int64_t)floor(p2*S);
        double c = (p >= phi_inv) ? p2/(1.0+p2)
                                  : p2*(1.0-p)/((1.0-p)*(1.0-p)+p2);
        int64_t C0 = (int64_t)floor(c*npairs);

        long long nacc_chord = 0, nacc_arc = 0;
        int mismatches = 0, onesided_fails = 0, superset_fails = 0;
        double worstH = 99.0;

        for (int c1 = 0; c1 <= npairs; c1++) {
            for (int c11 = 0; c11 <= c1; c11++) {
                // ideal arithmetic reference
                int ab = ( (S*c11) <= (A1*(int64_t)c1 - A0) );
                int bc = ( (S*c11) <= (B1*(int64_t)c1) );
                int dc = ( c11 >= 2*c1 - npairs );
                int ed = ( c11 >= c1 - (int)C0 );
                int64_t d = (int64_t)c1 - c11;
                int64_t n0 = npairs - c1;
                int arc = ( (S*d*d) <= (P2*(int64_t)c1*n0) ) || ed;
                int ref_chord = ab && bc && dc && ed;
                int ref_arc   = ab && bc && dc && arc;

                int got_chord = inside_polygon(c1, c11, H, k, N);
                int got_arc   = inside_polygon_exact(c1, c11, H, k, N);

                if (got_chord != ref_chord || got_arc != ref_arc) {
                    if (mismatches < 5)
                        printf("MISMATCH H=%.4f c1=%d c11=%d got(%d,%d) ref(%d,%d)\n",
                               H, c1, c11, got_chord, got_arc, ref_chord, ref_arc);
                    mismatches++;
                }
                if (got_chord && !got_arc) {
                    if (superset_fails < 5)
                        printf("SUPERSET FAIL H=%.4f c1=%d c11=%d\n", H, c1, c11);
                    superset_fails++;
                }
                if (got_arc || got_chord) {   // check one-sidedness of both accept sets
                    double h = hinf(c1, c11, npairs);
                    if (h < worstH) worstH = h;
                    if (h < H - 1e-9) {
                        if (onesided_fails < 5)
                            printf("ONE-SIDED FAIL H=%.4f c1=%d c11=%d Hinf=%.6f\n",
                                   H, c1, c11, h);
                        onesided_fails++;
                    }
                }
                nacc_chord += got_chord;
                nacc_arc   += got_arc;
                total_checked++;
            }
        }
        printf("H=%.4f: accepted chord=%lld arc=%lld  minHinf(accepted)=%.6f  "
               "mismatch=%d onesided=%d superset=%d\n",
               H, nacc_chord, nacc_arc, worstH, mismatches, onesided_fails, superset_fails);
        if (mismatches || onesided_fails || superset_fails) { printf("VERIFY FAILED\n"); return 1; }
    }
    printf("ALL OK: %lld point-tests across %d thresholds, N=%d k=%d\n",
           total_checked, nH, N, k);
    return 0;
}
