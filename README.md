# polygonoht
Run binary data through the polygon OHT with n=2304

```$ polygonoht -h
Usage: polygonoht [-h][-o <out filename>][-q][-b][-l][filename]
  [-b] Interpret incoming binary data as big endian
  [-l] Interpret incoming binary data as little endian (the default)
  [-q] Quiet output. Only output the pass rate.
  [-o <filename>] Send output text to a file
  [-h] Print out this help information

Run binary data through the polygon OHT with n=2304.
  Author: David Johnston, dj@deadhat.com
```

The Polygon Test

This is an entropy test for binary data that has any combination of
bias a serial correlation. The test works on blocks of 2304 bits.
A block is either passed or failed by the test.
The test establishes that a a pair of pattern counts from the data
lands within a polygon shape in the P1/P11 plane. This shows that
the entropy of the data is above 0.3 bits of min entropy per bit
of data.
For data with entropy rate below 0.3, the test should always fail.
For data with entropy rate above 0.4, the test should always pass.
Between 0.3 and 0.4, the test may either pass or fail. This is the
test pass/fail transition region.

The block size of 2304 bits is due to a two things:
1) 2304 bits is enough to get a pass/fail cut off region within
   an entropy rate space of 0.1.
2) 2304 bits is the amount of noise source data necessary to seed
   a 256 bit CTR DRBG via a 6X extration ratio conditioner.
