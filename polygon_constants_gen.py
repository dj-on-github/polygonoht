import math

PHI_INV = (math.sqrt(5) - 1) / 2          # golden ratio threshold p* = 1/phi

def polygon_constants(H, n, k=12):
    N, S = n - 1, 1 << k
    p  = 2.0 ** (-H)
    p2 = 2.0 ** (-2 * H)
    if p >= PHI_INV:                       # H <= log2(phi) ~ 0.6942
        c = p2 / (1.0 + p2)                # chord intercept, arc endpoints E,D
        dc_active = True
    else:                                  # triangle regime: arc endpoints A',C'
        c = p2 * (1.0 - p) / ((1.0 - p) ** 2 + p2)
        dc_active = False
    a0 = math.ceil((1.0 - p) * S * N)
    return {
        'A1': math.floor((2.0 - p) * S),   # AB: (count11<<k) <= A1*count1 - A0
        'A0': a0,
        'B1': math.floor(p * S),           # BC: (count11<<k) <= B1*count1
        'C0': math.floor(c * N),           # ED: count11 >= count1 - C0
        'DC': dc_active,                   # DC: count11 >= 2*count1 - N
        'BW': math.ceil(math.log(a0,2))+1  # required bitwidth for arithmetic
    }

for H in [0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9]:
    print(H, polygon_constants(H, 2304))

