import sys, random, math
# gen_markov.py mu scc nbytes seed  -> raw bytes on stdout, LSB-first packing
mu, scc, nbytes, seed = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
p01 = mu*(1.0-scc); p10 = (1.0-mu)*(1.0-scc)
p11, p00 = 1.0-p10, 1.0-p01
h = -math.log2(max(p11, p00, math.sqrt(p01*p10)))
print(f"# p01={p01:.4f} p10={p10:.4f} Hinf={h:.4f}", file=sys.stderr)
rng = random.Random(seed)
state = 1 if rng.random() < mu else 0
out = bytearray()
byte = 0
for i in range(nbytes*8):
    if state == 1:
        state = 0 if rng.random() < p10 else 1
    else:
        state = 1 if rng.random() < p01 else 0
    byte |= (state << (i & 7))
    if (i & 7) == 7:
        out.append(byte); byte = 0
sys.stdout.buffer.write(out)
