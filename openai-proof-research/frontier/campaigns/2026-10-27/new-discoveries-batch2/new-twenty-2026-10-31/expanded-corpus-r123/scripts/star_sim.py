# 346303: Monte Carlo of the Aldous-Lanoue averaging process on the star S_n (diagnostic only).
import random, math, sys
n = int(sys.argv[1]); reps = int(sys.argv[2]); rng = random.Random(1)
T = int(2 * n * math.log(n)); marks = [0, 1, n // 10, n // 2, n, 2 * n, 4 * n, int(n * math.log(n) / 2), int(n * math.log(n)), T]
acc = {m: 0.0 for m in marks}
for _ in range(reps):
    x = [-1.0 / (n + 1)] * (n + 1); x[0] = 1 - 1.0 / (n + 1)
    for t in range(T + 1):
        if t in acc: acc[t] += sum(abs(v) for v in x)
        i = rng.randrange(1, n + 1); a = (x[0] + x[i]) / 2; x[0] = x[i] = a
print('n', n, 'norm2', math.sqrt(n / (n + 1)), 'norm1_t0', 2 * n / (n + 1))
for m in marks: print('t', m, 't/(n log n)', round(m / (n * math.log(n)), 3), 'E Delta1 ~', round(acc[m] / reps, 4))
