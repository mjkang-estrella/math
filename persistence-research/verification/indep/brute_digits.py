# Digit-level brute force, independent of every 9n = 10^L-1+9S manipulation:
# all L-digit n made of 1s plus >=2 non-1 digits from {2,3,4}, digit product in {4,6,8,9}, n 7-smooth (5 !| n).
import itertools, sys
LP = int(sys.argv[1]) if len(sys.argv) > 1 else 80     # max L for pairs
LT = int(sys.argv[2]) if len(sys.argv) > 2 else 40     # max L for triples
def smooth(n):
    for p in (2, 3, 5, 7):
        if p == 5:
            if n % 5 == 0: return False
            continue
        while n % p == 0: n //= p
    return n == 1
found = []
count = 0
for L in range(1, LP + 1):
    rep = (10 ** L - 1) // 9
    # pairs
    for i, j in itertools.combinations(range(L), 2):
        for d1 in (2, 3, 4):
            for d2 in (2, 3, 4):
                if d1 * d2 not in (4, 6, 8, 9): continue
                n = rep + (d1 - 1) * 10 ** i + (d2 - 1) * 10 ** j
                count += 1
                if smooth(n): found.append((L, str(n)))
    if L <= LT:
        for i, j, k in itertools.combinations(range(L), 3):
            n = rep + 10 ** i + 10 ** j + 10 ** k      # {2,2,2}
            count += 1
            if smooth(n): found.append((L, str(n)))
# the pair loop above counts ordered digit assignments (d1 at i, d2 at j) for i<j : covers all placements of the multiset
print("tested", count, "candidates; members found:", sorted(set(int(s) for _, s in found)))
