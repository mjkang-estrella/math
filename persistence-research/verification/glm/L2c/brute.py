# L2c brute.py — ground truth: all 7-smooth n (n = 2^i 3^j 7^k, multi-digit)
# with Pi(n) = t, for t in the level-1 set (5-free) and the L2c targets.
# Enumerates ALL triples (i,j,k) with 2^i 3^j 7^k <= 10^B; Pi via decimal digits.
# Run: bash -c 'ulimit -v 1500000; python3 -I brute.py [B]'
import sys, json
from math import log

B = int(sys.argv[1]) if len(sys.argv) > 1 else 100
LB = B * 2.302585092994046  # ln(10^B)

TARGETS = [2, 3, 4, 6, 7, 8, 9, 12, 14, 16, 18, 24, 32, 42, 81, 112, 14112, 111132]
TS = set(TARGETS)
found = {t: [] for t in TARGETS}

n2 = 1
i = 0
count = 0
while log(n2) if n2 > 1 else 0 <= LB:
    if log(n2) > LB:
        break
    n3 = n2
    j = 0
    while True:
        ln = log(n3) if n3 > 1 else 0
        if ln > LB:
            break
        n = n3
        k = 0
        while True:
            if n > 1 and ln + k * 1.9459101490553132 <= LB:
                count += 1
                s = str(n)
                if '0' not in s and '5' not in s:
                    p = 1
                    for ch in s:
                        p *= ord(ch) - 48
                    if p in TS:
                        found[p].append((len(s), n, i, j, k))
            k += 1
            n *= 7
            if n <= 1 or ln + k * 1.9459101490553132 > LB:
                break
        j += 1
        n3 *= 3
        if n3 <= 1 or (log(n3) if n3 > 1 else 0) > LB:
            break
    i += 1
    n2 *= 2
    if (log(n2) if n2 > 1 else 0) > LB:
        break

print(f"B={B} triples considered ~ done; counts:")
out = {}
for t in TARGETS:
    lst = sorted(found[t])
    out[str(t)] = lst
    print(f"  Pi={t:>7}: {len(lst)} members" + (f": {lst[:12]}" + (" ..." if len(lst) > 12 else "") if lst else ""))
with open(f"brute_B{B}.json", "w") as f:
    json.dump(out, f)
print(f"saved brute_B{B}.json")
