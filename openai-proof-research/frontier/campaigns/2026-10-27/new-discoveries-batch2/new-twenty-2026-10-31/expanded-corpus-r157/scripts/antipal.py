# Conjecture 11 (Rajasekaran-Shallit-Smith): every even N of length n (n odd >= 9) is a sum of
# at most 10 antipalindromes of length n-3. Exhaustive bitset check for given n values.
import sys, json, time
def antipals(L):
    h = L//2; res = []
    for x in range(2**(h-1)):
        first = [1] + [int(b) for b in format(x, '0%db' % (h-1))] if h > 1 else [1]
        w = first + [1 - b for b in reversed(first)]
        res.append(int(''.join(map(str, w)), 2))
    return res
out = {}
for n in map(int, sys.argv[1:]):
    t = time.time(); L = n - 3
    A = [a//2 for a in antipals(L)]          # halve: all even
    top = 2**(n-1)                            # N/2 < 2^(n-1)
    mask = (1 << top) - 1
    reach = 1; total = 1; firstcount = {}
    need_lo, need_hi = 2**(n-2), 2**(n-1)    # N/2 in [2^(n-2), 2^(n-1))
    target = ((1 << need_hi) - 1) ^ ((1 << need_lo) - 1)
    for j in range(1, 11):
        new = 0
        for a in A:
            new |= reach << a
        reach = new & mask
        total |= reach
        firstcount[j] = bin(target & reach).count('1')
    miss = target & ~total
    nm = bin(miss).count('1')
    ex = []
    m = miss
    while m and len(ex) < 10:
        low = (m & -m).bit_length() - 1; ex.append(2*low); m &= m - 1
    out[n] = {'num_antipalindromes': len(A), 'targets': need_hi - need_lo, 'missing': nm, 'examples': ex,
              'covered_by_exactly_j': firstcount, 'sec': round(time.time()-t, 2)}
    print(n, out[n], flush=True)
