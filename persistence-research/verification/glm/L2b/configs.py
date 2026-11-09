# L2b configs.py — enumerate every digit-multiset family for the targets, every
# position configuration, dedup equations, apply the mod-8/mod-5 parity kill.
#
# Framework (r6/r8): n = repunit(L) + sum_{i: d_i!=1} (d_i-1) 10^i  (L digits, no zeros),
# so  9n = 10^L + sum_far A_i 10^{q_i} + K,  A_i = 9(d_i-1),  K = 9*S_low - 1,
# S_low = sum_{i<3, d_i!=1} (d_i-1) 10^i.
# 5 | Pi(n) iff 5 | t; then the single digit 5 is at position 0 (n ends in 5, n odd).
# (H) all non-1 digits at positions >= 3: killed by the Level-2 lemma (re-proved).
import itertools, json, math

TARGETS = [12, 14, 15, 16, 18, 21, 24, 32, 42, 81]

def multisets(t):
    res = set()
    def rec(rem, start, cur):
        if rem == 1:
            if cur: res.add(tuple(sorted(cur)))
            return
        for d in range(start, 10):
            if rem % d == 0:
                rec(rem // d, d, cur + [d])
    rec(t, 2, [])
    return sorted(res)

def v2(K):
    return (K & -K).bit_length() - 1

# ---- parity kill: is there (t,a,w) with 2^t 3^a 7^w = K (mod 8) and (mod 5)? ----
def parity_dead(K):
    # weak (superset) test: does ANY (t,a,w) satisfy 2^t 3^a 7^w = K (mod 8) and (mod 5)?
    # mod 8: 2^t (t<3), 3^a, 7^w have periods 3,2,2 -> t mod 12(=lcm with mod-5's 4), a mod 2, w mod 2.
    # mod 5: all three have period 4 -> the JOINT condition needs a mod 4, w mod 4, t mod 12.
    for t in range(12):
        e8 = pow(2, t, 8) if t < 3 else 0
        for a in range(4):
            for w in range(4):
                if (e8 * pow(3, a, 8) * pow(7, w, 8) - K) % 8 == 0:
                    if (pow(2, t, 5) * pow(3, a, 5) * pow(7, w, 5) - K) % 5 == 0:
                        return False
    return True

out = {}
allK = {}      # K -> list of (t, multiset, config description)
allAK = {}     # (A, K) -> ...
allAAK = {}    # (A1, A2, K) -> ...  (two-far)
higher = []    # (A-tuple, K)

GEN_TARGETS = [x for x in TARGETS if x != 15]   # t=15 handled separately (LHS 5*3^b*7^w)

for t in GEN_TARGETS:
    for ms in multisets(t):
        m = len(ms)
        has5 = 5 in ms
        # positions: low = {0,1,2}, far >= 3
        # enumerate assignments: injective map from multiset elements to positions,
        # split by which positions are low. Represent config as (low_digits_at_pos, far_multiset)
        for f in range(0, m + 1):          # number of far digits
            # choose which elements go far (as multiset) and arrange
            for far_comb in set(itertools.combinations(range(m), f)):
                far_ms = tuple(sorted(ms[i] for i in far_comb))
                low_ms = tuple(sorted(ms[i] for i in range(m) if i not in far_comb))
                if f == m:
                    kind = "H"   # all far
                elif f == 0:
                    kind = "alllow"
                elif f == 1:
                    kind = "onefar"
                elif f == 2:
                    kind = "twofar"
                else:
                    kind = f"{f}far"
                # arrange low digits over distinct positions in {0,1,2}
                # far digits: ordered assignment to increasing positions q1<q2<... is
                # captured by the ordered A-list; for dedup we keep (A sorted?) no:
                # (A1@q1, A2@q2) with q1<q2 - both orders are distinct configs.
                for lowperm in set(itertools.permutations(low_ms)):
                    # positions for low digits: choose len(low_ms) of {0,1,2} in order
                    for pos_comb in itertools.combinations(range(3), len(low_ms)):
                        S = sum((d - 1) * 10 ** p for d, p in zip(lowperm, pos_comb))
                        K = 9 * S - 1
                        if has5:
                            # n ends in 5 => digit 5 is at position 0 (always low)
                            if 5 not in lowperm:
                                continue
                            if lowperm[pos_comb.index(0)] != 5:
                                continue
                        desc = {"t": t, "ms": ms, "kind": kind, "S": S, "K": K,
                                "low": list(lowperm), "lowpos": list(pos_comb),
                                "far": list(far_ms)}
                        if has5:
                            # far digits plus low: the digit 5 must be at pos 0:
                            # handled by the has5 filter inside permutations below
                            pass
                        key = json.dumps(desc, sort_keys=True)
                        if kind == "H":
                            continue  # dead by lemma (verified separately)
                        if kind == "alllow":
                            allK.setdefault(K, []).append((t, ms, desc))
                        elif kind == "onefar":
                            for fa in set(itertools.permutations(far_ms)):
                                A = 9 * (fa[0] - 1)
                                allAK.setdefault((A, K), []).append((t, ms, desc))
                        elif kind == "twofar":
                            for fa in set(itertools.permutations(far_ms)):
                                A1, A2 = 9 * (fa[0] - 1), 9 * (fa[1] - 1)
                                allAAK.setdefault((A1, A2, K), []).append((t, ms, desc))
                        else:
                            for fa in set(itertools.permutations(far_ms)):
                                higher.append(([9 * (x - 1) for x in fa], K, t, ms))

print("=== all-low K values (1-D) ===")
deadK = sorted(k for k in allK if parity_dead(k))
aliveK = sorted(k for k in allK if not parity_dead(k))
print(f"count {len(allK)}, parity-dead {len(deadK)}: {deadK}")
print(f"alive {len(aliveK)}: {aliveK}")

print("=== one-far (A,K) pairs (2-D) ===")
deadAK = sorted(k for k in allAK if parity_dead(k[1]))
aliveAK = sorted(k for k in allAK if not parity_dead(k[1]))
print(f"count {len(allAK)}, parity-dead {len(deadAK)}, alive {len(aliveAK)}")

print("=== two-far (A1,A2,K) triples (3-D) ===")
deadAA = sorted(k for k in allAAK if parity_dead(k[2]))
aliveAA = sorted(k for k in allAAK if not parity_dead(k[2]))
print(f"count {len(allAAK)}, parity-dead {len(deadAA)}, alive {len(aliveAA)}")

print("=== higher-far ===")
from collections import Counter
c = Counter((tuple(a), K) for a, K, t, ms in higher)
print(f"count {len(c)} distinct (A-tuple, K)")
for (a, K), n in sorted(c.items()):
    print("  ", a, K, "parity_dead" if parity_dead(K) else "alive")

json.dump({"aliveK": aliveK, "deadK": deadK,
           "aliveAK": [list(k) for k in aliveAK], "deadAK": [list(k) for k in deadAK],
           "aliveAAK": [list(k) for k in aliveAA], "deadAAK": [list(k) for k in deadAA],
           "higher": [[a, K] for a, K in sorted(c.items())],
           "higher_dead": [[a, K] for (a, K), n in sorted(c.items()) if parity_dead(K)]},
          open("/home/mj-kang/Documents/Dev/math/persistence-research/verification/glm/L2b/configs.json", "w"))
