"""verify_members.py — independent certificate for the stage-2 pinned results.

For every reported member of F_delta (results_delta{d}.json):
  (1) n = R_L + (delta-1)*10^e, constructed directly;
  (2) exact digit-string check: all 1s except one delta at position e;
  (3) exact smoothness: strip 2,3,7 from 9n; remainder must be 1 and the
      valuations must equal the reported (t, u+2, w);
For every reported phantom (dead-pinned class): recompute N0 and verify the
equation fails on a WIDER candidate window than the sieve used (guards against
candidate-window bugs).

Run under: bash -c 'ulimit -v 3000000; python3 -I verify_members.py'
"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from glm2 import pow10_exp


def digit_string(n):
    return str(n)


def check_member(delta, m):
    L, e, t, u, w = m['L'], m['e'], m['t'], m['u'], m['w']
    n = (10 ** L - 1) // 9 + (delta - 1) * 10 ** e
    # (2) digit string (position e counts from the LEAST significant digit)
    s = digit_string(n)
    assert len(s) == L, (delta, m, len(s))
    assert s[L - 1 - e] == str(delta), (delta, m, s[:50])
    if delta != 1:
        assert s.count(str(delta)) == 1, (delta, m, s[:50])
        assert all(c == '1' for i, c in enumerate(s) if i != L - 1 - e), (delta, m, s[:50])
    # (3) exact smoothness of 9n
    N = 9 * n
    r = N
    t2 = u2 = w2 = 0
    while r % 2 == 0:
        r //= 2; t2 += 1
    while r % 3 == 0:
        r //= 3; u2 += 1
    while r % 7 == 0:
        r //= 7; w2 += 1
    assert r == 1, f"9n not 7-smooth: delta={delta} m={m} rest={str(r)[:50]}"
    assert (t2, u2, w2) == (t, u + 2, w), (delta, m, (t2, u2, w2))
    return True


def check_phantom(delta, ph):
    """The phantom's pinned N0 must fail the equation on a wider window."""
    U2, W2, t = ph['U2'], ph['W2'], ph['t']
    c = 9 * (delta - 1)
    N0 = pow(2, t) * pow(3, U2) * pow(7, W2)
    S = ph['S']
    hits = []
    for L in range(max(1, int(S) - 5), int(S) + 7):
        if L % 48 != ph['L48']:
            continue
        D = N0 + 1 - 10 ** L
        if delta == 1:
            if D == 0:
                hits.append(L)
            continue
        if D > 0 and D % c == 0:
            e = pow10_exp(D // c)
            if e is not None and e < L and e % 48 == ph['e48']:
                hits.append((L, e))
    assert not hits, f"phantom check FAILED delta={delta}: {ph} hits={hits}"
    return True


def main():
    total = 0
    for delta in range(1, 10):
        res = json.load(open(f"results_delta{delta}.json"))
        for m in res['members']:
            check_member(delta, m)
            total += 1
        nph = 0
        for ph in res.get('phantoms', []):
            check_phantom(delta, ph)
            nph += 1
        # completeness vs the raw enumeration file
        enum = []
        with open(f"members_delta{delta}.jsonl") as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith("#"):
                    enum.append(tuple(json.loads(line)))
        mine = sorted((m['L'], m['e'], m['t'], m['u'], m['w'])
                      for m in res['members'] if m['L'] <= 3000)
        assert mine == sorted(enum), f"enum mismatch delta={delta}"
        print(f"delta={delta}: {len(res['members'])} members verified, "
              f"{nph} phantoms re-checked (wider window), enum-complete OK")
    print(f"ALL CERTIFIED: {total} members across 9 families")


if __name__ == "__main__":
    main()
