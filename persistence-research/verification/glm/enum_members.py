"""enum_members.py — independent exact enumeration of 7-smooth members of
F_delta = {R_L + (delta-1)*10^e : L >= 1, 0 <= e < L} for L <= LMAX.

For each (L, e): N = 9n = 10^L + 9(delta-1)10^e - 1; strip factors 2,3,7 by exact
big-integer division; member iff the remainder is 1.  Checkpointed per L.

Run under: bash -c 'ulimit -v 3000000; python3 -I enum_members.py --delta D'
"""
import sys, json, os, time, argparse

LMAX = 3000


def last_done(path):
    if not os.path.exists(path):
        return 0
    done = 0
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line.startswith("#DONE"):
                done = max(done, int(line.split()[1]))
    return done


def main(delta):
    t0 = time.time()
    path = f"members_delta{delta}.jsonl"
    done = last_done(path)
    if done >= LMAX:
        print(f"delta={delta}: already complete to L={LMAX}")
        return
    pow10 = [10 ** i for i in range(LMAX + 2)]
    out = open(path, "a")
    print(f"delta={delta}: enumerating L in ({done}, {LMAX}]", flush=True)
    for L in range(done + 1, LMAX + 1):
        R = (pow10[L] - 1) // 9
        for e in range(L):
            N = pow10[L] + 9 * (delta - 1) * pow10[e] - 1
            r = N
            t = u2 = w = 0
            while r % 2 == 0:
                r //= 2; t += 1
            while r % 3 == 0:
                r //= 3; u2 += 1
            while r % 7 == 0:
                r //= 7; w += 1
            if r == 1:
                out.write(json.dumps([L, e, t, u2 - 2, w]) + "\n")
        if L % 25 == 0 or L == LMAX:
            out.write(f"#DONE {L}\n")
            out.flush()
            print(f"  L={L} ({time.time()-t0:.0f}s)", flush=True)
    out.close()
    print(f"delta={delta} enumeration complete ({time.time()-t0:.0f}s)")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--delta", type=int, required=True)
    a = ap.parse_args()
    main(a.delta)
