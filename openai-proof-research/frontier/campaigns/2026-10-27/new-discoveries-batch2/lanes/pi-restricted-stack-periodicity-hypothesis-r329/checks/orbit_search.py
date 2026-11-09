"""Exact orbit witness search for s_{132,213} and s_{231,213}.

Certificate logic (rigorous for each n searched):
  - s_T(id_n) = rev_n and s_T(rev_n) = id_n (verified directly), so {id,rev} is a
    2-cycle, both members periodic.
  - If EVERY pi in the searched domain has s_T^k(pi) in {id,rev} for some k <= B,
    then any cycle C of the functional graph meets {id,rev}, hence C = {id,rev}
    (cycles are the orbits of their members). So the periodic points are exactly
    {id, rev}. Any unhit orbit within cap B is flagged (would refute).

Domains:
  - Full S_n for n = 3..9.
  - n = 10, 11: two-pass: (a) full-domain chunked run, (b) domain restricted to
    pi_1 = pi_n, which is exhaustive for periodic points because
    (s_T(pi))_n = pi_1 (validated in verify_semantics V6 + proved by the argument
    that the bottom stack element cannot be popped while input remains, since a
    violation needs 3 elements above-or-equal it in the stack word).

Output: work/orbit-search.json with per-n results, max hitting time, flags.
"""
import sys, os, json, itertools, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lib_sT import s_T, reverse_word

T1 = ((1, 3, 2), (2, 1, 3))   # {132,213}
T2 = ((2, 3, 1), (2, 1, 3))   # {231,213}
CAP = 200

def search(n, T, domain=None):
    ident = tuple(range(1, n + 1))
    rev = reverse_word(ident)
    assert s_T(ident, T) == rev and s_T(rev, T) == ident
    if domain is None:
        domain = itertools.permutations(range(1, n + 1))
    hist = {}
    flagged = []
    t0 = time.time()
    count = 0
    for pi in domain:
        if pi == ident or pi == rev:
            continue
        p = pi
        k = 0
        while k <= CAP:
            if p == ident or p == rev:
                break
            p = s_T(p, T)
            k += 1
        if k > CAP:
            flagged.append(pi)
            if len(flagged) > 20:
                break
        else:
            hist[k] = hist.get(k, 0) + 1
        count += 1
        if count % 500000 == 0:
            print(f"  progress n={n}: {count} done, elapsed {time.time()-t0:.1f}s", flush=True)
    return {"n": n, "count": count, "hist": hist, "max_hit": max(hist) if hist else 0,
            "flagged": [list(x) for x in flagged], "all_hit": not flagged,
            "elapsed_s": round(time.time() - t0, 2)}

def main():
    # staged runs:
    #   orbit_search.py <132_213|231_213> full <n>...        full S_n sweep
    #   orbit_search.py <132_213|231_213> chunk <n> <parts> <part>   full S_n, chunk part/parts
    # (An earlier 'restricted pi1==pin' idea was INVALID: pi_1 and pi_n are values
    #  at distinct positions and cannot be equal for n>1. Full sweeps only.)
    name, mode = sys.argv[1], sys.argv[2]
    T = {"132_213": T1, "231_213": T2}[name]
    path = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                        "work", "orbit-search.json")
    out = {}
    if os.path.exists(path):
        out = {k: v for k, v in json.load(open(path)).items() if "restricted" not in k}
    if mode == "full":
        for n in [int(x) for x in sys.argv[3:]]:
            r = search(n, T)
            out[f"{name}_full_n{n}"] = r
            print(f"{name}_full_n{n}", "max_hit", r["max_hit"], "all_hit", r["all_hit"],
                  f"{r['elapsed_s']}s", flush=True)
    else:
        n, parts, part = int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
        def dom():
            for pi in itertools.permutations(range(1, n + 1)):
                if pi[0] % parts == part:
                    yield pi
        r = search(n, T, domain=dom())
        r["domain"] = f"full S_{n}, chunk {part}/{parts} (pi[0] mod {parts} == {part})"
        out[f"{name}_full_n{n}_chunk{part}of{parts}"] = r
        print(f"{name} n{n} chunk {part}/{parts}", "count", r["count"],
              "max_hit", r["max_hit"], "all_hit", r["all_hit"], f"{r['elapsed_s']}s", flush=True)
    with open(path, "w") as f:
        json.dump(out, f, indent=1)
    print("DONE", flush=True)

if __name__ == "__main__":
    main()
