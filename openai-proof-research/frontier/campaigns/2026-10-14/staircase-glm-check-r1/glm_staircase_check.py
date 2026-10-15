#!/usr/bin/env python3
"""Independent GLM implementation check: staircase tensor projection (m = 1, 2, 3).

Owner directory: frontier/campaigns/2026-10-14/staircase-glm-check-r1
Bound candidate: fresh-algebra-discovery-r1/candidate.md (Sections 1-4)
  SHA256 6b2e14d58ef3e132a666e3cdc6dbb3a2caa53a514301dc30323b6b7cf652c179
  length 17969 bytes, 151 lines, read in full.

Everything below is implemented from scratch from the candidate's stated
conventions; nothing is imported from the author's projection_controls.py or
any other checker, and no uniqueness lemma is assumed as a premise.

Conventions implemented (candidate Sections 1-3):
  B = {(i,j): i,j >= 1, i+j <= m+1}, lexicographically ordered, N = m(m+1)/2.
  Rows R_i = ((i,1),...,(i,m+1-i)); columns C_j = ((1,j),...,(m+1-j,j)).
  alt over an ordered block of size r: sum over all pi in S_r of sgn(pi)
  with letter pi(k) placed at the k-th position of the block.
  v_R = tensor_i alt_{R_i}, v_C = tensor_j alt_{C_j}, z = v_R (x) v_R (x) v_C.
  Local map at each cell on a triple word (a,b,c):
      output letter (a+b-1, a) if a == c at that cell, else the whole term dies.
  Content filter: keep an output word iff its multiset of letters is exactly
  D = {(r,a): 1 <= a <= r <= m}, each pair once, no other pair.
  Predicted: exactly one surviving term, the word
      w(i,j) = (m+1-i, m+2-i-j), with coefficient +1.

Position action (candidate Section 1): g e_a = e_{a o g^{-1}}.
J_m inverse used only to read off the group element: given a retained word d
(a bijection B -> D), J_m^{-1}(d) = delta_sigma with sigma = d^{-1} o w, i.e.
sigma(p) is the unique position q with d(q) = w(p).

Run:  python3 -B glm_staircase_check.py   (assertions enabled, no -O)
"""

import hashlib
import json
import platform
import sys
from datetime import datetime, timezone
from itertools import permutations
from pathlib import Path

HERE = Path(__file__).resolve().parent
CAND = HERE / "inputs" / "candidate.md"
RESULTS = HERE / "results"
RESULTS.mkdir(exist_ok=True)

EXPECTED_CAND_SHA = "6b2e14d58ef3e132a666e3cdc6dbb3a2caa53a514301dc30323b6b7cf652c179"
EXPECTED_CAND_BYTES = 17969
EXPECTED_CAND_LINES = 151


def sha256_file(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def sgn(pi):
    """Sign of a permutation given as a tuple pi(1),...,pi(r)."""
    s = 1
    for i in range(len(pi)):
        for j in range(i + 1, len(pi)):
            if pi[i] > pi[j]:
                s = -s
    return s


def build_positions(m):
    """B in lexicographic order, as (i,j) pairs; index = position in list."""
    return [(i, j) for i in range(1, m + 1) for j in range(1, m + 2 - i)]


def build_layer(m, blocks, signed=True):
    """Sum over independent block permutations with (optional) signs.

    blocks: list of ordered position-index lists (disjoint, covering 0..N-1).
    Returns dict: word (tuple of letters, indexed by position) -> integer coeff.
    """
    n = m * (m + 1) // 2
    out = {}
    word = [None] * n

    def rec(bi, coeff):
        if bi == len(blocks):
            key = tuple(word)
            out[key] = out.get(key, 0) + coeff
            return
        blk = blocks[bi]
        r = len(blk)
        for pi in permutations(range(1, r + 1)):
            c = coeff * (sgn(pi) if signed else 1)
            for k, letter in enumerate(pi):
                word[blk[k]] = letter
            rec(bi + 1, c)

    rec(0, 1)
    return out


def negate_layer(layer):
    """Negate every coefficient of a finished layer vector."""
    return {w: -c for w, c in layer.items()}


def row_blocks(m):
    """R_i rows as position-index lists, letters j = 1..m+1-i in order."""
    pos = build_positions(m)
    idx = {p: k for k, p in enumerate(pos)}
    return [[idx[(i, j)] for j in range(1, m + 2 - i)] for i in range(1, m + 1)]


def col_blocks(m):
    """C_j columns as position-index lists, letters i = 1..m+1-j in order."""
    pos = build_positions(m)
    idx = {p: k for k, p in enumerate(pos)}
    return [[idx[(i, j)] for i in range(1, m + 2 - j)] for j in range(1, m + 1)]


def target_word(m):
    pos = build_positions(m)
    return tuple((m + 1 - i, m + 2 - i - j) for (i, j) in pos)


def run_pipeline(vR1, vR2, vC, m, mode="standard"):
    """q^B followed by the content projection pi_D, on the given layer dicts.

    Returns counts and the aggregated output {word: total integer coeff}.
    mode:
      standard : letter (a+b-1, a), local filter a == c, content D exactly.
      no_filter: letter (a+b-1, a), NO local filter, content D exactly.
      drop2    : letter (a+b-1,),   local filter a == c,
                 content: each r in 1..m exactly r times, no other r.
      shift    : letter (a+b, a),   local filter a == c, content D exactly.
      a_eq_b   : letter (a+b-1, a), local filter a == b, content D exactly.
    """
    n = m * (m + 1) // 2
    d_sorted = sorted((r, a) for r in range(1, m + 1) for a in range(1, r + 1))
    want_r = [r for r in range(1, m + 1) for _ in range(r)]

    raw = 0
    local_surv = 0
    content_surv = 0
    agg = {}

    for a, ca in vR1.items():
        for b, cb in vR2.items():
            for c, cc in vC.items():
                raw += 1
                if mode == "no_filter":
                    ok = True
                elif mode == "a_eq_b":
                    ok = all(a[p] == b[p] for p in range(n))
                else:
                    ok = all(a[p] == c[p] for p in range(n))
                if not ok:
                    continue
                local_surv += 1
                if mode == "drop2":
                    word = tuple((a[p] + b[p] - 1,) for p in range(n))
                    if sorted(x[0] for x in word) != want_r:
                        continue
                elif mode == "shift":
                    word = tuple((a[p] + b[p], a[p]) for p in range(n))
                    if sorted(word) != d_sorted:
                        continue
                else:
                    word = tuple((a[p] + b[p] - 1, a[p]) for p in range(n))
                    if sorted(word) != d_sorted:
                        continue
                content_surv += 1
                agg[word] = agg.get(word, 0) + ca * cb * cc

    return {
        "raw_triples": raw,
        "local_survivors": local_surv,
        "content_survivors": content_surv,
        "aggregated": agg,
    }


def invert_perm(g):
    inv = [0] * len(g)
    for i, x in enumerate(g):
        inv[x] = i
    return tuple(inv)


def act_word(word, ginv):
    """g e_a = e_{a o g^{-1}}: letter at position p becomes a(g^{-1}(p))."""
    return tuple(word[ginv[p]] for p in range(len(word)))


def agg_to_json(agg):
    return {json.dumps(list(k)): v for k, v in sorted(agg.items())}


def jw_to_str(word):
    """Render a word over positions (i,j) readably."""
    pos = build_positions(M_CUR)
    return "{" + ", ".join(f"({i},{j})->{list(letter)}" for (i, j), letter in zip(pos, word)) + "}"


M_CUR = 0  # set per-m for rendering


def main():
    cand_sha = sha256_file(CAND)
    cand_bytes = CAND.stat().st_size
    cand_lines = len(CAND.read_text().splitlines())
    assert cand_sha == EXPECTED_CAND_SHA, f"candidate hash changed: {cand_sha}"
    assert cand_bytes == EXPECTED_CAND_BYTES and cand_lines == EXPECTED_CAND_LINES

    results = {
        "bound_candidate": {
            "path": "frontier/campaigns/2026-10-14/fresh-algebra-discovery-r1/candidate.md",
            "copy": "frontier/campaigns/2026-10-14/staircase-glm-check-r1/inputs/candidate.md",
            "sha256": cand_sha,
            "bytes": cand_bytes,
            "lines": cand_lines,
            "read_extent": "full (Sections 1-4 used; file read end to end)",
        },
        "m": {},
    }

    for m in (1, 2, 3):
        global M_CUR
        M_CUR = m
        n = m * (m + 1) // 2
        pos = build_positions(m)
        wt = target_word(m)

        vR1 = build_layer(m, row_blocks(m))
        vR2 = build_layer(m, row_blocks(m))
        vC = build_layer(m, col_blocks(m))
        vR2_unsigned = build_layer(m, row_blocks(m), signed=False)
        vC_neg = negate_layer(build_layer(m, col_blocks(m)))

        mres = {"N": n, "layer_support_sizes": {
            "vR": len(vR1), "vR_second": len(vR2), "vC": len(vC)}}

        # ---- base identity: (pi_D q^B)(z) == e_w with coefficient +1 ----
        base = run_pipeline(vR1, vR2, vC, m, "standard")
        assert base["aggregated"] == {wt: 1}, (m, base["aggregated"])
        mres["base"] = dict(base, aggregated=agg_to_json(base["aggregated"]))
        assert base["raw_triples"] == len(vR1) * len(vR2) * len(vC)

        # ---- reductions mod 2, 3, 5 of the same integer computation ----
        mods = {}
        for p in (2, 3, 5):
            red = {k: v % p for k, v in base["aggregated"].items()}
            red = {k: v for k, v in red.items() if v != 0}
            assert red == {wt: 1 % p} or red == {wt: 1}, (m, p, red)
            mods[p] = agg_to_json(red)
        mres["mod_reductions"] = mods

        # ---- full orbit: P(g z) == delta_g for every g in Sym(B) ----
        # Direct full-orbit expansion (no word-permutation shortcut):
        # each orbit vector g z is rebuilt by permuting the layer supports
        # and re-expanded from scratch through the pipeline.
        orbit_pass = 0
        for g in permutations(range(n)):
            ginv = invert_perm(g)
            gvR1 = {act_word(w, ginv): c for w, c in vR1.items()}
            gvR2 = {act_word(w, ginv): c for w, c in vR2.items()}
            gvC = {act_word(w, ginv): c for w, c in vC.items()}
            res = run_pipeline(gvR1, gvR2, gvC, m, "standard")
            # left inverse: J^{-1}(d) = delta_g, i.e. d = w o g^{-1} and coeff 1
            expected = {tuple(wt[ginv[p]] for p in range(n)): 1}
            assert res["aggregated"] == expected, (
                f"m={m} orbit element {g}: got {res['aggregated']}")
            d = next(iter(res["aggregated"]))
            # independent re-derivation of the group element from d:
            # sigma = d^{-1} o w must equal g (same check, different reading)
            sigma = tuple(next(q for q in range(n) if d[q] == wt[p])
                          for p in range(n))
            assert sigma == g, (f"m={m} sigma mismatch", g, sigma)
            orbit_pass += 1
        mres["orbit_test"] = {
            "method": "direct full-orbit expansion of g z for every g in Sym(B)",
            "orbit_elements_tested": orbit_pass,
            "expected_factorial": math_factorial(n),
            "all_pass_P_gz_equals_delta_g": True,
            "all_pass_d_equals_w_compose_g_inverse": True,
        }

        # ---- negative controls on the base vector z (bounded) ----
        controls = {}

        def record(name, res, note):
            agg = res["aggregated"]
            controls[name] = {
                "counts": {k: res[k] for k in
                           ("raw_triples", "local_survivors", "content_survivors")},
                "aggregated": agg_to_json(agg),
                "rendered": [jw_to_str(w) + f" coeff {v}" for w, v in agg.items()],
                "matches_target_identity": agg == {wt: 1},
                "note": note,
            }

        record("C1_no_equality_filter",
               run_pipeline(vR1, vR2, vC, m, "no_filter"),
               "local map emits (a+b-1,a) unconditionally; content filter kept")
        record("C2_drop_second_coordinate",
               run_pipeline(vR1, vR2, vC, m, "drop2"),
               "letters f_{a+b-1} only (a==c kept); content = each r exactly r times")
        record("C3_sum_shift_a_plus_b",
               run_pipeline(vR1, vR2, vC, m, "shift"),
               "local map emits (a+b,a) instead of (a+b-1,a); a==c kept")
        record("C4_filter_a_equals_b",
               run_pipeline(vR1, vR2, vC, m, "a_eq_b"),
               "local filter a==b instead of a==c")
        record("C5_column_sign_negated",
               run_pipeline(vR1, vR2, vC_neg, m, "standard"),
               "column layer generator sign convention negated")
        record("C6_second_row_layer_unsigned",
               run_pipeline(vR1, vR2_unsigned, vC, m, "standard"),
               "second row layer sums permutations with sign +1 (honest report "
               "required if ineffective)")
        mres["negative_controls"] = controls
        results["m"][m] = mres
        print(f"m={m}: raw={base['raw_triples']} local={base['local_survivors']} "
              f"content={base['content_survivors']} agg={agg_to_json(base['aggregated'])} "
              f"orbits={orbit_pass} controls="
              f"{ {k: v['matches_target_identity'] for k, v in controls.items()} }")

    script_sha = sha256_file(Path(__file__))
    results["environment"] = {
        "python": sys.version,
        "platform": platform.platform(),
        "asserts": "enabled (no -O)",
        "checker_sha256": script_sha,
        "checker_path": "frontier/campaigns/2026-10-14/staircase-glm-check-r1/glm_staircase_check.py",
        "provenance": "implemented from candidate Sections 1-4 conventions only; "
                      "projection_controls.py not read or imported",
    }
    results["run_metadata"] = {
        "utc": datetime.now(timezone.utc).isoformat(),
        "command": "python3 -B glm_staircase_check.py",
    }

    out = RESULTS / "glm_staircase_check_results.json"
    out.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n")
    print(f"results written: {out}")
    print("ALL ASSERTIONS PASSED")


def math_factorial(n):
    f = 1
    for k in range(2, n + 1):
        f *= k
    return f


if __name__ == "__main__":
    main()
