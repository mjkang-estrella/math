"""I187 byte authentication, formal identities, and inherited sealed replay.

The finite checks below are algebra on sign variables, not graph or state
enumeration. Mathematical recovery and cut arguments are reviewed in prose.
"""
import itertools
import json
import math
import runpy
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXP = ROOT / "frontier/experiments"
PREVIOUS = runpy.run_path(str(EXP / "i186-parent-validate.py"))
REFERENCE = PREVIOUS["REFERENCE"]
sha = PREVIOUS["sha"]
SOURCE = "frontier/sources/i164_structural_graph_discovery/upstream-paper.tex"
SOURCE_HASH = "03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56"
OUTPUTS = {
    "frontier/iterations/i187-frozen-state-survival.md":
        "6c37f8f35bbbefd181473335a7d1013532d92be70afa17c9717d4508b5d10734",
    "frontier/experiments/i187_frozen_state_survival/analytic-attempt.md":
        "9ba0316f9db9d344b39b3d5637e4474d790696bcd2cdea7016698a611f98468f",
    "frontier/experiments/i187_frozen_state_survival/reading-and-failures.md":
        "a62333f9e1cd118ddd9a751b55906fc1303ff02bc361e75b49d3b48cdd9afa6e",
    "frontier/experiments/i187_frozen_state_survival/input-authentication.json":
        "8d398bd1811d0bc5939fe7b5899888213138a3a9cb2b5b66202178db91ddefe5",
    "frontier/sources/i187_frozen_state_survival/literature.md":
        "686e3c5e5334c4ec0d267488ee7142c1a2ba7b9618da81c20d334a0c72d80947",
}


def authenticate():
    for name, digest in OUTPUTS.items():
        assert sha(name) == digest, name
    found = {"frontier/iterations/i187-frozen-state-survival.md"}
    for directory in ("frontier/experiments/i187_frozen_state_survival",
                      "frontier/sources/i187_frozen_state_survival"):
        for p in (ROOT / directory).rglob("*"):
            assert not p.is_symlink()
            if p.is_file():
                found.add(p.relative_to(ROOT).as_posix())
    assert found == set(OUTPUTS)
    receipt = json.loads((ROOT /
        "frontier/experiments/i187_frozen_state_survival/input-authentication.json").read_bytes())
    assert set(receipt["exclusive_outputs"]) == set(OUTPUTS)
    assert len(receipt["inputs"]) == 16
    anchors = dict(PREVIOUS["OUTPUTS"], **{SOURCE: SOURCE_HASH})
    anchored = 0
    for row in receipt["inputs"]:
        assert sha(row["path"]) == row["sha256"], row["path"]
        if row.get("expected_sha256") is not None:
            assert row["sha256"] == row["expected_sha256"] == anchors[row["path"]]
            anchored += 1
    assert anchored == 6
    PREVIOUS["authenticate"]()
    return {"output_hashes": OUTPUTS, "input_records": receipt["inputs"],
            "supplied_anchors": anchored, "previous_proof_records": "unchanged"}


def formal_checks():
    cut_counts = {
        k: [(a, k-a) for a in range(k+1) if (2*a-k) % 3 == 0]
        for k in (1, 2, 3)
    }
    assert cut_counts == {1: [], 2: [(1, 1)], 3: [(0, 3), (3, 0)]}
    fourier_cases = endpoint_cases = 0
    for c in range(1, 4):
        signs = list(itertools.product((-1, 1), repeat=c))
        # Exhaust Boolean functions on up to three formal signs.
        # Laurent monomials retain distinct exponents, so no numeric
        # evaluation can hide an incorrect coefficient identity.
        for bits in range(1 << len(signs)):
            values = [(bits >> i) & 1 for i in range(len(signs))]
            coefficients = {
                mask: Fraction(sum(g * math.prod(e[j] for j in range(c)
                                                if (mask >> j) & 1)
                                   for e, g in zip(signs, values)), 2**c)
                for mask in range(1 << c)
            }
            for e, g in zip(signs, values):
                lhs = g * math.prod(e)
                # 2^c times the cosh/sinh denominators cancel.
                rhs = sum(coefficient * math.prod(e[j] for j in range(c)
                                                  if not (mask >> j) & 1)
                          for mask, coefficient in coefficients.items())
                assert lhs == rhs
            fourier_cases += 1
    for c in range(1, 5):
        signs = list(itertools.product((-1, 1), repeat=c))
        for fixed in itertools.product((-1, 0, 1), repeat=c):
            if sum(bool(v) for v in fixed) > 2:
                continue
            free = [j for j, v in enumerate(fixed) if not v]
            q = len(free)
            retained = [e for e in signs if all(not v or e[j] == v
                                               for j, v in enumerate(fixed))]
            # L_j^+ = m_j+d_j, L_j^- = m_j-d_j, d_j=j+1>0.
            weights = [sum((j+2) + e[j]*(j+1) for j in range(c))
                       for e in retained]
            taylor = [
                sum(Fraction(math.prod(e) * w**n, math.factorial(n))
                    for e, w in zip(retained, weights))
                for n in range(q+1)
            ]
            assert all(v == 0 for v in taylor[:q])
            expected = math.prod(v for v in fixed if v) * math.prod(2*(j+1) for j in free)
            assert taylor[q] == expected != 0
            # Gaussian unit phases are represented by powers of i modulo 4.
            fplus = fixed.count(1)
            fminus = fixed.count(-1)
            assert (3*c + 2*fminus) % 4 == (3*(q+fplus) + fminus) % 4
            endpoint_cases += 1
    assert fourier_cases == 276 and endpoint_cases == 64
    return {
        "small_cut_color_counts": cut_counts,
        "exact_Boolean_Fourier_identities": fourier_cases,
        "endpoint_mark_order_and_phase_cases": endpoint_cases,
        "scope": "Formal sign algebra and cut arithmetic only; no actual graph/state tests or nonvanishing theorem",
    }


def replay():
    before = authenticate()
    checks = formal_checks()
    reference, proc = REFERENCE["replay"]()
    assert reference["status"] == "PASS" and authenticate() == before
    return {"status": "PASS", "authentication": before, "formal_checks": checks,
            "sealed_reference_replay": reference, "I187_computational_seal": False,
            "local_ear_mechanism": "PARKED", "E183": "UNRESOLVED",
            "Z184": "UNRESOLVED"}, proc


if __name__ == "__main__":
    assert sys.flags.isolated and sys.dont_write_bytecode
    assert not sys.argv[1:]
    result, proc = replay()
    prefix = EXP / "i187-parent-verification"
    for suffix, data in ((".stdout", proc.stdout), (".stderr", proc.stderr)):
        with prefix.with_suffix(suffix).open("xb") as out:
            out.write(data)
    with prefix.with_suffix(".json").open("x") as out:
        json.dump(result, out, indent=2, sort_keys=True)
        out.write("\n")
    print("PASS: I187 hashes, formal identities and inherited 23-stage replay",
          result["sealed_reference_replay"]["elapsed_seconds"], "seconds")
