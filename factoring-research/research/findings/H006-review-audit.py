"""Independent H006 review checks; writes only its uniquely named review output."""
import hashlib
import json
import math
import time
from collections import Counter
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "research/experiments/H006/certified_subtree.py"
PROTOCOL = ROOT / "research/hypotheses/H006.md"
RESULT = SOURCE.with_name("result.json")
OUT = Path(__file__).with_name("H006-review-audit.json")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def independent_bounds(j, t, left, right):
    if left == right:
        return left**j, left**j
    tangent_left = j * left ** (j - 1) * t - (j - 1) * left**j
    tangent_right = j * right ** (j - 1) * t - (j - 1) * right**j
    chord = Fraction(right**j - left**j, right - left) * (t - left) + left**j
    return max(left**j, tangent_left, tangent_right), min(right**j, math.floor(chord))


def coefficients(n, s, a):
    radix, modulus = 2**s, 2 ** (6 * s)
    inv = pow(a, -1, modulus)
    out = [n * inv % modulus]
    for _ in range(5):
        out.append(-radix * inv * out[-1] % modulus)
    return out


def independent_check(n, k, s, a, left, right, qlo, qhi, witness):
    t, q, z = witness
    radix, modulus = 2**s, 2**k
    assert k == 6 * s and n % 2 == 1 and a % 2 == 1
    assert len(z) == 6 and z[0] == 1 and z[1] == t
    assert left <= t <= right and qlo <= q <= qhi
    assert all(isinstance(v, int) for v in [t, q] + z)
    for j in range(2, 6):
        low, high = independent_bounds(j, t, left, right)
        assert low <= z[j] <= high
    c = coefficients(n, s, a)
    assert (sum(x * y for x, y in zip(c, z)) - q) % modulus == 0
    assert sum(c[j] * t**j for j in range(6)) % modulus == n * pow(a + radix * t, -1, modulus) % modulus
    # Every actual ancestor, including its original power-box constraints.
    ancestor_left, ancestor_right = radix**2 // 2, radix**2 - 1
    while True:
        for j in range(2, 6):
            low, high = independent_bounds(j, t, ancestor_left, ancestor_right)
            assert low <= z[j] <= high
        if (ancestor_left, ancestor_right) == (left, right):
            break
        mid = (ancestor_left + ancestor_right) // 2
        if right <= mid:
            ancestor_right = mid
        else:
            assert left > mid
            ancestor_left = mid + 1


def lifted_witness(n, s, a, left, right, t, z2):
    r, m = 2**s, 2 ** (3 * s)
    c = coefficients(n, s, a)
    z = [1, t, z2]
    q = sum(x * y for x, y in zip(c, z)) % m
    if q < m // 2:
        return None
    for j in range(3, 6):
        partial = sum(x * y for x, y in zip(c, z))
        assert (q - partial) % r**j == 0
        residue = (q - partial) // r**j * pow(c[j] // r**j, -1, r) % r
        low, high = independent_bounds(j, t, left, right)
        value = low + (residue - low) % r
        assert value <= high
        z.append(value)
    return t, q, z


def main():
    if OUT.exists():
        raise SystemExit("Refusing to overwrite review evidence")
    start = time.monotonic()
    frozen = json.loads(RESULT.read_text())
    hashes = {"source": digest(SOURCE), "protocol": digest(PROTOCOL), "result": digest(RESULT)}
    assert hashes["source"] == frozen["source_sha256"]
    assert hashes["protocol"] == frozen["protocol_sha256"]
    namespace = {"__name__": "H006_independent_review", "__file__": str(SOURCE)}
    exec(compile(SOURCE.read_text(), str(SOURCE), "exec"), namespace)
    original_certificate = namespace["certificate"]
    checked = Counter()
    examples = {}

    def audited_certificate(n, k, s, a, left, right, c, qlo, qhi, counts):
        witness = original_certificate(n, k, s, a, left, right, c, qlo, qhi, counts)
        if witness is not None:
            independent_check(n, k, s, a, left, right, qlo, qhi, witness)
            checked[k] += 1
            if k not in examples and (a + 2**s * witness[0]) * witness[1] != n:
                examples[k] = {"n": n, "K": k, "a": a, "left": left, "right": right,
                               "t": witness[0], "q": witness[1], "z": witness[2]}
        return witness

    namespace["certificate"] = audited_certificate
    replays = []
    bottom_counts = []
    inverse_cache = {}
    for row in frozen["rows"]:
        n, k, s = row["n"], row["K"], row["s"]
        replay = namespace["probe"](n, k, time.monotonic() + 60)
        for key in ("status", "counts", "full_unpruned_nodes", "certified_subtree_node_fraction"):
            assert replay[key] == row[key], (n, key)
        replays.append({"n": n, "K": k, "all_non_timing_fields_match": True})
        r, m = 2**s, 2 ** (3 * s)
        if s not in inverse_cache:
            inverse_cache[s] = [(p, pow(p, -1, m)) for p in range(m // 2 + 1, m, 2)
                                if (p // r) % 4 in (1, 2)]
        qualifying, nodes, factor_positions = 0, set(), 0
        for p, inv in inverse_cache[s]:
            q = n * inv % m
            if q >= m // 2:
                qualifying += 1
                nodes.add((p % r, (p // r) // 4))
                factor_positions += p * q == n
        bottom_counts.append({"n": n, "K": k, "eligible_positions": len(inverse_cache[s]),
                              "qualifying_positions": qualifying, "certified_bottom_nodes": len(nodes),
                              "exact_factor_positions": factor_positions,
                              "visited_lower_bound_three_times_bottom": 3 * len(nodes),
                              "full_tree_fraction_lower_bound": Fraction(3 * len(nodes), row["full_unpruned_nodes"]).__str__()})

    all_residue_counts = []
    for s in (2, 3, 4):
        m = 2 ** (3 * s)
        inverses = [inv for _, inv in inverse_cache[s]]
        values = [sum((n * inv % m) >= m // 2 for inv in inverses) for n in range(1, m, 2)]
        all_residue_counts.append({"s": s, "N_residues_checked": m // 2, "minimum": min(values),
                                   "maximum": max(values), "mean": Fraction(sum(values), len(values)).__str__(),
                                   "main_term_M_over_16": m // 16})

    counterexample = None
    for n in (1763, 1591, 2021, 1517):
        for a in (1, 3):
            for left in (8, 12):
                right = left + 3
                restricted = [n * pow(a + 4 * t, -1, 64) % 64 for t in (left + 1, left + 2)]
                if any(q >= 32 for q in restricted):
                    continue
                for t in (left + 1, left + 2):
                    low, high = independent_bounds(2, t, left, right)
                    for z2 in range(low, high + 1):
                        witness = lifted_witness(n, 2, a, left, right, t, z2)
                        if witness is not None:
                            independent_check(n, 12, 2, a, left, right, 32, 63, witness)
                            counterexample = {"n": n, "K": 12, "a": a, "left": left, "right": right,
                                              "restricted_inverse_residues": restricted, "t": t,
                                              "q": witness[1], "z": witness[2], "coefficients": coefficients(n, 2, a)}
                            break
                    if counterexample:
                        break
                if counterexample:
                    break
            if counterexample:
                break
        if counterexample:
            break
    assert counterexample is not None

    c = coefficients(2021, 2, 3)
    assert original_certificate(2021, 12, 2, 3, 10, 11, c, 32, 63, Counter()) is None
    missed_true = {"n": 2021, "K": 12, "a": 3, "interval": [10, 11],
                  "exact_pairs": [[43, 47], [47, 43]], "certificate_result": None}

    # Exhaustive integer support checks for the root-counting lemma used in the proof.
    square_root_checks = []
    for h in range(3, 13):
        modulus = 2**h
        histogram = Counter(x * x % modulus for x in range(1, modulus, 2))
        assert max(histogram.values()) == 4
        square_root_checks.append({"exponent": h, "maximum_roots": 4})

    # Narrower intervals, including three integers, directly check the curvature margin.
    margins = []
    for s in range(2, 8):
        r = 2**s
        minimum = None
        for left in (r*r//2, r*r-9):
            for span in range(2, 9):
                for t in range(left + 1, left + span):
                    for j in range(3, 6):
                        low, high = independent_bounds(j, t, left, left + span)
                        curvature = j * (j-1) * left ** (j-2)
                        assert high - low >= curvature >= r
                        minimum = high-low if minimum is None else min(minimum, high-low)
        margins.append({"s": s, "minimum_tested_upper_minus_lower": minimum})

    assert hashes == {"source": digest(SOURCE), "protocol": digest(PROTOCOL), "result": digest(RESULT)}
    output = {"status": "all_checks_passed", "frozen_hashes_unchanged": hashes,
              "audit_source_sha256": digest(Path(__file__)), "replays": replays,
              "independently_checked_witnesses_by_K": dict(checked), "witness_examples": examples,
              "bottom_node_counts": bottom_counts, "all_odd_N_residue_checks": all_residue_counts,
              "unrestricted_z2_counterexample": counterexample, "uncertified_true_node": missed_true,
              "square_root_count_checks": square_root_checks, "width_margin_checks": margins,
              "seconds": time.monotonic() - start,
              "limits": ["Enumeration is diagnostic exponential work, not a factoring algorithm.",
                         "Finite checks support, but do not replace, the report's symbolic proof."]}
    OUT.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({"status": output["status"], "checked_witnesses": sum(checked.values()),
                      "seconds": output["seconds"], "counterexample": counterexample,
                      "all_odd_N_residue_checks": all_residue_counts}))


if __name__ == "__main__":
    main()
