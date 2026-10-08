"""Arithmetic falsifiers for unaccepted W010 design claims, not VM execution.

These checks do not test a WordRAM implementation (none exists), the accepted
Lean solvers, or physical performance. They expose obligations in the proposal.
"""
import json


def main():
    width_cases = []
    for k in range(9):
        q = 2**k
        proposed_bits = (q - 1).bit_length()  # ceil(log2(q)), q>0
        assert proposed_bits == k
        assert not q < 2**proposed_bits
        assert q < 2**q.bit_length()
        width_cases.append({"q": q, "proposed_bits": proposed_bits,
                            "q_fits": False, "sufficient_bits": q.bit_length()})

    # Counterexample to using live/peak words as the maximum bump address.
    # This is arithmetic simulation of the proposed non-reusing allocator,
    # not a test of any accepted allocation semantics.
    brk, live, peak = 1, 1, 1
    allocations = []
    for _ in range(3):
        base = brk
        brk += 3
        live += 3
        peak = max(peak, live)
        allocations.append({"base": base, "last_address": brk-1})
        live -= 3
    assert (brk, live, peak) == (10, 1, 4)
    assert peak < 2**3 and allocations[-1]["last_address"] >= 2**3

    # The proposed listed parser checks omit primality. A nonzero discriminant
    # expression over a composite modulus does not establish a finite field.
    p, a, b, gx, gy, element = 4, 0, 1, 0, 1, 3
    assert p != 0 and 0 <= gx < p and 0 <= gy < p
    assert (gy*gy-gx**3-a*gx-b) % p == 0
    discriminant = (4*a**3+27*b*b) % p
    assert discriminant != 0
    fermat_value = pow(element, p-2, p)
    product = element*fermat_value % p
    assert product != 1

    # q*G=0 certifies a multiple of the order, not exact order by itself.
    # This is the abstract additive group Z/7, not a new EC experiment.
    actual_order, claimed_order = 7, 14
    assert claimed_order % actual_order == 0
    assert actual_order != claimed_order

    print(json.dumps({
        "scope": "arithmetic counterexamples to unaccepted W010 proposal; no VM or performance result",
        "q_word_width": width_cases,
        "nonreusing_addresses": {"word_bits": 3, "initial_words": 1,
            "allocations": allocations, "peak_live_words": peak,
            "terminal_live_words": live, "terminal_brk": brk},
        "missing_prime_hypothesis": {"p": p, "a": a, "b": b,
            "generator": [gx, gy], "discriminant_factor": discriminant,
            "element": element, "fermat_value": fermat_value,
            "element_times_fermat_mod_p": product},
        "multiple_not_exact_order": {"actual_order": actual_order,
            "claimed_order": claimed_order, "claimed_multiple_is_zero": True}
    }, indent=2))


if __name__ == "__main__":
    main()
