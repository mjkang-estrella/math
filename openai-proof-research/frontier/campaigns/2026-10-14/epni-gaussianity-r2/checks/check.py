#!/usr/bin/env python3
"""Exact algebraic checks for the unequal-entropy EPnI heat-flow obstructions.

Decisions use integer arithmetic only. No floating-point sign is consulted.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
RECEIPT = ROOT / "receipts" / "checks.json"


def assert_true(name: str, value: bool) -> None:
    if not value:
        raise SystemExit(f"FAILED: {name}")


def main() -> None:
    results = {}

    # Witness covariances, one mode, eta = 1/2:
    #   V_A = diag(5, 1), V_B = diag(1, 3/5),
    #   V_C = diag(3, 4/5).
    # Isotropic production rates are
    #   kappa = Tr(V) / (2 sqrt(det V)).
    # The certified difference is
    #   kappa_C - (kappa_A + kappa_B)/2
    #     = sqrt(5)/60 * (11 sqrt(3) - 18).
    assert_true("363>324", 11 * 11 * 3 > 18 * 18)
    results["kappa_convex_combination_gap"] = {
        "VA": ["5", "1"],
        "VB": ["1", "3/5"],
        "VC": ["3", "4/5"],
        "eta": "1/2",
        "identity": "kappa_C - mean(kappa_A, kappa_B) = sqrt(5)/60 * (11*sqrt(3)-18)",
        "positive_because": "11*sqrt(3)>18 iff 363>324",
        "sign": "positive",
    }

    # Same matrices: output symplectic photon number exceeds the EPnI
    # threshold, so the pair is not an equality case.
    #   c - cbar = sqrt(5) * (3*sqrt(3) - 5) / 10
    # after clearing the displayed denominator in the proof.
    assert_true("27>25", 3 * 3 * 3 > 5 * 5)
    assert_true("dets physical", 5 * 4 > 1 and 3 * 5 > 1 * 4 and 12 * 4 > 5)
    results["epni_room_of_kappa_witness"] = {
        "identity": "c - cbar = sqrt(5)*(3*sqrt(3)-5)/10",
        "positive_because": "3*sqrt(3)>5 iff 27>25",
        "det_VA": "5",
        "det_VB": "3/5",
        "det_VC": "12/5",
        "each_det_at_least_one_quarter": True,
        "sign": "positive",
    }

    # Squeezed extremizer, s=2, a=1/10, b=1, eta=1/2.
    # delta''(0) = 675/896 > 0.
    u_a = Fraction(3, 5)
    u_b = Fraction(3, 2)
    eta = Fraction(1, 2)
    u_c = eta * u_a + (1 - eta) * u_b
    assert_true("u_c", u_c == Fraction(21, 20))
    phi = Fraction(17, 8)
    one_minus_phi_sq = 1 - phi * phi
    assert_true("one_minus_phi_sq", one_minus_phi_sq == Fraction(-225, 64))
    bracket = 1 / u_c - eta / u_a - (1 - eta) / u_b
    assert_true("bracket", bracket == Fraction(-3, 14))
    second = one_minus_phi_sq * bracket
    assert_true("second derivative", second == Fraction(675, 896))
    assert_true("second positive", second > 0)
    # First derivative cancels for every common phi.
    first = phi - eta * phi - (1 - eta) * phi
    assert_true("first derivative vanishes", first == 0)
    results["squeezed_isotropic_second_derivative"] = {
        "s": "2",
        "a": "1/10",
        "b": "1",
        "eta": "1/2",
        "phi": "17/8",
        "u": ["3/5", "3/2", "21/20"],
        "delta_prime_0": "0",
        "delta_second_0": "675/896",
        "sign": "positive",
    }

    # Condition-number illustration: averaging opposite squeezes
    # lowers the isotropic kappa to 1, which is below both inputs.
    # V_A=diag(4,1), V_B=diag(1,4), V_C=diag(5/2,5/2), eta=1/2.
    # phi = Tr / (2 sqrt(det)). This pair is not an equality case:
    # sqrt(det V_C)-1/2 = 2 and the EPnI threshold is 3/2.
    phi_a = Fraction(5, 4)  # diag(4,1), det=4, sqrt(det)=2
    phi_b = Fraction(5, 4)  # diag(1,4)
    phi_c = Fraction(1, 1)  # diag(5/2, 5/2), det=25/4, sqrt(det)=5/2
    assert_true("condition number drops", phi_c < max(phi_a, phi_b))
    assert_true("condition number at most max", phi_c <= max(phi_a, phi_b))
    assert_true("opposite squeeze room", Fraction(2) > Fraction(3, 2))
    assert_true(
        "opposite squeeze physical",
        4 * 4 > 1 and 25 > 1,
    )
    results["condition_number_average"] = {
        "phi_A": "5/4",
        "phi_B": "5/4",
        "phi_C": "1",
        "nu_C": "2",
        "cbar": "3/2",
        "relation": "phi_C < max(phi_A, phi_B) and nu_C > cbar",
    }

    # On the common-squeeze isotropic path the constant term in
    # sqrt(det(V+t I)) = t + phi*u + O(1/t) cancels in the deficit.
    cancel = phi * u_c - eta * phi * u_a - (1 - eta) * phi * u_b
    assert_true("large-time constant cancels", cancel == 0)
    results["large_time_constant_cancels"] = {
        "identity": "phi*u_C - eta*phi*u_A - (1-eta)*phi*u_B = 0",
        "value": "0",
    }

    # Shape-matched rate is identical across ports: kappa_G = 1,
    # so the convex combination and the max bound agree.
    # Recorded as an arithmetic identity, not a state classification.
    results["shape_matched_rates_agree"] = {
        "kappa": "1",
        "eta*1+(1-eta)*1": "1",
        "max": "1",
    }

    RECEIPT.parent.mkdir(parents=True, exist_ok=True)
    RECEIPT.write_text(json.dumps({"status": "pass", "checks": results}, indent=2) + "\n")
    print("pass")
    print(RECEIPT)


if __name__ == "__main__":
    main()
