"""One-shot evaluation of Schoof's displayed finite class-number formula."""

import json
import math
from pathlib import Path


def legendre(a, p):
    a %= p
    if a == 0:
        return 0
    t = pow(a, (p - 1) // 2, p)
    return -1 if t == p - 1 else t


def chi_minus23(n):
    m = n
    while m % 2 == 0:
        m //= 2
    if m % 23 == 0:
        return 0
    return legendre(m, 23)


def chi_minus115(n):
    v = 0
    m = n
    while m % 2 == 0:
        m //= 2
        v += 1
    if m % 5 == 0 or m % 23 == 0:
        return 0
    sign = -1 if v % 2 else 1
    return sign * legendre(m, 5) * legendre(m, 23)


def evaluate(delta, chi, expected_terms):
    modulus = abs(delta)
    terms = []
    total = 0
    for x in range(1, modulus // 2 + 1):
        if math.gcd(x, modulus) != 1:
            continue
        value = chi(x)
        terms.append([x, value])
        total += value
    two = chi(2)
    denominator = 2 - two
    if denominator == 0 or total % denominator != 0:
        raise SystemExit(f"non-integral class number for {delta}")
    if len(terms) != expected_terms:
        raise SystemExit(f"term count {len(terms)} != {expected_terms} for {delta}")
    return {
        "discriminant": delta,
        "chi_of_2": two,
        "denominator": denominator,
        "sum": total,
        "class_number": total // denominator,
        "term_count": len(terms),
        "terms": terms,
    }


def nearest_integers(height):
    root = 0
    while (root + 1) * (root + 1) <= height:
        root += 1
    low_gap = height - root * root
    high_gap = (root + 1) * (root + 1) - height
    if low_gap < high_gap:
        return [root]
    if high_gap < low_gap:
        return [root + 1]
    return [root, root + 1]


def main():
    if chi_minus23(1) != 1 or chi_minus23(5) != -1 or chi_minus23(2) != 1:
        raise SystemExit("character check failed for -23")
    if chi_minus115(1) != 1 or chi_minus115(2) != -1 or chi_minus115(3) != -1:
        raise SystemExit("character check failed for -115")
    first = evaluate(-23, chi_minus23, 11)
    if first["class_number"] != 3:
        raise SystemExit("discriminant -23 did not return 3")
    second = evaluate(-115, chi_minus115, 44)
    height = first["class_number"] * second["class_number"]
    nearest = nearest_integers(height)
    prime_order = second["class_number"] in {2, 3, 5, 7, 11, 13, 17, 19, 23}
    rows = []
    for guess in nearest:
        divides = height % guess == 0 if guess else False
        annihilates = (
            guess % first["class_number"] == 0
            and guess % second["class_number"] == 0
        )
        rows.append(
            {
                "integer": guess,
                "divides_product": divides,
                "divisible_by_both_class_numbers": annihilates,
            }
        )
    result = {
        "formula": "Schoof printed p.245 maximal-order finite sum",
        "h_minus_23": first,
        "h_minus_115": second,
        "product": height,
        "prime_order_groups": prime_order and first["class_number"] == 3,
        "nearest_to_geometric_mean": rows,
        "product_annihilates_both": True,
    }
    out = Path(__file__).with_name("class-number-certificate-results.json")
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: result[k] for k in ("product", "prime_order_groups", "nearest_to_geometric_mean")}))
    print(f"h(-115)={second['class_number']}")


if __name__ == "__main__":
    main()
