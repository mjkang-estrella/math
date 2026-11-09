# H011 — exact affine reporter retained, exponent target rejected

Date: 2026-10-08. Verified factoring complexity improvement: **NONE**.

The coordinator accepts the restricted negative result in the
[construction and audit](H011-coupled-inverse.md). For R=2^s, M=R^5 and odd N,
the exact inverse graph has second difference

    f_a(x+2)-2*f_a(x+1)+f_a(x)
      = 2*N*D² / ((a+D*x)(a+D*(x+1))(a+D*(x+2))) mod M.

All denominator factors are units. Its valuation is exactly 2r+1 until
vanishing, where D=2^r. Thus an affine formula valid at every integer suffix
starts precisely at r=floor(5s/2). The secant slope, rather than the formal
derivative, handles the odd-exponent endpoint correctly.

At that depth the construction reduces each class to an affine congruence
in a box. The stated difference of two signed floor sums counts its points
exactly. The coordinator checked the indicator identity and Euclidean
horizontal-level recurrence. Positive-count bisection is output-sensitive
within one class, but it must first visit every nonempty class.

In the full balanced box, all D/2 odd classes have nonempty coordinate
intervals, for every odd N and s>=2. Therefore this implementation pays
Theta(R^(5/2)) class visits. Its conservative total bit cost is
`O(R^(5/2)*s³ + Z*s⁴)`, with `Z=R^(1+o(1))` only an output-size bound.
This misses the required exponent below 6/5 by a wide margin. Few or zero
outputs do not eliminate empty-query work. Shallower whole-graph affine
segments have at most two consecutive points; this closes that particular
repair, not general inverse reporting or early-stop factoring.

All 61 frozen correctness cases passed, including 208,845 signed floor-sum
checks and 11,880 second-difference checks. The 48 reporting cases emitted
16 modular pairs, all in full boxes. There were no actual factor pairs, and
the clipped/singleton positive-output cases were not exercised. The run is
an arithmetic correctness audit, not a successful factoring benchmark.
All ten artifact hashes in the manifest were rechecked and match.

**Close this explicit affine-class construction as a speedup.** Reopen only
with a transition that processes or excludes groups of exact inverse branches
without individually constructing every class's inverse and slope. Faster
per-class arithmetic cannot remove the dominant class count. The balanced-box
scope also requires a separate all-input reduction before a general claim.
The proof is informal coordinator-reviewed mathematics; no new Lean theorem
or independent second-review promotion is claimed.
