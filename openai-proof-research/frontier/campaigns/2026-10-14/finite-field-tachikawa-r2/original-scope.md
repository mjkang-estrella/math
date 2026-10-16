# Frozen target FT2: a symmetric homological counterexample over the prime field

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Third-party rights retained privately.

There exist positive integers a,m, an associative unital F_2-algebra A with
F_2-dimension a, and a unital left A-module M with F_2-dimension m, such that:

1. A is symmetric: A is isomorphic to Hom_{F_2}(A,F_2) as an A-A-bimodule.
2. M is not projective.
3. For EVERY integer i>=1, Ext_A^i(M,M)=0.

No prescribed dimension, number of simples, radical length, presentation,
complexity, syzygy bound, commutativity, or relation to a particular source
example is imposed. The field is exactly F_2. A finite range of vanishing,
a growing family depending on that range, an infinite-dimensional algebra,
a module of infinite dimension, a rational-function field, or its algebraic
closure is not this assertion. A proof of the negation must show that EVERY
finite-dimensional symmetric F_2-algebra and EVERY finite-dimensional
nonprojective module have a positive self-extension in some degree.

Source family: 199, at openai/math commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Its main symmetric example is over
F_2(q,H_1,H_2) with algebraically independent parameters; extension of that
field is allowed, specialization to F_2 is not supplied.

The concrete unpaid operation selected BEFORE sustained proof work is to
replace the source's infinite-order parameter separation by finite-field
homological data while preserving nonprojectivity and ALL positive-degree
vanishing. Finite-field base descent of an arbitrary all-degree example
would suffice but is not assumed. A different construction is allowed.

Primary operation screen before freezing: Schulz (1995), Example 7, uses a
non-root-of-unity syzygy parameter and has nonzero Ext^1. Erdmann (2017),
Theorem 1.1, classifies eventual-vanishing examples for the stated weakly
symmetric radical-cube-zero class using non-root-of-unity parameters.
Enomoto--Marczinzik (2026), Theorem 1.1 and the beginning of Sections 2--3,
work over a FIXED artinian coefficient ring; their trivial-extension
implications do not lower the field. The actual pinned companion main
statements only extend the original rational-function field. None of these
read operations performs the selected finite-field replacement.

This is a research assertion, not an established theorem or a new-to-world
conjecture claim. Its scope will not be narrowed to claim success. No
independent mathematical or contribution PASS, manuscript, Lean package,
acceptance, or count increase is authorized by this freeze.
