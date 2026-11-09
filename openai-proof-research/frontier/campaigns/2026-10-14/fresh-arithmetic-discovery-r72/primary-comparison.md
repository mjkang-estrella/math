# Primary comparison and contribution limits for T179A

Bounded comparison. Unread bodies are listed as such and are not treated as
clearance. Exact identities of retained private copies are in
`primary-identities.json`.

## What was previously known (as far as actually read)

**Fourth roots (part (a)).** The conjecture that a perfect sequence over
{±1, ±i} (equivalently a circulant complex Hadamard matrix with these entries)
has length at most 16 is due to Turyn. Bright–Kotsireas–Ganesh
(arXiv:1905.00267v2, §VI, read) state: "In the case n = 4, the conjecture
states that the longest perfect sequence over {±1, ±i} has length 16 and Turyn
[Complex Hadamard matrices, 1970] showed that the length of any longer perfect
sequence cannot be of the form 2p^k for any prime p and integer k", and that
"the longest perfect {±1, ±i}-sequence of length 2^t is of length sixteen".
Blake (arXiv:2603.13914v1, March 2026, abstract and introduction read) states
that Mow's conjecture (no perfect n-phase sequence longer than n²) remains open.
Arasu–de Launey–Ma, *On circulant complex Hadamard matrices*, Des. Codes
Cryptogr. 25 (2002) 123–142: only the abstract as reported by search engines
was seen (equivalence with relative difference sets in C_4 × C_n with a
forbidden subgroup of order two; nonexistence "for many orders"). Its theorems
were **not read**. Parraud, *On the non-existence of (almost-)perfect quaternary
sequences*, AAECC 2001 (LNCS): title only; **not read**.
Hiranandani–Schlenker (Europ. J. Combin. 2015, arXiv:1311.5390v4, §1, §5 and
Table 1 read) record, for entries in 4th roots, a generalized Turyn obstruction
at n = 6, 14 and a computational count 0 at n = 10.

New orders covered by (a): n = 2m with m odd, m a sum of two squares (else n is
not a norm from ℤ[i] and nonexistence is trivial), m not a prime power, e.g.
n = 90, 130, 170, 290, 370, … . Whether ALM02 or Parraud already covers all or
some of these is **not determined**.

**Cube roots (part (b)).** Ma–Ng, *On non-existence of perfect and nearly
perfect sequences*, IJICoT 1 (2009) — publisher abstract read in full: no
p-ary perfect sequences (p odd prime) of length p^s (s ≥ 3), 2p^s (s ≥ 1),
pq (q > p prime), and no ternary perfect sequences of length 3q_1q_2 for
primes 3 < q_1 < q_2; further results under "self-conjugate" conditions; tables
for n ≤ 50. Body **not read**. Lv (arXiv:1612.05682v1, §1 list read) summarizes
Ma–Ng's self-conjugacy result (types [p, q^l n′], q self-conjugate w.r.t. p, l
odd) and Liu–Feng's conditional results for p ≡ 3 (mod 4).
Hiranandani–Schlenker Table 1: entries in cube roots exist at n = 3, 9; count 0
at n = 12; generalized Turyn obstruction at n = 6, 15.

New orders covered by (b), relative to the abstract-level list above: every
n = 3m with 3 ∤ m and m not of the forms 2, a prime q > 3, or q_1q_2
(primes 3 < q_1 < q_2), and with n a norm from ℤ[ω] (otherwise trivial), e.g.
n = 12, 48, 84, 147, 228, 588, … (but not 273 = 3·7·13, which is a Ma–Ng 3q_1q_2 case). Coverage by Ma–Ng's unread self-conjugate
section or tables (n ≤ 50, so n = 12 and 48) is **not determined**; 12 and 48
may well be in those tables.

## Operation-level comparison with the stipulated source

| Step | Source 179 | T179A |
|---|---|---|
| Group-ring translation, hh^* = n | real ±1, C_{4u²} | μ_4 on C_{2m}; μ_3 on C_{3m} |
| Order restriction | `prop:order` (2-adic descent, n = 4u², u odd) | Lemma 1.1 (vanishing sums), elementary |
| Normalization | divide partial evaluations at Z = ±1, i by 2 | divide by 1+i (two evaluations) or by 1−ω (three evaluations) |
| Torsion of alternating products | `prop:alternating`, P = C_{u²}, scalar u², ℤ[i] | re-run for P = C_m, scalar m, ℤ[i] or ℤ[ω], including p = 2 |
| Contradiction | two ratio families at a prime over 2, L_r + L_w ≡ J/c via H_2 + iH_3 ≡ (1+i)J | (a) one ratio family, d − c = −(1−i)H_1, H_1 ≡ J mod (1+i); (b) two families at a prime over 3, M + M′ = ω²(H_1 + H_2) ≡ −J mod λ |

Every lemma of the source is used under its stated hypotheses; the new steps
are the three rows marked with alphabet-specific identities and the observation
(`barriers.md` §1) that automatic normalization holds exactly in these cases
among the alphabets checked.

## Author's expectation (not a gate)

The theorem is a complete, new-to-this-project full statement settling
infinitely many orders in two long-standing classification problems. Its proof,
however, is the source's architecture with alphabet-specific parameters and
short identities. Under this campaign's standard that a full theorem whose proof
is a literal parameter substitution in paid operations is TECHNICAL, the author
expects an independent contribution review may well return TECHNICAL. Arguments
the other way: the source treats only the real alphabet; the cube-root case
uses a different prime (3), a different coefficient ring and a different
first-order combination; and §§2–3 of `barriers.md` show the transfer is not
automatic for other alphabets or larger q-parts. No rating is claimed here.

## Literature not consulted

Turyn 1970 (body), ALM02 (body), Parraud 2001, Ma–Ng 2009 (body and tables),
Liu–Feng, Schmidt's field-descent papers, Leung–Schmidt, and Banica–Nechita–
Schlenker's generalized Turyn obstruction were not read. Priority is therefore
not established.

Original prose: Myeongjin Kang, CC BY 4.0.
