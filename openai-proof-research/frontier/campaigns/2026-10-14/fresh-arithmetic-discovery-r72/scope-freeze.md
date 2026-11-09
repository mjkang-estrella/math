# T179A — circulant Butson Hadamard matrices over the fourth and third roots of unity

Frozen UTC: 2026-10-19 (fresh-arithmetic-discovery-r72, Opus 5.5 fallback child).
Status at freeze: candidate statement with a worked proof sketch; no gate, nominee or count claim.

## Frozen full target

Write ω = e^{2πi/3}. A matrix H of order n is *circulant* if H_{jk} = h_{k−j mod n}
for some first row (h_0,…,h_{n−1}). It is a *complex Hadamard matrix* if
H H^* = n I_n, where H^* is the conjugate transpose.

**T179A.**

(a) For every positive integer n with 4 ∤ n, there is a circulant complex Hadamard
matrix of order n with all entries in {1, i, −1, −i} if and only if n ∈ {1, 2}.

(b) For every positive integer n with 9 ∤ n, there is a circulant complex Hadamard
matrix of order n with all entries in {1, ω, ω²} if and only if n ∈ {1, 3}.

Equivalent sequence form: a perfect sequence (all nontrivial periodic
autocorrelations zero) over the fourth roots of unity of length n ≢ 0 (mod 4)
exists only for n ∈ {1,2}; over the cube roots of unity of length n ≢ 0 (mod 9)
only for n ∈ {1,3}.

Quantifiers and strength: every such n, every first row, no restriction on
the prime factorization of n (number of prime factors, prime powers, primes
≡ 1 or 3 mod 4, self-conjugacy of any prime modulo any integer, size of n),
no symmetry, real-part, Hermitian or other structural assumption on the
matrix, and both existence directions. The new content is the nonexistence
for n = 2m (m odd, m > 1) in (a) and for n = 3m (3 ∤ m, m > 1) in (b); the
remaining residue classes follow from elementary vanishing-sum arguments,
which are part of the frozen statement and will be proved.

Not included and not claimed: any order divisible by 4 in (a) or by 9 in
(b); Mow's or Turyn's full conjecture (orders ≤ 16, resp. ≤ 9); any other
alphabet; group-developed (non-circulant) matrices over non-cyclic groups;
real Menon–Hadamard difference sets in C_2 × C_2 × C_{u²} (a separate
observation recorded by fresh-structural-discovery-r60, not part of T179A).

## Source dependency (stipulated true)

Family 179, `preprints/The-circulant-Hadamard-conjecture-September-23-2026`,
pinned commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, files
`build/sections/{introduction,local,reduction,products,contradiction}.tex`:
Lemma `lem:local-ring`, Lemma `lem:comparison`, Lemma `lem:torsion`,
Proposition `prop:alternating` (and its proof, which will be re-run with the
group C_m and scalar m in place of C_{u²} and u², and with coefficient ring
Z[ω] in place of Z[i] for part (b)), and Lemma `lem:first-order`. The source
proves only the real ±1 alphabet; it does not treat {±1, ±i} or {1, ω, ω²}.

## Intended new operations (to be proved, not assumed)

1. Automatic normalization: for the alphabet μ_4 with a cyclic factor C_2, and
   for μ_3 with a cyclic factor C_3, the partial evaluations of the first row
   are divisible by 1+i, resp. 1−ω, giving elements of the odd (resp.
   prime-to-3) group ring with exact scalar norm m.
2. Re-running the alternating-product torsion proposition for C_m, scalar m,
   including the prime 2 when m is even in part (b).
3. Alphabet-specific first-order identities at a prime above 2 (resp. 3) that
   isolate the all-ones element J, giving the contradiction.

## Chronology (honest)

This freeze follows an extended screen (see `screening.md`) during which the
proof idea for (a) and (b) was found and checked informally. The freeze does
not pretend to precede that idea. It does precede the written proof, the
exact identity checks, the hostile controls and the primary comparison. A
more ambitious target (the full quaternary or ternary Mow conjecture) was
considered and not frozen because its central 2-adic/3-adic difficulty is
unpaid and no plan for it exists; see `barriers.md` once written.

Contribution risk, stated before any gate: the alternating-product
machinery is paid by the source and reused nearly verbatim. The new steps
are short. An independent contribution review may classify T179A as
TECHNICAL; this freeze does not presume otherwise.

Original prose: Myeongjin Kang, CC BY 4.0.
