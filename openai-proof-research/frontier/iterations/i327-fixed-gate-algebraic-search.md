# I327 — exact fixed-gate algebraic search beyond unique logarithms

2026-10-13. Research report; **no acceptance nomination and no count change**. Fourteen findings remain accepted toward twenty. All OpenAI premises below are stipulated at revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. I322 remains an unreviewed internal candidate; this report neither depends on its discrete-logarithm theorem nor reads its live audits.

## Outcome and dependency distinction

The full pinned corpus does yield the requested primitive-finding algorithm. The proof uses exact integer factoring **together with the pinned Dirichlet zero-free half-plane**, followed by a completely charged deterministic search for prime-index subgroup escape. It does not solve the multi-witness dyadic-completion problem using the factoring construction alone.

This is a classical analytic consequence followed by exact factoring, not a substantial new exactification mechanism. It is therefore **not an acceptance candidate** under the brief's contribution requirement. The direct polygonal-transform/completion route remains unresolved. A precise obstruction to its symmetric version is recorded below, without asserting impossibility of primitive finding.

## Theorem obtained

Assume the pinned exact-factoring theorem (`thm:main`) and the pinned quasi-Riemann theorem (`thm:main`, every Dirichlet L-function zero-free in Re(s)>7/8). There is a polynomial-time uniform quantum circuit family over

    NOT, CNOT, Toffoli, H, S=diag(1,i), their inverses,
    and their singly controlled versions

which, for every input prime p in binary, outputs a primitive element of F_p^* with probability one. Gate count, qubit count, and worst-case clock are bounded by one polynomial in the binary input length. The algorithm returns a deterministic function of p. It requires neither a supplied generator nor I322.

The classical part has the stronger interface: given the complete factorization of p-1, it deterministically constructs a generator in polynomial bit time. Its analytic input is a zero-location theorem, not an oracle or an uncharged search promise.

### 1. Uniform small escape from any proper subgroup

There is an effectively selectable absolute integer K such that, putting L=ceil(log_2 p) and X=K(L+1)^32, every proper subgroup H of F_p^* omits some integer a with

    1 <= a <= min(p-1, X).

Proof. If p<=X, all representatives 1,...,p-1 are available and the assertion follows from properness. Suppose p>X. Cyclicity supplies a nonprincipal multiplicative character chi modulo p trivial on H. This character is used only in the proof; the algorithm need not construct it, its phases, or any generator defining it. Since p is prime, chi is primitive of conductor p.

Write psi_chi(x)=sum_(n<=x) Lambda(n)chi(n) and psi(x)=sum_(n<=x) Lambda(n). The pinned zero-free theorem and the functional equation, applied also to the conjugate character, put every nontrivial zero of L(s,chi) in 1/8<=Re(s)<=7/8. The same holds for zeta. Classical explicit formulas and effective uniform zero counts give, for x>=2,

    |psi_chi(x)| <= C x^(7/8) (log(px))^2,
    |psi(x)-x| <= C x^(7/8) (log(x+2))^2,                (1)

with absolute effectively bounded C. The derivation and external theorem interfaces are audited in the analysis artifact. In particular there is no character-dependent onset hidden in (1): only the pinned zero locations are new premises; the conductor dependence of the classical formula is logarithmic and uniform.

Choose K large enough that, at x=X, each right-hand error in (1) is at most X/4, uniformly in L>=1. Such a fixed K exists effectively: the ratio is bounded by an absolute constant times (1+log K)^2/K^(1/8), using X=K(L+1)^32. If every a<=X belonged to H, then p>X implies chi(n)=1 for every positive integer n<=X. Consequently psi_chi(X)=psi(X), whereas (1) gives |psi_chi(X)|<=X/4 and psi(X)>=3X/4, a contradiction. This proves the escape bound uniformly over all proper H, independently of its index.

This argument finds an element outside a subgroup, not necessarily a small primitive element. No bound for the least primitive root is asserted.

### 2. Construct and combine primary components

Handle p=2 by returning 1. For odd p, run the stipulated exact finite-gate factoring algorithm on m=p-1. Let its canonical output give

    m = product_(ell in D) ell^e_ell.

For each distinct prime ell in D, search a=1,...,min(p-1,X) in increasing order for the first residue satisfying

    a^(m/ell) != 1 mod p.                              (2)

The kernel of a -> a^(m/ell) is the proper subgroup of size m/ell. The escape lemma guarantees that this finite search succeeds. Each test is binary modular powering, polynomial in L; |D|<=L and X is a fixed polynomial in L. This search is fully included in the clock and reversible-circuit cost.

For its successful a_ell define

    u_ell = a_ell^(m/ell^e_ell) mod p,
    g = product_(ell in D) u_ell mod p.                (3)

Let ord(a_ell)=ell^f d, with ell not dividing d and d dividing m/ell^e_ell. Test (2) implies f=e_ell: otherwise the order would divide m/ell. Raising to m/ell^e_ell eliminates d and is coprime to ell, so ord(u_ell)=ell^e_ell. In an abelian group, the product of elements of pairwise coprime orders has order their product: a power making the product 1, projected by powers annihilating all other components, must be divisible by each component order. Thus ord(g)=m. Equations (2) and (3) also give an efficient final verification.

### 3. Uniform exact circuit and clock

The factorization has certainty and a polynomial worst-case bound by the actual pinned theorem. Every subsequent operation is polynomially clocked deterministic binary arithmetic. The source model's reversible Boolean compilation and retained-record lemma implement it with NOT/CNOT/Toffoli and polynomial overhead. Conditional control and the factorization subroutine's inverse use the allowed singly controlled gates and scratch conjunctions. All branches, including malformed arithmetic labels in reversible implementations, have fixed caps; the mathematical theorem is on prime inputs.

K is a fixed algorithm constant selected from effective classical inequalities, not advice depending on p. Padding the bounded search to its polynomial upper bound gives a uniform generator of the circuit description. One may choose an enormous K; no practical resource bound is claimed. The algorithm performs no quantum attenuation for the primitive search, no odd-modulus QFT, no variable-angle rotation, no postselection, and no retry. Probability-one correctness of factoring followed by deterministic construction proves the theorem.

## What the exact-factoring machinery does and does not supply directly

The actual source was read, not merely its catalogue. In `02-model.tex`, `lem:dyadic` is a retained uniform-bit comparison, and `lem:records` retains computational measurement histories without copying labels before interference. In `03-order-transform.tex`, `lem:transform` implements the **unnormalized flagged matrix** Q^(-1/2)g_0(kx/Q), not an exact QFT. Its phase-register return probability is charged. `04-dyadic-order.tex` equalizes masses per reduced fraction through dyadic majorants and two correction modes. This is possible because residue progressions have efficiently summable bounded-degree pieces. It is not a generic derandomizer for an arbitrary marked set.

In `05-factor-process.tex`, canonical list witnesses are explicit CRT residues, 1 on one prime-power component and -1 on the others; exact orders are the unique canonical order outputs. The auxiliary tree expressly contains no primitive-root witnesses. In `06-exactness.tex`, `lem:completion` requires a particular good output y_0 for its residual guess, and `lem:quarter` uses exactly one canonical valid factor list. Neither theorem automatically supplies such a witness for primitive search.

With m=p-1 factored, the generator verifier is efficient and its count M=phi(m) is known. Uniform b-bit proposals give P=M/2^b. Capping repeats gives a known dyadic high success probability. That does not implement an exact retention coin 1/(4P).

For a two-mode quarter construction, let C be a rounded dyadic global retention and e=1/4-PC/2. If every valid b-bit guess is retained with the same t, its residual mass is M t / 2^(b+1). The required value is

    t=2^(b+1)e/M,                                     (4)

which need not be dyadic. Using the unique-output formula instead gives residual mass M e rather than e. No algebraic cancellation fixes (4) automatically.

More generally, a bounded source-gate circuit with success probability 1/4 and equal flagged probability at all M valid outputs would assign probability 1/(4M) to each flagged label. The independently checked ring argument makes this impossible if M has an odd divisor. This obstruction applies even with finitely many ancillary outcomes or adaptive histories. It excludes symmetric completion, not arbitrary nonuniform output or deterministic primitive finding. Adding auxiliary labels does not evade the obstruction if aggregation still gives equal flagged mass to each generator.

The unproved operation in a completion-only proof is an efficient asymmetric allocation of the residual dyadic mass among valid generators, or an efficient certificate selecting a canonical valid generator before using the residual guess. Exact prefix counts/ranks could support such allocation, but total phi(m) alone supplies neither. The bounded search above supplies a canonical escape witness using an additional pinned analytic theorem; it is not a multi-witness completion device.

## Other routes and supporting progress

The actual family-142 construction charges the numerical auxiliary primes and dense degrees. Its odd-primary construction uses Phi_ell of degree ell-1 and a degree-ell extension. Applying it for a divisor ell of p-1 of exponential size in L is not a polynomial-L algorithm. Its full 2-primary entry and its small-prime entries are useful routine consequences, not a general primitive theorem by themselves. Sparse notation for X^(p-1)-1 does not change the dense-input contract.

The optional exact black-box order route is valid supporting progress under a coherent unique-encoding group-operation interface and a polynomial-bit upper bound N. It can already be obtained by transferring the pinned prescribed order trial and independently auditing the unique-output bridge; a fresh lattice-counting theorem is unnecessary. Details appear in the analysis artifact. It is a routine transfer of source machinery and is not separately nominated. It does not furnish a primitive element in a group for which none is supplied.

## Correctness, contribution, and priority

**Correctness:** the main theorem above has a complete deduction from two stipulated pinned theorems and classical effective explicit-formula/zero-count inputs. It uses no provisional I322 result. The direct multi-witness compiler remains unproved; the symmetric obstruction is rigorous and limited.

**Substantive contribution:** negative. The analytic escape argument is standard in ancestry, and primary-component assembly is elementary. The report closes the requested main test case under the full corpus but does not offer a substantial new acceptance candidate. The gate-ring observation and black-box-order transfer are supporting lemmas, not extra findings.

**Priority:** no new-to-literature claim. Imran's 2022 primitive algorithm is a direct predecessor in a stronger gate model; Imran–Ivanyos explicitly separates QFT-oracle and finite-basis models. Classical analytic escape methods predate this report. Grossman's [2015 primary report](https://eccc.weizmann.ac.il/report/2015/207/) records deterministic primitive search with a supplied factorization under GRH. The present implication replaces the analytic hypothesis with a stronger-than-classically-known stipulated corpus theorem and composes it with the pinned exact factorizer. A bounded literature check cannot establish worldwide priority.

Source locators, authentication, failed retrievals, and independent proof checks are in the four companion deliverables. No full external source body was retained, no live I323/I324 body was read, and no shared index or count was edited.
