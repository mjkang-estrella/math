# I327 — independent deductions and technical audit

2026-10-13. Symbolic proof checks only; no empirical or numerical scan was executed. No acceptance recommendation. The principal theorem and exact dependencies are in the iteration artifact.

## Uniform character-sum estimate used for the charged search

Let chi be nonprincipal modulo a prime p. It is primitive of conductor p. The pinned `The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex`, `thm:main`, supplies Re(rho)<=7/8 for every nontrivial zero. Applying the functional equation to chi and conjugate(chi) supplies Re(rho)>=1/8. This lower bound is essential to control low zeros without a character-dependent denominator.

The classical truncated explicit formula at height T=x, with its standard O(log(px)^2) remainder (enlarging by endpoint terms if necessary), is

    psi_chi(x) = -sum_(|Im rho|<=x) x^rho/rho
                  + O(log(px)^2),    x>=2.

This is the interface in Kowalski, Theorem C.5.6; the smooth contour explanation is also inspected there. The formula is used only for primitive nonprincipal characters. The zeta version has main term x. These are classical analytic inputs, not quantum primitives or new stipulated premises.

Uniform total zero counting gives N_chi(T)<=C(T+1)log(p(T+2)), with effective absolute C. Bennett–Martin–O'Bryant–Rechnitzer, Theorem 1.1 and Corollary 1.2, provide an explicit primary source for this conductor dependence. Their T>=5/7 bound includes the entire low-height range by counting at T=1. Standard zeta counting supplies the conductor-one counterpart.

For |Im rho|<=1, |rho|>=1/8, so their reciprocal sum is O(log(p+2)). For each dyadic annulus 2^j<|Im rho|<=2^(j+1), bound 1/|rho| by 2^(-j) and use the total count at 2^(j+1). This contributes O(log p+j+1). Summing O(log(x+2)) annuli proves

    sum_(|Im rho|<=x) 1/|rho| <= C log(px)^2.

The zero-location premise now gives |psi_chi(x)|<=C x^(7/8)log(px)^2. Identical reasoning for zeta gives |psi(x)-x|<=C x^(7/8)log(x+2)^2. Possible endpoint adjustments are absorbed in these bounds. Constants in the formula and counts are effective; the proof uses no modulus-dependent asymptotic onset from the proof of the pinned zero-free theorem.

For X=K(L+1)^32, L=ceil(log_2 p),

    log(pX) <= c(1+log K)(L+1),
    X^(-1/8)log(pX)^2
      <= c'(1+log K)^2 K^(-1/8)(L+1)^(-2).

Choose a single integer K making the last expression times the effective error constant <1/4. This selection is effective and independent of p and subgroup index. The procedure can therefore be padded to a fixed polynomial clock. This establishes the exact escape lemma, including when an odd prime factor of p-1 has exponentially large numerical value. No factorization of a large-degree polynomial is involved.

Algorithmic character construction is unnecessary: an arbitrary generator in the cyclicity proof defines a nontrivial character of F_p^*/H for analysis, but the circuit only evaluates the explicit subgroup membership test (2). This is not an assumed primitive element.

## Ring audit and its precise reach

R=Z[1/sqrt(2),i]=Z[1/2,sqrt(2),i]. Every entry of NOT, CNOT, Toffoli, H and S lies in R. Taking inverses conjugates/transposes their matrices and preserves R. A singly controlled gate adds identity blocks, hence also preserves R; scratch conjunctions add only Boolean permutation gates.

Starting in a computational basis state, a finite circuit's unnormalized amplitudes lie in R by addition and multiplication. A computational-basis measurement projects onto selected coordinates. Do not normalize a conditioned branch for this argument: retain its history and unnormalized amplitude. The source retained-history implementation gives the same computational-event probabilities. A bounded adaptive computation has finitely many histories, regardless of whether their number is exponential. Each event is a finite sum of squared moduli of R-elements, and therefore lies in the real ring Z[1/2,sqrt(2)].

Every element of that real ring has form a+b sqrt(2), a,b in Z[1/2]. If it is rational, irrationality of sqrt(2) forces b=0. Thus its intersection with Q is Z[1/2]. Rational computational-event probabilities are dyadic. This includes aggregate ancillary outcomes and retained adaptive histories, but not conditional probabilities after postselection or an unbounded sampler.

For M equally likely labels at total probability z=1 or z=1/4, each label-event probability would be z/M. If M has an odd divisor, this is not dyadic. Exact uniform group preparation when p-1 has an odd factor, and exact uniform flagged generator preparation when phi(p-1) has an odd factor, are excluded. The result makes no assertion about a nonuniform generator distribution. Many exact source-gate probabilities can be irrational; we have not asserted that all probabilities are dyadic.

## Audit of the source completion obstruction

The ordinary generator proposal is uniform over a dyadic range. With known M valid labels and common success-retention t, all successful labels have equal rational mass. Finite independent repetition, taking the first verified success, preserves equality among labels. Mixing this with uniform guesses and label-independent retentions also preserves equality. A single ordinary Grover amplification scales the whole good vector, so it preserves these equal masses. If the end flag has mass 1/4, the ring obstruction applies already before amplification.

Algebraically, the residual branch requires t=2^(b+1)e/M. Dividing by an odd factor of M is a potential forbidden nondyadic coin, even though e and total ordinary success are known dyadics. The rounded global retention is legitimate; the subsequent missing mass is the problem. Per-generator dyadic completion to a common tau is feasible at the small-total stage, but gives total M tau. Raising that total to an exactly known quarter by a symmetry-preserving mechanism encounters the same obstruction.

A sufficient but unproved alternative would compute asymmetric dyadic weights t_g with sum_g t_g equal to the required residual numerator, using valid generators as labels. Knowing M only counts the whole set; it does not compute integer ranks, prefix counts, or an efficiently certified distinguished generator. The modular-power predicates are not linear congruence constraints on integer variables, so invoking fixed-dimensional lattice counting without a new reduction is unjustified.

## Imran's merge operation, independently repaired for analysis

The displayed `gcd(x,y)` is not an explained group operation. If read as the integer gcd of residue representatives, it fails already with x=1: every allowed y outside <1> has gcd(1,y)=1. This is a symbolic counterexample, not a scan. Algorithm 2 also displays r without an update inside the loop. Neither informal line is imported as a proved merge.

A valid replacement, given exact factored orders r=ord(x), s=ord(y), is elementary. For each prime ell in lcm(r,s), choose v_ell from x or y having maximal ell-adic order f_ell, and set w_ell=v_ell^(ord(v_ell)/ell^f_ell). Its order is ell^f_ell. The product w_ell has order lcm(r,s). In a cyclic group, y outside <x> means s does not divide r, so lcm(r,s)/r is an integer >=2. This gives the claimed bounded growth with a correct merge. It leaves the exact escape preparation unresolved in the restricted gate model; our main theorem resolves that preparation classically through the pinned analytic theorem.

## Optional black-box exact order — supporting result only

Specify the oracle interface: elements have unique computational-basis encodings of length h, identity and g are supplied, and reversible multiplication/inversion oracles (and their inverses and controlled uses) are available. Charge their calls. The group is finite, and an integer N with ord(g)<=N is supplied in binary. The conclusion is polynomial in h+log N plus the supplied oracle cost; it is not a theorem for an arbitrary unimplementable multiplication table.

The source order trial already works with |g^x> replacing |a^x mod m>. Choose n=max(128,bitlength(N)), B=2^n>N, Q=B^16. Reversible binary powering uses polynomially many oracle calls, uncomputes its scratch, and retains no extra information about x before the transform. Group values coincide exactly when x=x' mod r. Thus all flagged matrix and probability proofs in source Sections 3–4 transfer verbatim. In the correction modes substitute the identity test g^d=e for a^d=1. Every returned candidate d<B is a multiple of the true order r, and the true candidate probability is

    p(r)=phi(r)2^(-ceil(log_2 r)-10).

Check g=e first and return r=1. For other candidates, factor d with the stipulated exact factorizer; require g^d=e and g^(d/ell)!=e for each prime ell|d. These tests recognize exactly d=r. Their cost is polynomial on every candidate, including false ones. Exact factoring contributes no extra failure. p(r) is computable as a polynomial-bit dyadic on the sole verified value r, and

    p(r)>=1/[2048(n+1)].

Indeed phi(r)/r>=1/(n+1) by the source's elementary product bound, and 2^ceil(log_2 r)<=2r. Independent repetitions R=4096(n+1) have verified success P=1-(1-p(r))^R>=3/4. Use fresh registers and fixed clocks.

The frozen unique-output bridge is independently checked as follows. Let W=n be the unique encoding width for r; on a valid label compute

    C=2^(-(W+2)) floor(2^(W+2)/(2P)),
    e=1/4-PC/2.

Choose the amplified trial with probability 1/2 and retain valid output with C; otherwise guess a uniform W-bit r', verify it using exact factoring and the order tests, and retain with 2^(W+1)e computed from that verified r'. On invalid guesses reject before divisions. Exactly one guess is valid. Since P>=3/4, C<=1 and 0<=e<P2^(-(W+3)); the guessed retention is <1/4. The two masses are PC/2 and e, totaling 1/4. All coins are dyadic of polynomial bit length. Both successful branches compute the same P because they have the same unique r; P is not needed before a valid label exists.

Retained records compile the entire preparation, including factorizations and verifier controllers, to a unitary with inverse. With psi=V|0> and good projection Pi, ||Pi psi||^2=1/4 implies the source's two reflections produce 2Pi psi exactly. This proves certainty and a polynomial worst-case clock. No provisional prime-order logarithm claim is used.

This supporting theorem is a direct group-oracle transfer of the stipulated order trial plus the elementary bridge. It is not a distinct substantial nomination, and does not solve generator search in a generic black-box group. The suggested smaller-Q lattice-count route might also work, but was unnecessary and is not claimed newly audited here.
