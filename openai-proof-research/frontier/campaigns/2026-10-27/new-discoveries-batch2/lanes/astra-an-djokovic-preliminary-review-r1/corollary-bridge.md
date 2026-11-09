# Exact classical-corollary bridge used in the eligibility judgment

This is the reviewer's derivation from an actual classical theorem, not a claim that the following packaging or the An–Đoković endpoint was previously printed. It makes the routine-corollary objection checkable. Its validity and the campaign's judgment of substantiveness are separate questions.

Let n≥2. Write D_n for the unnormalized path divided symmetrization with denominator ∏_(i=1)^(n−1)(x_i−x_(i+1)). The classical input is Postnikov, *Permutohedra, Associahedra, and Beyond*, IMRN 2009, Proposition 3.5, printed p.1035, equivalently Nadeau–Tewari arXiv:1908.10934v2 Lemma 3.7, equation (3.6), p.7:

    D_n(x^a) = (−1)^|S(a)| β_n(S(a)),
    S(a) = {j<n : a_1+...+a_j<j},   ∑ a_i=n−1,

where β_n(S) counts permutations with exactly descent set S. All coefficients and linear maps below are over Q; extension to the source's real polynomial ring is automatic.

For a homogeneous polynomial f of degree n−1 whose internal variable degrees are at most one, define

    F_j(t) = f(t,...,t,1,...,1)  (j copies of t),
    T_j(f) = ∑_(d=j)^(n−1) [t^d]F_j(t),   1≤j<n.

Then the following general evaluation is an elementary corollary of that theorem:

    D_n(f) = (−1)^(n−1) f(1,...,1)
             + ∑_(j=1)^(n−1) (−1)^(n−j−1) binom(n,j) T_j(f).       (B)

Proof of the bridge. By linearity it suffices to take f=x^a. The quantities A_j−j, with A_j=∑_(i≤j)a_i, do not increase as j runs from 1 to n−1, since a_(j+1)≤1. Thus S(a)={r,...,n−1} for a unique r∈{1,...,n}, allowing r=n. A permutation with these descents has its maximum n at r; choosing its r−1 left entries gives β_n(S)=binom(n−1,r−1). The classical value is therefore w_r=(−1)^(n−r)binom(n−1,r−1). Meanwhile T_j(x^a)=1 exactly when j<r. The right side of (B) is

    w_1 + ∑_(j<r)(w_(j+1)−w_j)=w_r,

because Pascal's identity gives w_(j+1)−w_j=(−1)^(n−j−1)binom(n,j). This proves (B) on a basis, hence for arbitrary signed coefficients. No positivity or probability assumption is involved.

Now apply (B) to the literal source numerator

    P_(n,k) = ∏_(j=1)^k (x_n−x_j) ∏_(i=k+1)^(n−1) (x_i−x_1),
    1≤k<n.

It has degree n−1, degree at most one in each internal variable, and P_(n,k)(1,...,1)=0. For j<k, F_j has the zero factor x_n−x_(j+1). For j>k, F_j has the zero factor x_(k+1)−x_1. For j=k, all n−1 factors are 1−t. Consequently

    T_j(P_(n,k)) = 0 (j≠k),
    T_k(P_(n,k)) = ∑_(d=k)^(n−1)(−1)^d binom(n−1,d)
                 = (−1)^k binom(n−2,k−1).

Substitution in (B), with (n−k−1)+k=n−1, gives

    D_n(P_(n,k)) = (−1)^(n−1) binom(n,k)binom(n−2,k−1).            (C)

Finally put Δ=∏_(i<j)(x_i−x_j), A=∏_(i<n)(x_i−x_(i+1)). The three source pattern sets are disjoint and their product is χ_J=(Δ/A)P. Thus Alt(χ_J)=Δ D_n(P). The coefficient of x_1^(n−1)x_2^(n−2)...x_n^0 in Alt(χ_J) is exactly the monomial-orthonormal pairing ⟨χ_J,Δ⟩: the staircase exponents are distinct and each signed staircase monomial of Δ is encountered once. The same coefficient on the right is D_n(P). Combining this identity with (C) gives the complete literal source endpoint, not only a model numerator.

For n=2,k=1, P=x_2−x_1, T_1=−1, and (B) gives −2. For k=1 and k=n−1 the same derivation gives (−1)^(n−1)n. There are no empty-tail or out-of-range conventions hiding these cases.

## Why this matters, and what it does not establish

The general basis evaluation (B) is just the printed classical monomial theorem, terminal descents, and telescoping; its specialization requires only inspecting zero factors and the alternating binomial tail. It supplies an exact route to the full source conclusion with no unevaluated combinatorial or analytic assertion. This is the basis for my recommendation to classify the present candidate as a routine classical corollary under this campaign's unusually strict rule.

That classification is a mathematical judgment, not proof that someone previously wrote (B) or (C). The strongest contrary judgment is that identifying this structure across two literatures, particularly replacing the many signed coefficient classes by the single surviving specialization, is itself a worthwhile all-n contribution. I agree it can merit a short mathematical note. I nevertheless assess its remaining mathematical content, once the actual classical theorem is placed alongside the source polynomial, as routine evaluation rather than the substantive new outcome required here. This judgment does not rely on the brevity of the proof, the age of the conjecture, a registry label, or the existence of a computational algorithm alone.
