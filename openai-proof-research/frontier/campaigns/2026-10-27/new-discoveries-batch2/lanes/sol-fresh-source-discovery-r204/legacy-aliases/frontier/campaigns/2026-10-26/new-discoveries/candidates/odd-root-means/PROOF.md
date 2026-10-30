# Candidate resolution of MathDB 336466

Date: 2026-10-26. Status: complete written algebraic argument and full source-definition Lean proof; pinned independent-build replay PASS50 declarations in6 modules. Independent mathematical/source/novelty review pending. No discovery count authorized here.

## Exact primary statement

Gregory Gerard Wojnar, Daniel Sz. Wojnar, Leon Q. Brin, *Universal Linear Mean Relationships in All Polynomials*, arXiv:1706.08381v2, 23 October 2017, Section 4, Conjecture 2:

For every odd degree D polynomial f:C→C,

    sum_{rho=1}^{D-1} (-1)^rho binom(D,rho) phi(D,0,rho) = 0.

Section 1 explicitly defines the root family as a multiset of D roots, even when roots repeat. Here phi(D,0,rho) is (D-rho)^(-1) times the sum of f over the roots of f^(rho), with multiplicity. No real-rootedness, simplicity, positivity, or generic-coefficient hypothesis is imposed. The primary paper reports computation through degree49, and labels the general identity a conjecture in its latest v2.

Primary URLs: https://arxiv.org/abs/1706.08381 ; https://arxiv.org/html/1706.08381v2 . Local exact source: sources/1706.08381v2.html. Fresh MathDB snapshot: sources/336466.json.

## Algebraic theorem and proof

It suffices to prove the assertion for monic f: multiplication by its nonzero leading coefficient preserves every derivative root multiset and multiplies all the means by that coefficient. Write

    f(z)=F_D(z)=sum_{k=0}^D binom(D,k) a_k z^(D-k),  a_0=1.

Extend a_k arbitrarily beyond D (for example by zero). For each integer m≥1 define the monic polynomial

    F_m(z)=sum_{k=0}^m binom(m,k) a_k z^(m-k).

For 1≤m≤D, differentiation term by term gives

    f^(D-m)=(D!/m!) F_m.

Consequently their roots, with multiplicity, coincide. Let S_i(m) be the sum of the i-th powers of all m roots of F_m, and set q_0(T)=1. For i≥1 put

    B_i(T)= (T-1)(T-2)...(T-i+1)/i!,
    C_i(T)=T B_i(T),
    q_i(T)=-sum_{k=1}^{i-1} C_k(T) a_k q_{i-k}(T)
           - i B_i(T) a_i.

The empty product is1, so B_1=1. C_k is the usual binomial-coefficient polynomial binom(T,k).

**Normalized Newton-moment lemma.** For every integer m≥1 and i≥1,

    q_i(m)=S_i(m)/m,
    deg(q_i)≤i-1,
    q_i(0)=(-1)^i a_i.

Proof. The standard Newton recurrence, with coefficients c_k=binom(m,k)a_k and c_k=0 for k>m, is valid for every i≥1:

    S_i(m)+sum_{k=1}^{i-1} c_k S_{i-k}(m)+i c_i=0.

For i>m it is the usual homogeneous recurrence, as c_i=0; for i≤m it is Newton's inhomogeneous identity. Divide by the nonzero integer m, and use c_i/m=B_i(m)a_i; induction on i proves the evaluation claim. In particular the formula also works for i>m. This is important because f has degree D, even when F_m has smaller degree. Each summand C_k q_{i-k} has degree at most k+(i-k-1)=i-1, and B_i has degree i-1. This proves the degree bound. Every C_k(0)=0, while B_i(0)=(-1)^(i-1)/i, yielding the constant-term identity. □

Now form the polynomial in the degree parameter

    Phi(T)=sum_{k=0}^D binom(D,k)a_k q_{D-k}(T).

For integer 1≤m≤D its evaluation is precisely the average of f on the roots of F_m, by expansion of f and q_0=1. Thus

    Phi(m)=phi(D,0,D-m).

The degree bound is deg(Phi)≤D-1 (the q_0 summand is constant). At m=D every evaluation of f is0, so Phi(D)=0. At the artificial argument T=0 the just-proved constant-term formula gives

    Phi(0)=sum_{k=0}^D binom(D,k)(-1)^(D-k)a_k a_{D-k}.

**Phi(0) is not an average over roots of a constant polynomial.** It is the value at0 of the polynomial extension of the positive-integer root means, defined by the preceding recurrence. This value is, up to the conventional overall sign, the classical degree-D apolar self-pairing. For odd D, pairing the k summand with the D-k summand cancels them: the binomial coefficients are equal, the products commute, and the signs are opposite. Hence Phi(0)=0.

The D-th finite difference of a polynomial of degree≤D-1 is0:

    sum_{m=0}^D (-1)^m binom(D,m)Phi(m)=0.

Its endpoint terms m=0,D vanish, so reindexing rho=D-m gives the exact source identity, up to the common nonzero factor (-1)^D. For D=1 the desired sum is empty, hence0, and the same proof is valid. This proves the conjecture for every odd D and every complex polynomial of that degree, with root multiplicities included. □

## Ingredient credit and preliminary nearest-prior audit

Newton's identities, polynomial finite differences, and the fact that odd-degree binary forms are apolar to themselves are classical; no novelty is asserted for any of them. The proposed contribution is the exact bridge from normalized derivative-root moments to the polynomial extension Phi, whose zero endpoint is identified with apolarity, resolving the full stated mean identity.

An important older neighboring result must receive prominent credit: Kiyoshi Toda, *On Certain Functional Inequalities*, Journal of Science of Hiroshima University, Series A4(1934),27–40, DOI10.32917/hmj/1558749761; and *A Method of Approximation of Convex Functions*, Tohoku Mathematical Journal42(1936),311–317. Tiberiu Popoviciu, *Notes sur les fonctions convexes d'ordre supérieur (III)*, Mathematica16(1940),74–86, Section11, explicitly credits Toda with the following: for a polynomial P of degree m with all roots real and a test polynomial h of degree≤n<m,

    sum_{i=0}^n (-1)^i binom(n,i) average_{P^(i)=0} h =0.

This is the lower-degree moment/finite-difference phenomenon used above. It does not directly supply the source endpoint: our test polynomial has the same degree as P, our weights have n=m, and the absent degree-zero root average has to be replaced by an apolar self-pairing. The 1936 primary paper pp315–316 uses normalized binomial coefficients and Waring's formula to compute related derivative-root moment differences. It does not state the source odd-degree self-evaluation identity in its7 pages. The 1940 original French scan and the1936 original primary have been read (including displayed formulas in rendered pages); sources are retained locally. The1934 publisher endpoint presents an anti-bot page, so its full body has not yet been read. This inaccessible primary is a residual novelty risk, not evidence of a prior proof.

Links: https://www.jstage.jst.go.jp/article/tmj1911/42/0/42_0_311/_pdf/-char/en ; https://ictp.acad.ro/notes-on-higher-order-convex-functions-iii/ ; https://doi.org/10.32917/hmj/1558749761 .

No explicit published proof of the full2017Conjecture2 has been located in the targeted searches so far. This is a finite-search statement, not a worldwide-priority certification. Exact rational quotient-algebra traces independently verify180 random polynomials across odd degrees1–35. The full Lean source-definition bridge is complete and the fresh pinned verifier passes all50 declarations with warningAsError and only propext, Classical.choice, Quot.sound. Independent mathematical/source/novelty review and remaining nearest-prior checking are required before discovery acceptance.
