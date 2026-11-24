# Balanced Fourier certificates for circulant matrix completion

**Formalization status: COMPLETE.** The accompanying Lean theorem `Circulant.mathdb338558` proves the literal generic complex completion-rank formula, including all definitions and both global algebraic bridges. The eight stage-1 modules are unchanged. Independent final review and replay remain acceptance steps for the parent campaign.

## Abstract

A balanced mechanical word supplies Fourier frequencies with bounded collision multiplicities for every cyclic band mask. Vandermonde interpolation then proves injectivity of restriction of a tensor product to the missing entries. Bilinear annihilator duality gives a surjective differential for the observed rank-factorization map; dominance and constructibility give generic low-rank completions. Determinantal charts prove the matching lower bound. Thus the ordinary proof gives generic complex completion rank n-floor(sqrt(n(n-l))) for all n≥1 and 0≤l≤n. The Lean certificate includes the Jacobian criterion, actual complex-point lifting by Chevalley and Nullstellensatz, and a polynomial-chart proof of the matching lower bound.

## Source and literal statement

D. I. Bernstein, G. Blekherman and R. Sinn, Typical and Generic Ranks in Matrix Completion, Linear Algebra and its Applications 585 (2020), 71–104, arXiv:1802.09513v2. Final journal text: https://par.nsf.gov/servlets/purl/10356160 . Source quotations below transcribe the mathematical symbols in the supplied cached journal text.

Conjecture 5.6:

> Bipartite circulant graphs of the form G(n,l) have the generic completion rank predicted by the dimension count. That is, gcr(G(n,l)) = n − floor(sqrt(n²−nl)).

The literal MathDB 338558 record, preserved in `record-338558.txt`, reads:

> The generic-rank conjecture for bipartite circulant graphs
> Let $G(n,l)$ be a bipartite circulant graph of the form considered in the paper, and let the generic completion rank be the rank attained by a generic matrix completion. The dimension-count prediction is
> 
> $$
> n-
> \left\lfloor\sqrt{n^2-nl}\right\rfloor.
> $$
> 
> **Bipartite circulant generic-rank conjecture.** Every graph $G(n,l)$ has generic completion rank predicted by the dimension count; equivalently,
> 
> $$
> \operatorname{gcr}(G(n,l))=n-\left\lfloor\sqrt{n^2-nl}\right\rfloor.
> $$
> 
> The paper proves the dimension-count prediction for a subset of these graphs and conjectures it for all bipartite circulant graphs of this form. The claim is presented as unresolved.
> Daniel Irving Bernstein, Grigoriy Blekherman and Rainer Sinn, “Typical and Generic Ranks in Matrix Completion”, arXiv:1802.09513 (2019). https://arxiv.org/abs/1802.09513

Section 5.3 defines the family:

> We consider the subset of such graphs whose parts A and B are disjoint copies of [n], where each i ∈ A is adjacent to all vertices in B aside from i, i+1, ..., i+n−l−1. We denote such a graph by G(n,l).

These are cyclic indices. Reindexing [n] by Fin n gives exactly the modular band used in Unknown below.

Definition 2.1:

> Let G = (R ∪ C,E) be a bipartite graph. The (K-)completion rank of a G-partial matrix M ∈ K^E is the smallest rank among all completions of M with entries in K, i.e. all matrices A ∈ M_(m×n)(K) such that π_G(A) = M. For K = C, we usually say complex completion rank. Analogously, we say real completion rank in the case K = R.

Proposition 2.2 gives the generic quantifier:

> Then there exists a unique integer r that is the completion rank of almost all G-partial matrices. Here, “almost all” means all G-partial matrices in the complement of a certain hypersurface in K^E.

Definition 2.4:

> We call the integer r for K = C of the previous proposition 2.2 the generic completion rank of the bipartite graph G. We write gcr(G) for the generic completion rank.

Here C in the source quotations means the complex field ℂ. The matching Lean definitions are printed next to these source definitions:

```lean
def Unknown (n l : ℕ) : Set (Fin n × Fin n) :=
  {ij | ∃ s : ℕ, s < n - l ∧ ij.2.val = (ij.1.val + s) % n}

def Observed (n l : ℕ) : Set (Fin n × Fin n) := (Unknown n l)ᶜ

def Agrees {n : ℕ} (E : Set (Fin n × Fin n))
    (x : E → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ e : E, M e.val.1 e.val.2 = x e

def CompletionRank {n : ℕ} (E : Set (Fin n × Fin n)) (x : E → ℂ) : ℕ :=
  Nat.find (completion_exists E x)

def ZeroLocus {I : Type*} (S : Set (MvPolynomial I ℂ)) : Set (I → ℂ) :=
  {x | ∀ p ∈ S, MvPolynomial.eval x p = 0}

def ZOpen {I : Type*} (U : Set (I → ℂ)) : Prop :=
  ∃ S : Set (MvPolynomial I ℂ), U = (ZeroLocus S)ᶜ

def PrincipalOpen {I : Type*} (p : MvPolynomial I ℂ) : Set (I → ℂ) :=
  {x | MvPolynomial.eval x p ≠ 0}

def GCR {n : ℕ} (E : Set (Fin n × Fin n)) (r : ℕ) : Prop :=
  ∃ U : Set (E → ℂ), ZOpen U ∧ U.Nonempty ∧
    ∀ x ∈ U, CompletionRank E x = r

def LiteralConjecture : Prop :=
  ∀ n l : ℕ, 0 < n → l ≤ n →
    GCR (Observed n l) (n - Nat.sqrt (n * (n - l)))
```

The predicate minimized by CompletionRank is existence of an actual agreeing matrix of rank t; completion_exists proves its inhabitation by zero filling. Matrix.rank is Mathlib's linear-map rank, connected to the range dimension by Matrix.rank_eq_finrank_range_toLin. Attainment and minimality are proved, rather than assumed.

Every nonempty ZOpen contains a principal open D(p) with p nonzero (principalOpen_inside), so shrinking gives the source's hypersurface-complement formulation. Nonzero polynomials over ℂ have nonzero evaluations (MvPolynomial.funext). Products show that two nonempty opens intersect, proving uniqueness of GCR (gcr_unique). The empty-variable affine space is included.

## Theorem and ordinary proof

For all n≥1 and 0≤l≤n, the least rank of an actual complex completion is n-floor(sqrt(n(n-l))) on a nonempty Zariski-open subset of the observed-coordinate space.

Index rows and columns by Z/nZ, represented by 0,...,n−1, and put d=n−l. The **unspecified** entries are precisely

    H={(i,i+s mod n): i in Z/nZ, 0<=s<d}.

The observed entries E are its complement, so |H|=nd and |E|=nl. Generic completion rank means the unique rank attained as the minimum complex completion rank on a nonempty Zariski-open set of observed entries (source Proposition 2.2). This is not a claim about every real filling or the maximum typical rank.

We prove, for all n>=1 and 0<=d<=n,

    gcr(E)=n−floor(sqrt(nd)).

## Lemma 1: an evenly spaced set of frequencies

For integers 0<=k<=n define a periodic binary sequence

    e_j=floor((j+1)k/n)−floor(jk/n), j in Z.

Each e_j is 0 or 1, e_(j+n)=e_j, and its sum over one period is k. Let A be the k-element subset of Z/nZ where e_j=1. Let B={0,...,k−1}.

For any integer L and any nonnegative integer d with k²<=nd,

    sum_(j=L)^(L+k−1) e_j
      =floor((L+k)k/n)−floor(Lk/n)
      <=floor(Lk/n+d)−floor(Lk/n)
      =d.                                                     (1)

For each residue f, the set of pairs

    F_f={(a,b) in A×B: a+b=f mod n}

therefore has at most d elements: its a-coordinates are precisely the elements of A in the cyclic interval f−k+1,...,f. Distinct pairs in F_f have distinct b-coordinates, since a=f−b determines a uniquely. The periodic-sequence proof covers intervals that wrap around 0 and non-coprime k,n without exceptions.

## Lemma 2: an injective restriction on a tensor space

Suppose 1<=k<n and k²<=nd. Let zeta be a primitive nth root of unity in C. Define n×k matrices U,V by

    U_(i,a)=zeta^(ia), a in A;
    V_(j,b)=zeta^(jb), b in B.

Both have column rank k. Indeed, they consist of subsets of the distinct character columns of the n×n Fourier matrix. For completeness, those columns are independent because

    sum_(i=0)^(n−1) zeta^(ih) = n if h=0 mod n, and 0 otherwise;

for nonzero h this is the finite geometric-series identity and zeta^h!=1. Multiplying a linear relation by each opposite character and summing isolates its coefficient.

We claim that the linear restriction map

    C in C^(k×k) |--> ((U C V^T)_(i,i+s))_(i,s), 0<=s<d,       (2)

is injective. All transposes in this proof are ordinary transposes, with no complex conjugation.

If C is in its kernel, then for every i and every s in 0,...,d−1,

    0=sum_(a in A,b in B) C_(a,b) zeta^(i(a+b)) zeta^(sb).

Independence of the Fourier characters in i yields, separately for every residue f,

    sum_((a,b) in F_f) C_(a,b) (zeta^b)^s=0, 0<=s<d.           (3)

Put m=|F_f|. Lemma1 gives m<=d. The m numbers zeta^b indexed by F_f are distinct: the b's are distinct integers between0 and k−1<n. Restricting (3) to s=0,...,m−1 gives a square Vandermonde system, whose determinant is the product of all pairwise differences of these distinct numbers. It is nonzero. Thus every C_(a,b) in F_f is zero. Empty F_f's impose no condition. The F_f's partition A×B, so C=0, proving injectivity.

The construction is valid even when nd is not a square; excess missing entries simply give more equations than needed in some blocks. No divisibility assumption on k and n is used.

## Lemma 3: the differential criterion for generic completion rank

Let E be any observed mask, H its complement, r=n−k, and U,V any n×k full-column-rank matrices. If restriction of U C V^T to H is injective in C, then gcr(E)<=r.

Here is the full linear-algebra reduction and the standard genericity step. Choose full-column-rank n×r matrices P,Q such that

    ker(P^T)=col(U), ker(Q^T)=col(V).

Such matrices exist by quotient spaces. For W=col(U), the quotient ℂⁿ/W has dimension n−k, so choose a linear equivalence with ℂʳ and compose it with the quotient map. The transpose of its matrix is P. Then ker(Pᵀ)=W. Construct Q in the same way. No non-isotropy hypothesis is needed; no Hermitian pairing is used.

Consider the polynomial map

    Phi(P',Q')=(P' Q'^T)|E

from two n×r matrix spaces to C^E. Every point of its image has a completion of rank at most r. Its differential at (P,Q) sends (D,F) to

    (D Q^T+P F^T)|E.                                         (4)

We show this differential is onto. Let a linear functional on C^E annihilate its image, and extend its coefficient array by zeros on H to an n×n matrix N. Pairing coefficients using trace(N^T X), annihilation of (4) for arbitrary D,F says

    N Q=0, N^T P=0.                                          (5)

The second equation says every column of N is in ker(P^T)=col(U), so N=U D0 for some k×n matrix D0. Since U has independent columns, the first equation implies D0 Q=0. Each row of D0 is consequently the transpose of a vector in ker(Q^T)=col(V), hence D0=C V^T for some k×k matrix C. Thus N=U C V^T. But N vanishes on H. The assumed injectivity gives C=0, so N=0 and the original linear functional is zero. Finite-dimensional duality now proves surjectivity of (4).

Select a nonsingular square column minor of the observed Jacobian. This is possible because its rows are linearly independent. Regard its entries as partial derivatives of polynomials f_j in all factor variables; the determinant is a nonzero polynomial since it has a nonzero evaluation at (P,Q).

Here is a fully algebraic dominance argument, also implemented in Lean. If R(f)=0 is a nonzero relation of minimum total degree, differentiate in every selected input direction. The chain rule gives a row vector with entries (∂R/∂y_j)(f) multiplied by the square Jacobian minor equal to zero. Its determinant is nonzero in the integral domain of input polynomials, so this vector is zero. Every nonzero partial derivative of R has smaller total degree and would itself be a relation, a contradiction. Hence every partial derivative of R is zero. In characteristic zero this forces R to be constant: for any nonconstant monomial with nonzero coefficient, differentiating in a positive-exponent variable gives a nonzero coefficient. A nonzero constant cannot be a relation. Therefore f is algebraically independent and the coordinate homomorphism φ:ℂ[y]→ℂ[z], y_j↦f_j, is injective.

We now prove actual generic point lifting, not just density of an image. The homomorphism φ is of finite type: ℂ[z] is generated over ℂ[y] by its finitely many input variables. Since ℂ[y] is Noetherian it is of finite presentation. Chevalley's theorem makes the image of Spec(φ) constructible. Its image contains the zero prime because φ is injective. Write this constructible image as a finite union of sets V(g₁,…,g_s)∩D(p). A component containing the zero prime has every g_i=0 and p≠0. Thus D(p) lies in the spectrum image.

Write Y_j for the target coordinate indeterminates, and let y=(y_j) be any complex point with p(y)≠0. Its evaluation ideal lies in D(p), hence has a prime Q above it in ℂ[z]. Extend Q to a maximal ideal N. The weak Nullstellensatz over ℂ identifies N with the evaluation ideal of a complex point z. For every j, Y_j−C(y_j) belongs to the target evaluation ideal, so f_j−C(y_j) belongs to Q and therefore to N. Evaluation at z gives f_j(z)=y_j. The factor matrices encoded by z give an actual completion of rank at most r. Since p is nonzero, D(p) is nonempty. This is the required upper polynomial certificate.

These are standard generic matrix-completion facts; the source's proof of Lemma 4.13 uses the same differential principle for its special indicator-vector construction. Our proof above supplies the full-row-rank version needed when |H| may exceed k².

## Completion of the theorem

If d=0, every entry is observed and a generic matrix has rank n. If d=n, no entry is observed and the zero matrix gives completion rank 0. These agree with the formula.

Now 1<=d<n. Set

    k=floor(sqrt(nd)), r=n−k.

Then 1<=k<n and k²<=nd, so Lemmas 1–2 construct U,V satisfying Lemma 3. Consequently gcr(E)<=r.

For the lower bound we use polynomial charts, avoiding rational denominators. Let M have rank exactly t. Select t independent rows indexed by an embedding s:{1,…,t}↪{1,…,n}; they form a basis of its row space. Let Q be the t×n matrix consisting of these rows and let P contain the coordinates of each row of M in this basis. Then M=PQ and P_(s(a),b)=δ_(a,b). The nt entries of Q and the (n−t)t entries of P outside the selected rows are unrestricted parameters. For each fixed s, the entries of PQ are polynomial expressions in exactly t(2n−t) variables. These charts cover every rank-exactly-t matrix, with no invertibility or generic-position exception.

If a polynomial map has fewer input coordinates than outputs, its coordinate polynomials are algebraically dependent: otherwise the transcendence degree of the input polynomial algebra would be at least the number of output coordinates. Thus each projected chart has a nonzero polynomial q_s vanishing on its entire complex point image. The product over the finitely many row embeddings is nonzero and vanishes on every projected rank-t matrix. Taking a further product over t<r gives a nonzero polynomial q vanishing on every projected matrix of rank below r. Empty products are one, so r=0 is included.

If t<r, then n−t>=k+1>sqrt(nd), and therefore

    t(2n−t)=n²−(n−t)²<n²−nd=nl=|E|.

The rank-at-most-t variety cannot dominate C^E. Its projected closure is proper, so generic observed entries cannot be completed at rank at most t. Hence gcr(E)>=r.

On the principal open D(pq), where p is the upper certificate and q is the lower certificate, both conclusions hold simultaneously. The polynomial pq is nonzero, and over ℂ its non-vanishing set is nonempty. Thus the minimum completion rank is exactly r there, proving the exact literal formula for every G(n,l).


## Exact scope of the Lean packet

The appendix contains all 22 Lean modules in import order, with byte-exact source blocks. The final endpoint is

```lean
theorem Circulant.mathdb338558 : ∀ n l : ℕ, 0 < n → l ≤ n →
  Circulant.GCR (Circulant.Observed n l) (n - Nat.sqrt (n*(n-l)))
```

`Circulant.literalConjecture_proved` inhabits the unchanged `Circulant.LiteralConjecture`. The proof constructs the upper p and lower q described above and applies `gcr_of_polynomial_certificates` on D(pq). A point in this nonempty open has a rank-at-most-r completion, while no agreeing matrix has rank below r. CompletionRank is therefore exactly r.

The finite Fourier implementation isolates characters using the nonsingular Vandermonde matrix of all n roots of unity. The tangent implementation proves independence of actual polynomial Jacobian rows directly rather than introducing a separate analytic differential. It uses a linear splitting of col(U) to preserve NQ=0 under the factorization N=UD; this also handles matrices with redundant columns. The actual factor-variable and chart-variable finite types are retained instead of relabelling them by Fin. Their cardinalities are proved. The proof handles k=0, k=n and empty observed-coordinate spaces uniformly.

`GenericImage` and `JacobianCriterion` contain the abstract global bridge. `MatrixKernel`, `TensorAnnihilator`, `SquareMinor`, `FactorJacobian` and `CirculantUpper` connect it to the stage-1 certificate. `RankFactorization`, `RankCharts`, `FinitePolynomialObstruction`, `LowRankPolynomial` and `CirculantLower` prove the lower certificate. `CirculantConjecture` assembles the literal theorem. `CirculantFinalAudit` prints all 37 new theorem statements and their axiom dependencies. DESIGN.md records the dependency map and the deliberate helper-signature refinements. There are no unproved formal bridges.

## Significance and prior-art limits

The balanced Fourier frequency construction supplies the all-parameter ingredient missing from the source's partition and divisible-square cases. Fourier independence, Vandermonde interpolation, determinantal dimensions, Chevalley and Nullstellensatz are standard. The contribution is the uniform balanced frequency selection and collision-block interpolation for every cyclic band. The independent Opus review judged this nonroutine, while recording the risk that a specialist might recognize a coding-theoretic construction. Formal verification establishes the theorem; it does not establish priority. No numerical checks enter the proof.

The following bounded prior-art report is reproduced from section 1 of the supplied cross-model Opus review dated 2026-11-20. This implementation lane did not perform a fresh external search and makes no stronger novelty claim:

- Source: Bernstein–Blekherman–Sinn, arXiv:1802.09513v2 (22 Sep 2019), LAA 585 (2020) 71–104, Conjecture 5.6 (also Conjecture 1.5). I downloaded the v2 PDF myself, after arXiv's robots.txt (crawl delay 15 s respected), and read §2 (Def. 2.1, Prop. 2.2, Rem. 2.3, Def. 2.4, Prop. 2.5), §4 (Lemmas 4.1, 4.11–4.13) and §5.3 (Prop. 5.4, Conj. 5.6, Prop. 5.7). The Sol lanes read the open final journal copy (par.nsf.gov 10356160), which keeps the conjecture.
- Principia: the id is not in `principia-ids.txt`, and the clone has no hit for the id, "1802.09513", "generic completion rank" or "bipartite circulant".
- Omega registry issues: searches for "1802.09513", "circulant generic rank", "Blekherman Sinn matrix completion", "completion rank" and "338558" returned nothing relevant. The only hits are chordal PSD completion research units and the Bourin–Lee operator conjecture.
- Later literature: I read the circulant parts of Dressler–Krone, *Multiple typical ranks in matrix completion*, arXiv:2010.09777v2 (12 Mar 2025; LAA 2025). It studies **real typical** coranks of G(n,k)ᶜ and gives asymptotic real-completability bounds (Props. 4.1 and 4.3). Its Corollary 3.6 is for anti-band patterns. It quotes only Prop. 5.7 (the crown graphs) for gcc and does not prove the general complex formula. I also read the abstract and introduction of Brakensiek–Dhar–Gao–Gopi–Larson, arXiv:2405.00778v2 (Mar 2026), on the link between completion matroids and MR tensor codes. There is no circulant or band result in it. Correctable patterns of MR tensor codes are characterised only for a = b ≤ 2.
- Tsakiris (2004.12430, TPAMI 2023): its families of finitely completable patterns are built from SLMF partitions. Applying them to circulant patterns would itself be a new construction, not a citation.
- Citing list: OpenAlex refused me (daily budget exhausted), and I respected that. The discovery lane's saved list has 15 titles, and I screened them. None is about circulant generic rank; the closest are the determinantal matroid papers, which the Sol lanes screened in full text.
- Web searches (extended and standard): no full proof of Conj. 5.6.
- Conclusion: nothing public found (bounded search).


## Reproducibility and limits

PINS.json records Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. Binary and metadata hashes were independently checked in pin-verification.json. All final modules are compiled and kernel-checked through the inherited runner with its 32-GiB address-space, 6-GiB resident-memory and CPU guards. REPORT.md records the receipts, endpoint statements and axiom output. Only propext, Classical.choice and Quot.sound occur in final endpoint dependencies. The ordinary proof uses no numerical evidence. Nothing was submitted, published, uploaded or sent anywhere.
