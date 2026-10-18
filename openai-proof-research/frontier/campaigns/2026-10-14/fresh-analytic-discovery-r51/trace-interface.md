# Finite-aspect traces versus the Perron cylinder state

Author-side technical analysis; no theorem about the actual six-vertex torus is proved here.

## 1. What the source provides

Source 225, sections 01–03, defines its plane state by first sending the cylinder length M to infinity, then the even circumference L to infinity. The finite row algebra, the real Perron Bethe vector, and fixed-word matrix elements support this order. Section 03 explicitly fixes word length, compact sets and derivative orders before limits, and disclaims uniformity in unbounded word length. Its analytic twist branch is local at each finite L; the proof explicitly does not give an L-independent twist neighbourhood. For part of the homogeneous regime it works at filling L/2-floor(L^epsilon), not at every fixed imbalance from half filling. These are stipulated true source contracts, not defects in the source theorem.

For a row transfer matrix T_L with Perron eigenvalue Lambda_L, the cylinder limit discards other eigenvalues. In contrast, at M/L tending to r>0,

    Z_{L,M}/Lambda_L^M = Tr((T_L/Lambda_L)^M)

retains all eigenvalues whose logarithmic gaps are of order 1/L, with their multiplicities and phases. Separate conserved-arrow sectors must also be compared. Inserted traces are needed for the field law, in addition to the partition function. The source's absence of a completeness hypothesis is useful for its own Perron computation but does not establish trace completeness or trace tails.

## 2. An exact positive-matrix counter-inference

Let P be the orthogonal projection onto (1,1)/sqrt(2), and for a>0 put

    T_L(a)=P+exp(-a/L)(I-P).

Every matrix entry is strictly positive. The Perron eigenvalue is 1 and the normalized Perron vector is independent of a. Thus every single vacuum expectation <v,Av> is exactly independent of a. More generally, for any fixed finite number of uniformly bounded insertions and fixed powers of T_L, the vacuum word limits are independent of a, since ||T_L(a)-I|| tends to zero. At every fixed L, the long-cylinder projection converges to P. Nevertheless

    Tr(T_L(a)^M)=1+exp(-a M/L) -> 1+exp(-ar)

when M/L tends to r. The finite-aspect trace remembers a quantity erased by the iterated limit. This is a counterexample to an abstract inference from these limited contracts, not a counterexample to source 225, its full proof, or the six-vertex torus conjecture.

## 3. Fixed-level convergence is also insufficient

Let L>=2, D_L=L+1, let P_L project onto the constant vector in R^{D_L}, and put

    S_L=P_L+exp(-log(L)/L)(I-P_L).

Again S_L is strictly entrywise positive with Perron eigenvalue 1. The scaled logarithmic spectral energies are 0 once and log L with multiplicity L. For each fixed energy cutoff R, eventually only the Perron level lies below R. In particular every bounded-energy spectral window has converged to the singleton vacuum. Yet

    Tr(S_L^L)=1+L exp(-log L)=2.

A nonzero trace contribution escapes every fixed energy window. Even a non-Perron gap much larger than 1/L is not enough without counting its multiplicity. This exact example motivates a uniform trace-tail bound; it is not a physical construction.

## 4. A sufficient spectral contract, not a deduction

For a hypothetical nonnegative self-adjoint normalized transfer spectrum write E_{L,j}=-L log(lambda_{L,j}/Lambda_L)>=0. Fix 0<r0<r1. If

    sup_L sum_j exp(-r0 E_{L,j}) <= C,

then uniformly for r>=r1,

    sum_{E_{L,j}>R} exp(-r E_{L,j})
       <= C exp(-(r1-r0)R).

The proof multiplies exp(-r0 E) by exp(-(r-r0)E) and bounds the latter on E>R. Consequently convergence of every finite spectral window, with no mass at the cutoff, implies convergence of the full trace for fixed r>=r1 by truncation. For general transfer matrices phases and signs require additional control; this positive-spectrum statement is only a transparent sufficient interface. It is not assumed of six-vertex matrices.

The same bound controls a single bounded insertion A via |Tr(A exp(-rH)1_{H>R})| <= ||A|| Tr(exp(-rH)1_{H>R}) in this self-adjoint positive setting. Macroscopic height tests and multiple inserted traces still need their own convergent matrix elements and suitable bounded or integrable observables. Partition-function convergence alone does not prove the field law.

## 5. Exact scale of the rigorous free-energy error

Duminil-Copin–Kozlowski–Krachun–Manolescu–Tikhonovskaia, arXiv:2012.11675v2, defines f_N^(n) by first taking cylinder length to infinity. Its Theorem 2 has per-site error O(1/N), alongside the quadratic polarization correction for -1<=Delta<1. Setting k=N/2-n and M comparable to N, the expected winding cost is of size

    NM (2k/N)^2 = O(k^2),

whereas the displayed error becomes O(M)=O(N) in the logarithm of the putative cylinder dominant-state weight. At fixed k it does not identify an O(1) ratio. The theorem itself notes that it gives meaningful information only once k exceeds sqrt N. Its admissible imbalance condition must also be retained, especially near Delta=-1. This comparison does not bound the full finite-aspect trace, which additionally includes excited states.

Theorem 22 replaces the per-site error by O(1/[zeta N(N-2n)]) but explicitly assumes a != b and |Delta|<1, with k bounded below by a constant depending on zeta. Its proof uses root-quantile quadrature, interlacement and a positive lower bound for the root density on a truncated interval. With k>0 the log-weight uncertainty is O(M/k)=O(N/k) at fixed aspect ratio. To make this smaller than the quadratic k^2 signal requires k^3 much larger than N. At fixed k it still diverges. It cannot be applied to a=b=1; even a hypothetical extension with the same error would not settle fixed windings. No cancellation between sector errors has been established here.

## 6. Closest torus antecedent and the remaining operations

Noh–Kim, cond-mat/9511001, already gives the compactified Gaussian torus partition function, including mismatch and twist parameters. This is a direct classical antecedent to the intended conclusion. Its operative derivation explicitly assumes differentiability of the inverse phase function at the Fermi endpoints and a 1/N expansion of the phase (equations 33–37), then expands each low-lying energy and sums its conformal descendants (equations 64–74). At the symmetric half-filled point it explicitly says naive endpoint application is invalid and invokes a careful Wiener–Hopf treatment. This screen does not dismiss that literature: it records exactly which assumptions or analyses have not been supplied by the pinned source contract and have not been proved here. We have not read all the cited Wiener–Hopf papers or proved a uniform summability bound for the resulting levels.

The JEMS 2024 delocalization paper studies the balanced finite torus and proves logarithmic variance, distinguishing that from a torus GFF limit. Its displayed torus theorem therefore does not supply winding weights. Its further-questions discussion also identifies the failure of its positive-association tools for c<1. The logarithmic variance result is substantial existing work, not a new corollary claimed here.

Two concrete routes were tested at the interface level. (i) Applying the rigorous sector free-energy asymptotic loses O(N) or O(N/k), so cannot normalize fixed sectors. (ii) Reusing source local kernels across a finite-aspect trace requires excited-state completeness, endpoint expansions and uniform entropy bounds; fixed-word Perron formulas do not provide them. A spatial alternative would require torus-uniform conditional response or winding-sensitive Ward identities, also absent from the read source contracts. No construction closing any of these debts is obtained. The full torus direction remains unproved in this packet, not refuted and not claimed open worldwide.


## 7. Why the existing geometric torus reduction does not repair this

DKLM, arXiv:2603.06268v1, section 18, actually defines a modified torus spin law conditioned on height gains in 8Z. Remark 18.3 explicitly distinguishes it from the original six-vertex law, which admits gains in 2Z not in 4Z; the extra restriction is used in the FKG decomposition. Its Lemma 18.7 proves cylinder identification by the lower bound

    P(balanced) >= 1-(1-eta^L)^(M/2),    0<eta<1,

from equation (324). For fixed L this tends to one as M tends to infinity. At M comparable to L, Bernoulli's inequality instead bounds this displayed lower bound above by (M/2)eta^L, which tends to zero. Thus that estimate supplies no positive finite-aspect lower bound. This statement concerns the usefulness of the estimate, not the actual balanced probability. The modified law's finite-support local limit is also not a statement about the full rescaled field or winding distribution. No 8Z conditioning is silently substituted for the full intended torus law.

The same primary's Theorem 2.2 identifies local arrow limits, including arbitrary joint growth of M,L for c in [1,2], and Theorem 2.8 gives the full-plane GFF for c in [sqrt(3),2]. Remark 3.1 explicitly explains that its spectral method averages eigenvalues away from the edge and circumvents a leading-eigenvalue calculation. This is compatible with the spectral debt above. No defect of those proved results is alleged.
