# Ordinary investigation, author only, no candidate
All derivations here were done personally without enumeration, numerical experiments, CAS, solvers or formal execution. No independent PASS or credit is asserted.

## 341858: the determinant route collapses to a correction and a general rank law
Primary acquired: Cimpoeas, arXiv 1902.05302v1, equations (4.7), (4.9), (4.11)-(4.14), Conjecture 4.4 and Lemma 3.1. Material source glyphs were not visually rendered; statements below bind the extracted text, with this fidelity limitation retained. The extracted lower product index is zero, as is the corpus literal. Already r=1 makes that printed formula incompatible with (4.7): the 2 by 2 determinant with first row (1,1), second row (B1(x),B1(y)) is y-x, whereas the displayed conjecture gives (y-x)^3. This is a source/endpoint correction, zero credit.

I pursued the intended all-r product with lower index 1 rather than stopping at r=1. Let t=y-x and set
 P_k(x,t)=(B_{k+1}(x+t)-B_{k+1}(x))/(k+1), k>=0.
Let M_r=(P_{i+j}(x,t)) for i,j=0,...,r-1. Column subtraction and expansion of (4.7), equivalently (4.11), give Fbar_{r,2}(x,x+t)=(-1)^{r(r-1)/2} det M_r. For positive integers N, the Bernoulli difference identity gives
 P_k(x,N)=sum_{s=0}^{N-1}(x+s)^k.
This is a Gram moment matrix of N evaluation vectors. Translating the variable from s to x+s conjugates by a unit lower-triangular Pascal matrix, so its determinant is independent of x. The same statement for polynomial x,t follows because the identities hold for every positive integer N and all x. This is polynomial identity, not experimental interpolation.

Every entry is divisible by t, so det M_r is divisible by t^r. At t=N, 1<=N<r, rank M_r<=N. Subtracting its value at N shows that the determinant has zero order at least r-N: multilinearity needs at least r-N columns from the difference matrix before a term can have full rank. At t=-N,
 P_k(x,-N)=-sum_{s=-N}^{-1}(x+s)^k,
so the identical rank argument supplies (t+N)^(r-N). Thus det M_r is divisible by
 t^r product_{j=1}^{r-1}(t^2-j^2)^(r-j).
Its degree is at most r^2, since P_{i+j} has degree i+j+1 in t and every determinant term has summed degree r^2. The displayed product has exactly that degree. The top coefficient is det(1/(i+j+1)), whose exact nonzero value is supplied by primary Lemma 3.1:
 C_r=[1!2!... (r-1)!]^3/[r!(r+1)!...(2r-1)!].
Consequently the corrected product is proved for every r>=1, with empty products at r=1. This uses source Bernoulli definitions and the source Hilbert determinant evaluation; no new estimate is needed. It is an instance of the generic polynomial moment-rank factorization law. The deliberate all-r conjecture is the strongest significance case; the correction plus complete generic rank bridge is the stronger objection. No candidate is proposed, and no earlier printed corrected formula is claimed authenticated. The bounded search found no usable Bernoulli follow-up; that is not a worldwide novelty conclusion.

Lean: Matrix.det, Polynomial, rational coefficients, factorials, finite sums and Bernoulli polynomials are established mathlib objects. A literal endpoint must use (4.7), not an invented replacement determinant. The printed j=0 literal has a tiny r=1 negation; the intended j=1 identity would require the determinant bridge, Bernoulli difference identity, rank-to-multiplicity lemma and degree/leading-coefficient argument. No imports, exact lemma names or kernel feasibility were tested. No formal dispatch is justified.

## 357983: generic quotient / incidence / differential routes, incomplete
Primary: Julian Vill, 2304.02332v1, Theorem 7.8, Example 7.7, Conjecture 7.11 and Remark 7.12, pp18-20. Wbar is the image in A/(l), not W itself. The source already proves n>=2k+1 and k=1. Those cases and the exceptional common-factor example earn zero credit. The restriction enters the proof at the simultaneous independence of H1,...,Hr,l1,...,l_{k+1}, requiring r+k+1<=n; simply improving an estimate cannot cross it.

Route 1 (geometric section): If a generic quotient contains a pure power, write F_l=L_l^d+l G_l in W. Taking zero sets shows a degenerate generic hyperplane section of V(W), but this loses scheme multiplicity and does not force W itself to contain a pure power. Example 7.7 is exactly the failure. Repeating Bertini as if nondegeneracy alone settled the conjecture is invalid.

Route 2 (incidence fibers): Pass to projective nonzero F in P(W) and record pairs ([l],[F]) for which F modulo l is a nonzero pure power. Green's injectivity at k<n ensures that the generic image F is not zero. A dominant incidence component over P(A1) has dimension at least n-1; its map to P(W) has fibers of dimension at least n-k. Therefore when n>=k+2 one is led to a fixed nonpower homogeneous F with at least a two-dimensional family of hyperplanes whose section is a pure d-th power. A useful missing theorem would bound this hyperplane family by dimension one for every nonpower F in characteristic zero. I did not prove that theorem, and do not assert it as classical. In the boundary n=k+1 even that bound would only allow one-dimensional fibers and would not classify W. The required simultaneous classification of W remains an additional gap. This explains precisely why a naive parameter count is not a proof.

Route 3 (differentiating the incidence): On a smooth local branch, F=L^d+lG yields, modulo l,
 dotF=d L^(d-1) dotL + dotl G.
For tangent directions in a fiber with fixed [F], scaling removes dotF. If dotl modulo l is relatively prime to L, then L^(d-1) divides G modulo l. If there are many independent such directions, this is restrictive. However one must prove existence and independence of these directions, handle ramification and nonreduced incidence components, and convert the local divisibility into a common factor for every F in W. These are unpaid. Substituting the expected exceptional form does verify it, but is a parameter instance, not classification.

No full-scope theorem or counterexample survives. No complete applicable classical subsumer was found; no routine exclusion is claimed for the unresolved conjecture. Search3 had no concrete matching later proof, which does not establish open status or novelty. Final/journal/correction and companion checks remain unpaid after network stop.

Lean: MvPolynomial over Complex, Submodule, Ideal quotient and linear maps exist. The literal needs a definition of homogeneous degree-d forms, the pure-power locus, a precise nonempty Zariski-open generic-l quantifier, and the exceptional basis form. Complete generic-incidence dimension and family-classification infrastructure is not established in this lane; no claim that a ready-made mathlib definition of this exact generic statement exists. An explicit counterexample could avoid most geometry, but none was found. No kernel test was run.

## 333496: nonzero-coefficient Niho classification, incomplete; zero coefficient is a correction
Primary Wu-Li-Zhang-Liu 1606.08952v1, definition via balanced derivatives, Section4 Theorems7/8, Conjecture1. The source itself proves both positive branches. Its cubic necessity uses three separate coefficient cases and Kloosterman-sum input; this is not an all-r proof.

The zero function is negabent: for each a!=0 the derivative test is Tr(ax), a nonzero linear functional, hence balanced. Thus alpha=0 at m=2,r=2,d=7 violates the two-branch criterion (m even and r not 3). This is an omitted-zero-coefficient correction, not a significant discovery. The extracted source prints no alpha!=0 in Conjecture1; visual glyph and final-version reconciliation remain unpaid. I did not promote this trivial literal refutation.

Route 1 (Frobenius classes): Since d=1 modulo q-1, q=2^m, only Frobenius multipliers 2^j with j=0 or m preserve that normalization. Multiplication by q changes r to 1-r modulo q+1. Thus arbitrary new r cannot simply be claimed equivalent to the cubic or quadratic branch. The source's interval selects representatives; its proved branches do not already classify the remaining ones. The m=1 boundary and zero coefficients must be kept separate in any literal formalization.

Route 2 (polar coordinates and ordinary Walsh spectrum): Every nonzero element of F_{q^2} is uniquely u z with u in F_q^* and z^(q+1)=1. This follows since the two orders q-1 and q+1 are coprime. Then x^d=u z^(1-2r), and
 f(uz)=Tr_{q/2}(u C(z)), C(z)=alpha z^(1-2r)+alpha^q z^(2r-1).
For b in F_{q^2}, let N_b be the number of z in this norm-one circle satisfying C(z)+b z+b^q z^-1=0. Summing first over u!=0 gives the exact ordinary Walsh identity W_f(b)=q(N_b-1). Indeed each zero coefficient contributes q-1, each nonzero coefficient -1, and x=0 contributes 1. This is a complete finite character-sum reduction for ordinary bentness. It is NOT the negabent endpoint. Treating N_b in {0,2} as the negabent criterion silently replaces the transform and is wrong. No helper credit.

Route 3 (twisted derivative / quadratic conversion): The actual condition is that f(x+a)+f(x)+Tr(ax) be balanced for every a!=0. For cubic algebraic degree the derivative is quadratic and the source can control its radical and trace. General Niho exponents need not have degree3, so the same linearized-kernel method fails. Adding the elementary symmetric quadratic in self-dual coordinates converts toward ordinary bent theory, but its polar form is Tr(ax)+Tr(a)Tr(x), and its restrictions on norm-one rays are not generally linear in u. Therefore the clean Walsh count above cannot be imported unchanged. Unpaid: classify all remaining nonzero-alpha exponents by finding an unbalanced twisted derivative, or supply a specific exact nonzero-alpha witness outside the branches. No such witness was found personally and no finite search was run.

Significance stress test: source own positive branches and alpha=0 are zero; a genuine nonzero coefficient new exponent would be meaningful if exact and not Frobenius-equivalent. No such result here. Search2 identified the 2018 final still printing this conjecture, but its actual final body was not acquired before the stop; excerpts are navigation only.

Lean: finite fields, finite sums, trace of finite extensions and ZMod exist. A finite witness can state balancedness as exact fiber cardinality for each a, avoiding complex Fourier transforms. The exact negabent/Niho definitions would be authored, not claimed to exist ready-made. A general classification requires substantial finite-field algebra; current kernel capacity is unknown, not a reason for rejection. No Lean executed.

## 358998: decimal prime route parked at a precise infinite gap
Primary 2307.00770v1 Definitions1.3/1.4, Conjecture1, Theorem1.1 and Section7. Definition1.4 explicitly reserves the unqualified word for base10. Prime examples in other bases would be domain corrections, not this target.

The source reduces the question to simultaneous primality of 5*10^m-1 and 5*10^m-3 for m>=4. I checked the converse algebra directly: reversing 49...9 gives 99...94=2(5*10^m-3); additivity at the two distinct odd prime factors yields the requisite equality. This is source-owned, not new.

Route1 modular obstruction: modulo7, 10 has order6. For m=1 mod6, 10^m=3 mod7 and 5*10^m-1=0. For m=2 mod6, 10^m=2 mod7 and 5*10^m-3=0. These are genuine composite values for m>=4 but leave four entire residue classes. No all-m finite covering congruence was constructed. I made no modular enumeration.
Route2 factorization: even or odd m gives scaled squares, but neither 5 z^2-1 nor 50 z^2-1 factors over integers by a geometric-series identity. This does not supply a primality obstruction. A proposed cyclotomic argument must control the factor5 rather than treating the expression as 10^m-1.
Route3 density/heuristic: the source's sum of reciprocal logarithm squares converges, but only under a random-prime model. Even rigorous finiteness would not imply zero. Thus neither that heuristic nor excluding finitely many m settles universal nonexistence. Missing lemma: for every integer m>=4 at least one of the two displayed integers is composite, or one explicit simultaneously prime pair with exact certificates. No such result obtained. The source forward proof was only partially passage-read; it is attributed, not independently reconstructed in full.

Lean: Nat.Prime, Nat.digits and factorization exist; reversal and v can be defined finitely. The literal nonexistence is an unbounded quantifier over naturals, not a finite computation. The source-characterization bridge must be formalized rather than assumed. No kernel run and no novelty clearance.
