# Independent review round 1: posterior critical wave process (PCW)

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT.
Third-party sources retain their rights and are private reading material.

## Verdicts

* **Mathematics: PASS_FULL_PCW.** The frozen author proof
  (`inputs/author/candidate.md`, SHA256 fd178b51…f1a1, sealed by author
  anchor 49b43b21…c9b4) proves the unchanged frozen target
  (`inputs/author/original-scope.md`, SHA256 229749a9…3391) for every d>=3,
  every finite vertex tuple, every finite T, in C([0,T],R^F) with the
  uniform topology, for both h and m, including time 0. Every new deduction
  was re-derived independently below. No required repair was found. The
  optional clarifications in Section 9 are expository; none changes a
  statement, constant, rate or quantifier, and none was applied to the
  frozen bytes.
* **Contribution: TECHNICAL.** The proof is a complete and careful
  combination of established operations: the Yu–Polyanskiy perturbative
  second/fourth moment normal form (same coefficient (b-1)/b), the
  Jain–Koehler–Liu–Mossel / Janson–Mossel style replacement of a weakly
  tilted planted array by an independent one, the classical continuous
  martingale functional CLT with a deterministic bracket limit, the
  Nam–Sly–Zhang Brownian observation posterior, and Elon's spectral-edge
  Gaussian wave covariance. The increasing-depth whole-path replacement is
  correct but short and elementary (absolute-sum linearization, a product
  total-variation telescoping bound, one logarithmic choice of depth). It is
  not a substantial new mechanism. Not DUPLICATE: no read primary body or
  pinned blob states the PCW process limit. This is a bounded observation,
  not a novelty certificate. Details are in `operation-comparison.md`.

Counted=false. Campaign count stays 4/10. Integrity verification (Section 10)
is not evidence of mathematics or novelty. B8C and crossing tracks are
separate and untouched.

## 1. What was authenticated and read

Before any reliance, the author guard was inspected in full and run with
the external anchor: `python3 -B guard.py --verifier-sha256 535f514b…dbb2
--anchor 49b43b21…c9b4 --controls` reported VERIFIED, exactly 51 files and
11 directories excluding root, 15 pinned blobs, and 12 passing negative
controls. A wrong (all-zero) anchor was rejected with "external seal anchor
mismatch". No bytecode was created. The verifier source (535f514b…dbb2)
and guard (f938351b…2560) were read fully before execution. No historical
mathematical program was run.

The complete candidate (474 lines), scope, checkpoints, screening record,
source contracts, author reading log and author operation comparison were
read, as were the complete original discovery brief (643 lines, SHA256
97d8e33d…aa79, including its historical appendices) and the complete
review brief (905 lines). Exact extents of source and primary reading are in
`source-reading.md`. Source theorem truth at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb is stipulated on exact interfaces
only; it was not audited.

## 2. Source interfaces actually used (P1 inputs)

Checked against the pinned TeX (`inputs/pinned/`):

1. `02-posterior-fields.tex` (all 282 lines): free law, Gaussian
   observation likelihood, `lem:posterior` cavity recursion
   h_v = X_v + sum_(w~v) psi(h_(w->v)), component recursion with b terms,
   psi(z)=atanh(theta tanh z), field bounds |h_(v->w)-X_v|<=b beta and
   |h_v-X_v|<=d beta.
2. `04-innovations.tex` 589–603: continuous versions are posteriors for the
   usual filtrations; "applied instead to tanh h_(v->w) and the raw component
   filtration, the argument gives the corresponding assertion for its usual
   augmentation", including time zero, starting at zero. Hence
   M_v = tanh h_(v->w) is a bounded continuous martingale in the augmented
   filtration of the component observations only. The candidate never uses
   it as a martingale in the full-tree filtration (P1 requirement).
3. `08-critical-comparison.tex` 1–59, `lem:critical-tail`: at theta=b^(-1/2),
   b>=2, there are K, t_0 depending on d with E|h_(v->w)(t)|^p<=e^(Kp^2)t^(p/4)
   for every integer p>=1 and 0<t<=t_0, also conditionally on either spin of
   the component root or of the deleted neighbor. This is the candidate's
   (1.2); only p<=6 is used.
4. `03-critical-information.tex` 1–300: the scale M(t)<=C sqrt(t) and the
   root/neighbor tilt identities at fixed times. The candidate re-derives
   the tilt it needs and determines the leading constant itself.

The pinned family contains no Gaussian process limit: a grep of all 15
pinned/companion blobs for "Gaussian", "wave", "central limit",
"invariance principle" and "functional limit" finds only the Gaussian
observation model and Gaussian attenuation estimates. The theorem/lemma
headers of the unread sections 05–07 were listed; they concern coupling,
spectrum and path-average concentration for the factor-of-IID proof.

## 3. P1: filtrations, versions, observations and whole-history tilt

*Claim (candidate 106–127).* For a component C=T_(v->w), O_C^s all
component observations through s, nu_s its law, and bounded measurable f,
E[f(O_C^s)|sigma_v=eta]=E[f(O_C^s)(1+eta M_v(s))], and conditioning on the
excluded neighbor spin gives density 1+eta theta M_v(s).

*Independent check.* The observation array is a countable product of
C[0,s] spaces, hence Polish, so regular conditional laws exist.
P(sigma_v=eta|O_C^s)=(1+eta M_v(s))/2 because M_v(s)=E[sigma_v|O_C^s]
(item 2 above, applied at the terminal time s of the history). Then
E[f 1_(sigma_v=eta)]=E[f (1+eta M_v(s))/2], and P(sigma_v=eta)=1/2. The
density concerns the whole history sigma-field O_C^s, not only M_v(s). The
neighbor version: sigma_w is conditionally independent of
(sigma_C, Brownian motions in C) given sigma_v, because v separates w from
C\{v} in the tree, and E[sigma_w|sigma_v]=theta sigma_v. Hence
E[sigma_w|O_C^s]=theta M_v(s). Both identities are correct.

*Path measurability.* The continuous version of M_v on [0,s] is a
measurable function of the completed O_C^s. Section 5 pushes forward under
two laws (actual planted, and nu_s^N). The actual law has density at most
2^N with respect to nu_s^N, so it is absolutely continuous. A path map
defined nu_s^N-a.s. is therefore also defined a.s. under the actual law.
The candidate states path measurability (119–121) but not this absolute
continuity; see clarification C1. It is implied by the displayed densities.

*Conditional independence with an explicit cut sigma-field.* Section 5
conditions on the level-n spin vector eta, and Section 6 on the spins at
the boundary roots y. In each case the conditioned vertices separate the
disjoint components from each other and from the rest of the tree. By the
tree Markov property and independence of the Brownian motions, the
component histories are conditionally independent, each depending only on
its own root spin. This is the correct sigma-field (P1 requirement).

*Uniform path moments (2.1)–(2.2).* Doob's L^p inequality for the bounded
martingale M and |tanh z|<=|z| give E sup_(r<=s)|M(r)|^p<=C_p s^(p/4). On
{sup_(r<=s)|X_v(r)|<=1}, sup|Y|<=1+b beta, so |Y|<=C|tanh Y| there. On the
complement (which for s<=1/2 requires sup|B_v|>1/2) the field bound
gives sup|Y|<=sup|X_v|+b beta, whose p-th moment restricted to an event of
probability <=4exp(-1/(8s)) is O(exp(-c/s)) by Cauchy–Schwarz and the
reflection principle. This proves (2.1) for every fixed integer p>=2, and
p=1 follows. The site field obeys sup|h_v|<=sup|X_v|+theta sum_(w~v)
sup|h_(w->v)| (|psi(z)|<=theta|z| since 0<psi'<=theta), giving (2.2). All
constants depend only on d, p (and T after rescaling). **P1: verified.**

## 4. P2: scalar recursions and remainders

Fix t, write Y=h_(v->w)(t), Q=E Y^2, R=E Y^4, a=E[tanh Y psi(Y)],
k=E psi(Y)^2. By (1.2), Q=O(t^(1/2)), R=O(t), E Y^6=O(t^(3/2)).

*Conditional structure.* Given the component-root spin +1, the b child
fields Y_i=h_(u_i->v) are independent with density 1+theta tanh y relative
to the symmetric law of Y (neighbor tilt of Section 3). The own observation
Z_0=X_v(t) is independent of them with law t+sqrt(t)Z. Even moments of Y are
unchanged by the conditioning (E[Y^(2j) tanh Y]=0 by symmetry), so Q and R
are also the conditional moments.

*Taylor bounds.* tanh y=y-y^3/3+O(y^5); atanh x=x+x^3/3+O(x^5); hence
psi(y)=theta y-theta(1-theta^2)y^3/3+O(y^5),
psi^2=theta^2y^2-(2/3)theta^2(1-theta^2)y^4+O(y^6), psi^4=theta^4y^4+O(y^6),
tanh(y)psi(y)=theta y^2+O(y^4). Globality: psi and tanh are bounded, so for
|y|>=1 the displayed polynomial right sides dominate after enlarging
constants. Verified.

*Odd conditional moments (3.1).* E[psi(Y_i)^j|+]=theta E[tanh Y psi(Y)^j]
for odd j, which is O(E|Y|^(j+1))=O(t^((j+1)/4)). Verified.

*Fourth moment (3.3).* Expand (Z_0+sum Z_i)^4 under the conditional product
law. One-child: b E psi^4=b theta^4 R+O(t^(3/2))=R/b+O(t^(3/2)).
Pattern 2+2: multinomial 6 per unordered pair, b(b-1)/2 pairs, giving
3b(b-1)k^2, and k^2=theta^4Q^2+O(t^(3/2)), so 3(b-1)Q^2/b+O(t^(3/2)).
Pattern 3+1: O(t)·O(t^(1/2)); 2+1+1: O(t^(1/2))^3; 1+1+1+1: O(t^2).
Own-observation terms: 4E Z_0 E(sum Z_i)^3=t·O(t)
(E(sum Z_i)^3=bEZ^3+3b(b-1)EZ^2EZ+b(b-1)(b-2)(EZ)^3=O(t));
6E Z_0^2 E(sum Z_i)^2=(t+t^2)O(t^(1/2)); 4E Z_0^3 E sum Z_i=(3t^2+t^3)O(t^(1/2));
E Z_0^4=3t^2+6t^3+t^4. All O(t^(3/2)). Hence (1-1/b)R=3(b-1)Q^2/b+O(t^(3/2)),
R=3Q^2+O(t^(3/2)). Verified, including the moments of Z_0 listed at line 173.

*Second moment (3.4).* Q=E Z_0^2+2E Z_0·b E Z_i+b E Z_i^2+b(b-1)(E Z_i)^2
=t+t^2+2bt theta a+bk+b(b-1)theta^2a^2. The child mean is theta a, not a:
verified. (This extra factor matches the (1-2delta) factor in Yu–Polyanskiy
Lemma 3's E[R^2]=dE F^2+d(d-1)((1-2delta)E F)^2.)

*Normal form (3.5).* With a=theta Q+O(t), k=theta^2Q-(2/3)theta^2(1-theta^2)R
+O(t^(3/2)) and b theta^2=1: 2bt theta a=2tQ+O(t^2)=O(t^(3/2)); bk=Q-(2/3)(1-1/b)R
+O(t^(3/2)); b(b-1)theta^2a^2=(b-1)Q^2/b+O(t^(3/2)). Cancelling Q and inserting
R=3Q^2 gives 0=t-2(b-1)Q^2/b+(b-1)Q^2/b+O(t^(3/2))=t-(b-1)Q^2/b+O(t^(3/2)).
So Q^2=kappa^2 t+O(t^(3/2)) with kappa^2=b/(b-1), and since Q>=0,
|Q-kappa sqrt t|<=C t^(3/2)/(kappa sqrt t)=O(t). Then
|q-Q|<=C E Y^4=O(t). Verified.

Cross-check against the antecedent: with full LLR R'=2Y, Yu–Polyanskiy's
(21) reads (d(1-2delta)^2-1)E R'^2=((d-1)/(4d))(E R'^2)^2. In half-LLR units
this is (perturbation)·Q=((d-1)/d)Q^2. PCW's forcing gives t=((b-1)/b)Q^2.
The quadratic coefficient is the same; only the linear forcing term differs.

*Uniformity to time 0 (3.7).* The remainders hold with one constant on
(0,t_0], q(0)=0, and for epsilon T<=t_0,
|epsilon^(-1/2)q(epsilon t)-kappa sqrt t|<=C epsilon^(1/2)t uniformly on
[0,T]. **P2: verified.**

## 5. P3: the independent averaging lemma

*Statement (candidate 212–226).* L_epsilon continuous square-integrable
martingale from 0, E sup|L_epsilon|^4<=C, E L_epsilon(t)^2->a(t) uniformly,
a continuous nondecreasing with a(0)=0; N(epsilon)->infinity independent
copies with their own filtrations; then N^(-1/2)sum L_(epsilon,i)=>B(a(.)).

*Independent proof.* (i) In the product filtration each copy remains a
martingale (independence), and for i!=j, L_i L_j is a martingale: for
F_i in the past of copy i and F_j in the past of copy j,
E[L_i(t)L_j(t)1_(F_i)1_(F_j)]=E[L_i(s)1_(F_i)]E[L_j(s)1_(F_j)], and such
rectangles form a pi-system generating the product past. So
<L_i,L_j>=0 and <S>=N^(-1)sum A_i, A_i=<L_i>. (ii) L^4 BDG:
E A_i(T)^2<=C_4 E sup|L_i|^4<=C'. (iii) E A_i(t)=E L(t)^2 and
Var <S>(t)<=C'/N. (iv) Choose a grid 0=t_0<...<t_m=T with
a(t_(j+1))-a(t_j)<=delta. By Chebyshev and (4.1), max_j|<S>(t_j)-a(t_j)|->0
in probability. For t in [t_j,t_(j+1)], monotonicity gives
<S>(t)-a(t)<=<S>(t_(j+1))-a(t_(j+1))+delta and the symmetric lower bound.
Hence (4.3). (v) Extend S beyond T by an independent Brownian motion,
so <S>(infinity)=infinity; Dambis–Dubins–Schwarz gives a standard Brownian
W_epsilon with S(t)=W_epsilon(<S>(t)). (vi) On the event
sup|<S>-a|<=eta_epsilon with eta_epsilon->0 slowly, both clocks lie in
[0,a(T)+1], and |S(t)-W_epsilon(a(t))|<=omega(W_epsilon,eta_epsilon) on
[0,a(T)+1]. Because every W_epsilon is standard Brownian, the law of this
modulus does not depend on epsilon and it tends to 0 in probability. No
independence of W_epsilon from the clock is used. W_epsilon(a(.)) has the
law of B(a(.)) for every epsilon, so S=>B(a(.)) in C[0,T], with tightness at
the singular point t=0 included (a(t)=kappa sqrt t is not Lipschitz there,
and none is needed). This is the special continuous-path case of the
triangular martingale FCLT (Whitt, arXiv:0712.1929, Theorem 2.1 with
deterministic limit bracket; Ethier–Kurtz 7.1.4). **P3: verified.**

*Application (4.4).* L_epsilon(t)=epsilon^(-1/4)M(epsilon t) is a martingale
in the time-rescaled component filtration. E sup|L|^4=epsilon^(-1)
E sup_(r<=epsilon T)|M|^4<=C T by (2.1), and E L(t)^2=epsilon^(-1/2)q(epsilon t)
->kappa sqrt t uniformly by (3.7). Limit B(kappa sqrt t), equal in law to
sqrt(kappa) B(sqrt t).

## 6. P4: one increasing depth, two errors

*Expansion (5.1)–(5.3).* The all-time component recursion gives
Y_u=X_u+sum_z psi(Y_z), with e_u=sum_z(psi(Y_z)-theta Y_z). Globally
|psi(y)-theta y|<=C|y|^3 (cubic near 0; for |y|>=1, |psi(y)-theta y|<=beta+theta|y|).
So ||e_u||_(L^2(C[0,s]))<=bC(E sup|Y|^6)^(1/2)<=C s^(3/4) by (2.1) with p=6.
Iterating n levels gives the displayed identity (verified by induction).
The triangle inequality, with b^j vertices at level j and weight theta^j,
gives sum_(j<n) b^(j/2)(||X||+||e||)<=C sqrt(N)(sqrt s+s^(3/4)); no
independence is used. Replacing leaf Y_u by M_u costs
theta^n·N·C s^(3/4)=C sqrt(N) s^(3/4). With s=epsilon T and the factor
epsilon^(-1/4): C_T sqrt(N) epsilon^(1/4) (5.3). Constants come only from
single-coordinate bounds and do not depend on n, epsilon or the vertex.

*Dependence (5.5).* Conditional on level-n spins eta, the leaf histories
are independent with densities 1+eta_u M_u(s) relative to nu_s (Section 3).
TV(mu,nu)=(1/2)E_nu|M(s)| for one factor, and
TV(prod mu_u, prod nu)<=sum_u TV(mu_u,nu) by telescoping. E|M(s)|<=E|Y(s)|
<=C s^(1/4). Averaging over the actual (correlated) law of eta is a mixture,
and TV is convex. The bound C N (epsilon T)^(1/4) refers to the actual
planted law of the N leaf histories. Pushforward to the rescaled leaf M
paths does not increase TV (with C1 for a.s.-defined maps).

*Single depth.* n=floor(log_b(1/epsilon)/8), N=b^n in
(epsilon^(-1/8)/b, epsilon^(-1/8)], so N->infinity, sqrt(N)epsilon^(1/4)
<=epsilon^(3/16), N epsilon^(1/4)<=epsilon^(1/8). Both errors use the same
n(epsilon); the lemma is applied with this N(epsilon) and with the
epsilon-dependent summand law. No fixed-depth limit is taken.

*Conclusion (5.6).* Let S^act=N^(-1/2)sum_u epsilon^(-1/4)M_u(epsilon .) under the
actual law and S^ind the same functional of N independent nu_s histories.
d_TV(S^act,S^ind)->0, S^ind=>H by Section 5, and the rescaled Y_o differs
from S^act by o(1) in L^2(C). Hence the rescaled Y_o=>H=sqrt(kappa)B(sqrt .).
The M_o version follows from |y-tanh y|<=C|y|^3 and (2.1).
**P4: verified.**

## 7. P5: finite hull, joint law, covariance and time 0

*Expansion (6.1).* For connected finite K, each internal message
h_(w->v) with w in K expands by the cavity equation over the forward part
of K; recursion terminates at outward edges. Each linearization discards
psi(Y)-theta Y for an actual cavity field Y (same process law as the
component field), bounded by C s^(3/4) in L^2(C). X_x receives
theta^dist(v,x), boundary Y_e receives theta^dist(v,x)·theta=theta^dist(v,y).
The number of terms depends only on K. Verified.

*Boundary decoupling.* Conditional on all boundary-root spins sigma_y,
the outward histories are independent, each with density 1+sigma_y M_e(s)
(Section 3). TV to the product of unconditional laws is
<=C|partial K|(epsilon T)^(1/4). Under the product law each rescaled Y_e
converges to an independent copy of H by (5.6), so the boundary vector
converges jointly. The own terms are O(epsilon^(1/4)) and R_v=O(epsilon^(1/2))
in L^2(C) after rescaling. The linear map to (h_v)_(v in K) is continuous on
C[0,T]^(partial K), so (6.2) holds jointly in C([0,T],R^K) and then for any
sub-tuple. Verified.

*Covariance (6.3)/(7.1).* E H_e(s)H_e(t)=kappa sqrt(min(s,t)).
Leaf-addition invariance: replacing outward edge (x,z) by z's b outward
edges multiplies its contribution by b theta^2=1. Any connected K
containing u,v reduces to the u–v path by pruning leaves. On a path of n>=1
edges: 2b outward edges at the endpoints, b-1 at each of n-1 interior
vertices, each exponent n+2, so S=[2b+(n-1)(b-1)]theta^(n+2)
=[(b+1)+(b-1)n]b^(-n/2)/b=(b+1)phi(n)/b; n=0 gives (b+1)/b. Then
kappa(b+1)/b=(b+1)/sqrt(b(b-1))=d/sqrt((d-1)(d-2))=A_d, and
phi(n)=(1+(d-2)n/d)(d-1)^(-n/2)=phi_d(n). Verified. The recurrence
phi(n-1)+b phi(n+1)=2 sqrt(b) phi(n) and d phi(1)=2 sqrt(b) phi(0) were
checked by hand; they identify Elon's lambda=2 sqrt(b) wave (Elon's Lemma 2.2
with U_(-1)=0 convention).

*Existence and consistency.* Finite-tuple laws are continuous centered
Gaussian with covariance A phi(dist) sqrt(min(s,t)), PSD by the hull
representation, consistent under restriction because the covariance is
hull-independent. Kolmogorov's extension on the countable product
(C[0,T])^V gives the process. Time 0: G(0)=0, and the averaging lemma gives
uniform-topology convergence on [0,T] including 0.

*Field to magnetization.* |h-tanh h|<=C|h|^3 and (2.2) give an L^2(C) error
C_T epsilon^(1/2). All d>=3 (b>=2, so kappa finite) and every finite tuple
(repetitions trivial) are covered. **P5: verified.**

## 8. Scope check

The proved statement is exactly the frozen PCW: process convergence in
C([0,T],R^F), uniform topology, every finite tuple and T, both m and h, the
stated covariance including the sqrt(min(s,t)) time structure and time 0,
under the actual planted law with common Brownian observations, plus
existence/consistency of the limit. No strict temperature, subsequence,
positive-time cutoff, finite-dimensional-time reduction or resampling was
inserted. Every premise from the source matches an exact pinned interface.

## 9. Optional clarifications (not repairs; frozen bytes unchanged)

* **C1 (Section 5, 119–121, 326).** State explicitly that the actual leaf
  history law has density prod_u(1+eta_u M_u(s)) averaged over eta, at most
  2^N, with respect to nu_s^N. Then the a.s.-defined continuous path maps
  push forward consistently. Already implied by (5.5)'s densities.
* **C2 (Section 6, 376–377).** Replacing boundary Y_e by M_e is
  unnecessary, since (5.6) is already proved for Y. It is harmless.
* **C3 (Section 4, 236).** "Its mean is E L(t)^2" uses that L is a
  square-integrable martingale from 0, so E<L>(t)=E L(t)^2. True under the
  stated assumptions.
* **C4 (Section 2.1, 92–94).** The complement estimate needs the field bound
  sup|Y|<=sup|X_v|+b beta and Cauchy–Schwarz against the event probability.
  The proof says this in words; the constant is routine.

None of these is a mathematical deficiency.

## 10. Integrity statement

This package's verifier (`verify.py`) authenticates the detached seal
against an externally supplied anchor before parsing anything, then checks
exact file and directory membership, safe unique paths, no symlinks or
bytecode, all sizes/hashes, the copied author files against the author
manifest and seal, pinned copies against their Git blob identities, and the
before/after receipts for the external fixed inputs. Integrity is not
mathematics.
