# I114 — Fresh quantum-information discovery

**Disposition: developed gap record; no substantial finding nominated.** Four exact targets were screened. The selected target is quantitative stability of the multimode constrained entropy minimum for a thermal attenuator at unequal input and bath temperatures. Two routes were developed. They yield the complete technical estimates B114 and Q114 below, but do not prove the selected theorem. That theorem remains **unproved and unrefuted**. The eight accepted findings stay eight.

All theorems **and lower proof operations** of `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted premises. No upstream truth audit or contradiction synthesis is performed. New claims here have author proofs, not independent-review acceptance. The parent owns integration and any future reviews. No children, shared edits, staging, commits, or publication were performed.

## 1. Scope and source/version checks

The four ledgers, AGENTS.md, complete preprint tree, catalogue, I39 and I110 are frozen under `../sources/i114_quantum_information_discovery/snapshots/`. The ledger reading included the accepted-count table, current dispositions and quantum-related entries; the full long historical ledgers were frozen, not represented as fully semantically read. The ledger's link to I07 led to reading its complete parent quantum screen. That older screen is crucial: it already excludes both GAD strong converse and conditional EPnI. I39 actually concerns Haldane disorder, SK entropy/waiting times, and PEPS algorithmic interfaces. It does not subsume quantum information as a whole. R009's reconstruction capacity is classical tree reconstruction; R012–R014's Gaussian/geometric entropy work is not bosonic channel stability. I110's technical closure and parked cancellation do not supply an entropy argument. No I112/I113 working output is bound or used.

The search domain is the complete I88 mapping: **10,373 original blob positions**, comprising the **9,340** reused I14 originals and **1,033** additional I79 positions, of which **776** have PDF text views and **257** have other byte views. The complete tree has **13,223 entries and 749 manuscript directories**. Exact expressions, every occurrence (including duplicates), original/text mappings and line conventions are retained. This is a full-domain **lexical search**, not full semantic reading. Neither recursive corpus copying nor whole-corpus downloading was done. The topic expression has 98 occurrences; the deliberately broad stability expression has 143. The zero-key lead was separately selected by its exact title, rather than pretending the topic expression covered it. The full-tree title pass checks all versions of the selected families.

Selected pinned identities and exact read passages are in `selected-inventory.json`, `read-manifest.json` and `passages.json`. Each includes or references the original SHA-256 and Git blob, text-view SHA-256 and exact pinned URL. Source and derived-text line numbers use Python UTF-8 `decode(errors="replace").splitlines()`; byte LF counts are recorded separately and are not substituted for those numbers. No PDF was newly downloaded or re-extracted. Existing PDF text views were searched as views and are independently bound to their immutable PDF originals; extraction completeness is not claimed. New primary sources use versioned HTML, with MathML `alttext` preserved in deterministic text views.

Four fresh pinned introduction responses match their reused originals byte for byte. The same four paths fetched from current `main` also match; they are observations, not substitutes for the pinned premises. The complete pinned tree has one manuscript directory for each of the five requested leads. Current-version checks produced an important correction: Fang's September v1 only bounds capacity, but **v2, revised October 6**, proves the exact strong-converse exponent. The v1 response and this correction are both retained. No positive candidate relies on the obsolete v1 description.

The primary comparison includes:

* **EP:** [pinned EPnI manuscript](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-entropy-photon-number-inequality-September-24-2026/build/sections/00-introduction.tex), `thm:epni`, `cor:thermal-attenuator`, and complete §§1–5 operations. It admits arbitrary entanglement among modes of either input, but independent input ports, finite n, and finite total energy. Thermal attainment is asserted; uniqueness is explicitly not asserted. Its four-weight interpolation, Gibbs minimization, metric and stationarity proofs were read through their endings.
* **AD:** the pinned GAD `paper.tex`, `cor:partner-additivity`, and full thermal, output and partner proofs. It already allows arbitrary finite-dimensional CPTP partners for Holevo information, minimum output entropy and regularized classical capacity. The partner can retain its own regularization.
* **PR:** the pinned repetition `thm:main`, full `04-threshold.tex` and `05-root-support.tex`. Its dimension- and question-alphabet-independent rate is κ₀δ⁵/(1+log d); its second rate is δ³/[16384(1+κ_μ)(1+log d)]. These concern i.i.d. question pairs and tensor-product finite-dimensional strategies, with a supremum over all finite dimensions, not a dimension cap or a commuting-operator theorem.
* **US:** the pinned synthesis main theorem and full field, encoder, recursion and compilation operations. The lower construction already controls clean-workspace operator error for coherently labelled families. The oracle is target-dependent, with unrestricted truth-table/classical construction cost.
* **ZK:** the zero-key introduction and complete channel-completion proof. The source already supplies a represented class closed under tensor powers, admitted countable/public-transcript protocols, public conditioning, and a trace-preserving 21-dimensional PPT channel whose square has an entangled corner. Merely flagging the dimension-ten example or tensoring it is spent work; no new protocol-model theorem is inferred.

External primary sources are distinguished from stipulated premises. [Li, 2609.40061v1](https://arxiv.org/html/2609.40061v1), §§3.1–3.4 and Appendix A.4, supplies a specific thermal-channel instrument used below, and an equality theorem for linear/exponential qEPI. [Cuesta, 1902.05298v1](https://arxiv.org/html/1902.05298v1), Theorem 9 and its quantitative proof, concerns approximate **product outputs**, assumes finite moments of all orders and has constants depending on second/fourth absolute moments; its state conclusion is Hilbert–Schmidt, not trace norm. These facts prevent importing a finite-energy, mode-uniform EPnI rate. Its full theorem is not independently certified here. [Fang, 2609.14621v2](https://arxiv.org/html/2609.14621v2), Theorems 1, 3, 4 and Appendix A, supplies the exact channel duplicate discussed below; its relevant proofs were read through their endings, without claiming an external proof audit.

Significance is tied to the **entropy photon-number conjecture and constrained minimum output entropy problem**, not to an invented ranking. The [QIQCOP problem page](https://qiqc-op.com/problem/op_ba39e7a80122b256/) records precisely the independent finite-energy multimode problem and its communication consequences, and records the OpenAI report while retaining its own catalog status. The pinned introduction attributes the problem to Guha–Erkmen–Shapiro and explains the constrained-entropy/broadcast interface. Our accepted-premise convention does not change that external catalog. No specific MathDB ranking is asserted.

## 2. Four exact targets and the screening decisions

### B — power stability of an unequal-temperature constrained minimum (selected)

Let H_n=ℓ²(N₀ⁿ), N=Σa_j†a_j and

τ_r=(r+1)^(−n)(r/(r+1))^N,   g(r)=(r+1)log(r+1)−r log r.

Let T_{η,b} be the n-mode tensor power of a thermal attenuator with **independent** environment τ_b, identical transmissivity η in every mode, and arbitrary n-mode input. All entropies are in nats, and ||·||₁ is unhalved.

**Target B:** for every integer n≥2 there is α_n>0 such that for every r,b>0 with r≠b, every 0<η<1 and finite E>nr, there is C=C(n,E,r,b,η)<∞ for which every centered state ρ with

Tr ρN≤E,   Tr ρa_j=0 (all j),   S(ρ)=ng(r)

satisfies

||ρ−τ_r||₁ ≤ C [S(T_{η,b}(ρ))−ng(ηr+(1−η)b)]^α_n.                 (B)

The bracket Δ is nonnegative by EP. The exponent is permitted to depend on n, while the constant sees all the other displayed parameters. No endpoint, uniform-in-n, or uniform-as-E→∞ estimate is claimed. Target B would in particular identify every centered exact optimizer. It is **a target, not a theorem**.

For an uncentered input use D(−μ)ρD(μ), μ_j=Trρa_j. This leaves both entropies and Δ unchanged, reduces energy by |μ|², and asks for closeness to the thermal state displaced by the input's own mean. There is no independence assumption across its n modes. Fixing the isotropic thermal environment matters: arbitrary common symplectic transformations are symmetries of the *two-free-port* inequality but change this fixed environment unless passive. The extremal family in B is therefore displaced isotropic product thermals, not all Gaussian states. At r=b the linear equality literature becomes relevant, but B deliberately retains the unequal-temperature obligation. At E=nr the Gibbs entropy-energy equality already forces τ_r; E>nr is the nontrivial regime.

### C — all-code GAD exponential strong converse (rejected: exact current duplicate)

This paragraph measures capacity, Rényi information and rates in bits, with a base-2 exponent; conversion to e^(−ck) multiplies the exponent by log 2. The screened claim was: for every 0<γ,ν<1 and R>C(A_{γ,ν}), there are c>0 and k₀ such that every k-use unassisted classical code of at least 2^(kR) equiprobable messages, allowing entangled inputs and collective decoding, has success ≤e^(−ck) for k≥k₀.

Fang v2 Theorem 1 proves more: all orders α>1 have additive sandwiched Rényi Holevo information and the exact limiting exponent is sup_{α>1}(α−1)/α [R−χ̃_α(A)]. The proof uses triangular Schatten compression, multiplicativity after arbitrary positive diagonal sandwiches, phase-covariant diagonal reference states, then the information radius. This is an exact full-scope reduction, not an inference from ordinary Holevo additivity. I07 had already rejected it. We retain no C nomination. This is a current **author theorem** comparison, not an independent acceptance of its proof.

### G — a universal cubic threshold exponent (unresolved screen, not selected)

The precise target is existence of one numerical c>0 such that for every finite two-player one-round game G with Boolean acceptance predicate, v=ω*(G)<1, d=|A||B|, every 0<δ<1−v and k≥1, and every finite-dimensional tensor-product joint strategy for k independent repetitions,

Pr[W_k≥ceil((v+δ)k)] ≤ exp[−cδ³ k/(1+log d)].                  (G)

The same bound would pass to the unrestricted finite-dimensional supremum. It would not imply a commuting-operator version. PR already proves universal fifth-power and fixed-law cubic bounds. Its full conditioning-to-threshold transfer takes an error Bτ^β to rate of order δ^(1+1/β). Thus obtaining G by this transfer requires **uniform square-root** conditioning control; simply rerunning Song's τ^(1/4) estimate gives δ⁵. The root-state construction supplies square-root control only with κ_μ, which diverges as support masses vanish or support paths lengthen. Replacing a root by a weighted graph mean might improve κ_μ to an inverse gap, but that still permits unbounded constants. It does not pay a universal cubic rate.

Song's all-win cubic estimate is a different event and uses an extra near-perfect-success step; the pinned source explicitly separates that operation from its generic conditioning lemma. We do not silently substitute all-win amplification for threshold amplification. No new sampling lemma or distribution-independent quantum rounding was established here. Current Song search results were used for orientation; the SSRN direct request failed, and no claim of a complete new Song proof audit is made. All comparisons required for the above quantified obstruction are explicit in the accepted PR operations.

### S — polylogarithmic precision in uniform Boolean-oracle synthesis (rejected: paid by lower operations)

The target was a deterministic generator, given 1^n and an integer precision k≥1, of one circuit over H,T,T†,CNOT and a single Boolean oracle, with qubits, gates, calls, address length and generation time poly(n,k), such that **for every** U∈U(2^n) **some target-dependent oracle** yields full diamond error ≤2^(−k), coherently with clean-workspace comparison before discarding ancillas. There is no bound on computing or explicitly listing the oracle.

Here is a concrete reduction, rather than just the phrase “error reduction.” The source has contraction r₀=3/4, M=4096(n+1)² and fewer than J=8M(n+1) levels. Choose integer L with

18J(3/4)^L ≤ ε/4,   ε=2^(−k).

Then L=O(k+log(n+1)). Its fields/encoders permit every integer L≥1, with h=ceil(log₂(L+1)), b=nL+h, K=b(L+1). Summing the actual one-recursive-call costs gives

Q=O(J(K+n+h)),  S=O(J[L(K+n+h)+K+n])

qubits and slots, with clean operator error ≤ε/4. Each field row still has at most L input columns: the integer power-sum multiset encoding has modulus exceeding L2^(nL). No register-size cost is omitted.

For compilation the source's proof, before its deliberately loose ξ^(−3) final bound, establishes net refinement e_{j+1}≤C₀e_j^(3/2), ℓ_{j+1}≤5ℓ_j. Start with its fixed net sufficiently fine that b₀=C₀²e₀<1. Induction gives C₀²e_j≤b₀^((3/2)^j). Therefore a word of accuracy ξ has length O((1+log(1/ξ))^κ), κ=log(5)/log(3/2). This uses precisely the already-proved commutator recursion. Choose per-slot error ξ=ε/[4(S+1)]. The source's phase-sensitive two-word lookup and ideal-prefix telescoping give total compilation error ≤ε/4. Its address has O(Q+log(S+1)+log(ℓ+1)) bits; each lookup uses polynomially many exact reversible gates. Word choices reside in the oracle, so the uniform generator need not find them. Total clean operator error is ≤ε/2 and the pure-vector trace bound gives full diamond error ≤ε, even with an external reference. The construction is block diagonal in any supplied label, so coherent relative phases are retained.

This proves S at author level **as a technical consequence of accepted source operations**, without a new mechanism. The oracle's truth table can still have 2^poly(n,k) bits. A current random-oracle lower bound, [Huang–Ramkumar–Wright 2610.06700v1](https://arxiv.org/abs/2610.06700v1), addresses a different oracle quantifier and is not used as a contradiction. No efficient oracle-generation result is claimed.

## 3. Route I: a quantitative thermal-balance construction

EP §5 identifies thermal limits from exact number-basis recurrences. We paid a stable version on the full infinite Fock space. It controls a specified defect, rather than asserting that entropy deficit already controls that defect.

### B114: stable thermal balance under a uniform energy cap

For fixed n≥1, r>0 and any state ρ with TrρN≤E<∞ define

R_j=(r+1)a_jρ−rρa_j,
ε_R²=Σ_j||R_j||₂²,
t=[2/(2r+1)]^(1/2) ε_R,
C_r,n=((2r+1)/(r+1))^n.

These are ordinary Hilbert–Schmidt norms; R_j are in fact trace class by finite-energy factorization. Put c=Tr(ρτ_r)/Tr(τ_r²). Then

0≤c≤C_r,n,   ||ρ−cτ_r||₂≤t.                                  (1)

For every integer K≥0,

||ρ−τ_r||₁ ≤ 2 sqrt(binomial(K+n,n)) t
                 +4[√E+C_r,n√(nr)]/√(K+1).                    (2)

In particular, for 0<t≤1,

||ρ−τ_r||₁ ≤ [2^(1+n/2)+4√E+4C_r,n√(nr)] t^(1/(n+1)).         (3)

For t=0 the left side vanishes; in all cases it is also ≤2. Constants are explicit, fixed-mode, and not uniform in energy or mode count. No faithfulness, mode-product form, or higher moment is needed for (1)–(3).

**Proof of (1).** Vectorize Hilbert–Schmidt matrices in the number basis, |p><q|↦|p>⊗|q>. On the resulting 2n-mode space define

D_j=(r+1)a_j⊗I−rI⊗a_j†,
E_j=(r+1)I⊗a_j−ra_j†⊗I.

Their commutators are [D_j,D_k†]=[E_j,E_k†]=(2r+1)δ_jk, with all cross annihilator and cross annihilator/creator commutators zero. They are a finite-mode two-mode squeezing transform of the usual annihilators: write tanh θ=r/(r+1), so cosh θ=(r+1)/√(2r+1), sinh θ=r/√(2r+1). For U(θ)=exp[θ(a_j b_j−a_j†b_j†)] on each mode pair, conjugation U(θ)†a_jU(θ) implements the first formula, and similarly for b_j. Differentiating gives the two coupled linear equations u'=−v†, (v†)'=−u and their cosh/sinh solution. Equivalently this is the standard finite-dimensional symplectic transformation in the Schrödinger representation. Its transformed oscillator number operator therefore has spectrum {0,1,2,...} and a one-dimensional vacuum. Hence, as closed quadratic forms,

Σ_j(D_j†D_j+E_j†E_j) ≥ (2r+1)(I−|Ω_r><Ω_r|),                 (4)

where Ω_r=τ_r/||τ_r||₂ under vectorization. One can check the vacuum explicitly: its coefficients are (1−q²)^(n/2)q^|p| on |p,p>, q=r/(r+1); both annihilator lists kill it. The squeezing unitary proves completeness of the oscillator basis, not merely uniqueness of this formal recurrence.

Finite energy places |ρ> in the form domain: ||a_jρ||₂²=Tr(ρ²a_j†a_j)≤Tr(ρa_j†a_j), and ||ρa_j||₂²≤Trρ(a_ja_j†). These statements follow first on finite number cutoffs, then by Hilbert–Schmidt convergence; ρ²≤ρ bounds the traces. Thus (4) applies without an illicit bounded inverse. D_j|ρ>=|R_j> and E_j|ρ>=|R_j†>, because ρ is self-adjoint. Orthogonal projection on Ω_r is |cτ_r>. Consequently (4) gives (2r+1)||ρ−cτ_r||₂²≤2ε_R². Finally Trτ_r²=(2r+1)^(−n), ||τ_r||∞=(r+1)^(−n); positivity and trace one imply the stated bound on c. This proves (1).

**Proof of (2)–(3).** Let P=1_{N≤K}, of rank d_K=binomial(K+n,n). For any state σ, q=Trσ(I−P), the gentle compression estimate is ||σ−PσP||₁≤2√q. For a pure state this follows by diagonalizing its two-dimensional P/(I−P) span (the norm is √(4q−3q²)); a pure decomposition, convexity and Cauchy–Schwarz prove it for mixed states. Markov gives q≤TrσN/(K+1). Thus

||ρ−cτ_r||₁≤√d_K t+2√(E/(K+1))+2c√(nr/(K+1)).

Its trace is 1−c, so |1−c| is at most the same quantity. Adding |1−c| proves (2). For t≤1 choose K+1=ceil(t^(−2/(n+1))). This is at most 2t^(−2/(n+1)), and d_K≤(K+1)^n by embedding the total-number simplex in the n-dimensional integer cube. Substitution proves (3). If t=0 then ρ=cτ_r and trace one gives c=1. ∎

### Explicit connection to the source's metric defect

For a **faithful centered** state with finite energy, use EP's thermal metric and defect at parameter r, when the dual defect norm Q²=Σ_j||q_j||²_{F,*} is finite. No Hessian comparison is assumed in this observation. In an eigenbasis with eigenvalues p_l,

q_j(Z)=Tr(R_j†Z),
||Z||_F²=Σ_lr h(r) ℓ(rp_l,(r+1)p_r)|Z_lr|²,

where h(r)=log((r+1)/r) and ℓ is the logarithmic mean. By ℓ(x,y)≤(x+y)/2 and p_l,p_r≤1,

||Z||_F²≤h(r)(2r+1)||Z||₂²/2.

The centered projection is orthogonal in this metric and q_j(I)=0. To justify it using exactly the source test domain, fix a finite spectral-block Z and let P_M increase through spectral projections containing its block. The centered finite-block tests Z_M=P_MZP_M−[Tr(ρP_MZP_M)/Tr(ρP_M)]P_M converge in the F metric to Z−Tr(ρZ)I, since the diagonal metric weight is p_l and Trρ(I−P_M)→0. As R_j is trace class, q_j(Z_M)→q_j(Z). Duality and orthogonal projection therefore give |q_j(Z)|≤||q_j||_{F,*}||Z||_F≤[h(r)(2r+1)/2]^(1/2)||q_j||_{F,*}||Z||₂. Hilbert–Schmidt density and duality now prove

ε_R²≤h(r)(2r+1)Q²/2,   ||ρ−cτ_r||₂≤√h(r) Q.                (5)

Thus (2)–(3) apply with t=√h(r)Q. This explicitly converts the source's *weighted* dual defect to the ordinary norm needed in B114; they are not silently identified.

At EP's particular regularized minimizers, its complete cancellation proves A_*²+M_*²≤2Cζ/ε, with fixed positive weights w_i and uniformly bounded energies. Apply (5) to each state after its own displacement. It gives a centered trace-distance rate O(ζ^(1/[2(n+1)])). The means have size O(√ζ). To undo centering, for a thermal state and displacement α,

||D(α)τ_rD(α)†−τ_r||₁≤2√(2r+1)|α|.

Indeed purify τ_r, write D(α)=e^{iH_α}, use |e^{ix}−1|≤|x| on the self-adjoint generator, and evaluate Trτ_rH_α²=(2r+1)|α|²; the pure-vector trace estimate and partial trace give the bound. Hence the same O(ζ^(1/[2(n+1)])) rate holds without centering, for 0<ζ≤1. These constants depend on the source's fixed auxiliary parameters, its sublevel energy bound and w_i. This strengthens its qualitative recurrence-limit step quantitatively, but does not change the class of states to which its stationarity estimate applies. It is **technical**, with a full reduction to thermal oscillator diagonalization, duality and energy cutoffs.

### The unpaid part of Route I

For B, one needs a bound on the actual near-minimizer, for example Q(ρ)≤CΔ^β after centering (with an appropriate definition/regularization if not faithful). This would combine with (5)–(3) to give α=β/(n+1). EP only supplies Q at its **auxiliary Gibbs minimizers constructed from a hypothetical strict negative witness**. Its precise difference identity, `eq:relative-entropy-difference`, and component Hessian contraction use the exact Gibbs equation and global minimality of that penalized functional. They do not apply to an arbitrary small nonnegative Δ. Letting ζ tend to zero does not create a coupling between the original ρ and those minimizers.

An attempted repair adds a tether to ρ or restricts the minimization to a small trace ball. A trace-ball boundary introduces a normal term in the Euler equation; a quadratic Hilbert–Schmidt tether adds 2λ(σ−ρ). The relaxation pairing then contains Tr[(σ−ρ)L_rσ], which the energy cap alone does not bound by λ times the thermal metric defect with the needed favorable sign. Moreover small objective value by itself gives no small gradient uniformly near eigenvalues zero: the entropy Hessian contains reciprocal logarithmic means. The source's output replacement bounds its own output logarithm but not the original state's small input eigenvalues. No quantitative tether/approximate-stationarity estimate is established. B114 pays the stable recurrence, not this missing entropy-to-defect transfer.

## 4. Route II: doubling, information loss and thermal filtering

This route uses a different mechanism: recover near-independence from near-preservation of information under a deliberately noisy channel. The following quantitative statement is proved fully and is independent of B114.

### Q114: energy-controlled strict information loss

Let X be m≥1 bosonic modes, K any separable reference with S(ω_K)<∞, and ω_XK any state with Trω_X N≤E<∞. Put Φ=T_{1/2,2}, acting on X only, and

ℓ=I(X;K)_ω−I(Y;K)_(Φ⊗id)(ω)≥0.

All mutual informations are finite, since S(X) is bounded by the energy constraint. For every integer L≥0,

||ω_XK−ω_X⊗ω_K||₁
 ≤ 2·3^m·2^L√(2ℓ)+8√(E/(L+1)).                             (6)

The left side is also ≤2, so the infimum of these upper bounds may be capped at 2. In particular, for 0<ℓ<1,

||ω_XK−ω_X⊗ω_K||₁
 ≤2√2·3^m ℓ^(1/4)+16√(E log2/log(1/ℓ)).                      (7)

For ℓ=0 it is zero. The bound is independent of reference dimension, but not of m or E. It is a trace-norm statement; no small-relative-entropy converse is asserted.

**Proof, including the channel construction.** The heterodyne representation is

Φ(ρ)=∫ Q_ρ(z) π_z d^(2m)z,
π_z=D(z/√2)τ_{1/2}D(z/√2)†,
Q_ρ(z)=π^(−m)<z|ρ|z>.

Its characteristic function is χ_ρ(w/√2)e^(−5|w|²/4), which agrees with a balanced mixer with bath mean 2. This verifies the representation by uniqueness of Weyl characteristic functions. For α=z/√2,

<0|π_z^(−1)|0>=(3/2)^m<-α|3^N|−α>=(3/2)^m e^|z|².

The middle equality is the convergent coherent-state series Σ3^k|α|^(2k)/k!=e^(3|α|²), with its normalization factor. Cauchy–Schwarz in the quadratic form of π_z gives π_z≥c(z)|0><0| with c(z)=(2/3)^m e^(−|z|²). Therefore Φ is a sum of two CP branches, one replacing its input by vacuum with effect

G=∫c(z)|z><z|d^(2m)z/π^m=3^(−m)2^(−N).

The polar coherent-state integral has kth diagonal coefficient 2^(−k−1) in one mode, proving this identity. The other branch Λ₀ is measure-and-prepare with positive kernel π_z−c(z)|0><0| and effect I−G. As I−G≥(1−3^(−m))I, it factors as Ψ₀((I−G)^(1/2)ρ(I−G)^(1/2)) for a channel Ψ₀. Thus Φ is implemented by the binary instrument with filters √G,√(I−G), then erasing X on outcome 1 and applying Ψ₀ on outcome 0, finally forgetting the outcome.

Let p=TrGω_X>0 and ξ=p^(−1)(√G⊗I)ω(√G⊗I). Data processing before and after this instrument, with its classical flag retained, gives exactly ℓ≥p I(X;K)_ξ: the flag-reference information and branch-0 upper bound cancel. This is Li's Eq. (59), reproduced here at its full operator scope. Branch entropies are finite: the filters commute with N and are contractions; each conditional reference entropy is bounded by S(ω_K) divided by its positive branch probability; output branch energies are bounded by the total output energy divided by the branch probability. Thus the ordinary chain rules used in that subtraction are legitimate. The integral maps are CP on every finite ancillary space because their operator-valued integrands are positive, with total trace at most the input trace; trace-norm continuity extends them to the stated separable systems.

Quantum Pinsker in nats (obtain it by a Helstrom binary measurement and classical Pinsker) gives

|| (√G⊗I)ω(√G⊗I)−(√Gω_X√G)⊗ξ_K ||₁≤√(2pℓ)≤√(2ℓ).

For P_L=1_{N≤L}, the compressed inverse has norm ||P_LG^(−1/2)||=3^(m/2)2^(L/2). Conjugating the preceding trace-class difference by this bounded operator therefore gives

||P_LωP_L−P_Lω_XP_L⊗ξ_K||₁≤3^m2^L√(2ℓ).

Both states ω and ω_X⊗ξ_K have the same X energy. Applying the gentle estimate from §3 to each yields

||ω−ω_X⊗ξ_K||₁≤3^m2^L√(2ℓ)+4√(E/(L+1)).

Partial trace bounds ||ω_K−ξ_K||₁ by that same expression. One final triangle inequality proves (6). For 0<ℓ<1 take L=floor(log(1/ℓ)/(4log2)); then 2^L√ℓ≤ℓ^(1/4) and L+1>log(1/ℓ)/(4log2), proving (7). If ℓ=0 first use (6) at fixed L, then let L→∞. ∎

The construction and information-loss budget are attributed to Li, not presented as a new equality mechanism. Finite-energy truncation of its explicit inverse filter supplies the paid logarithmic rate. This is a concrete full-scope technical reduction, and Q114 is **not nominated** as substantial.

### What the doubling identity actually buys, and why unequal EPnI stops it

Let independent finite-energy A,B have output pair CE under U_η and linear deficit

L_η=S(C)−ηS(A)−(1−η)S(B).

Li's exact doubling identity, with an independent auxiliary pair (τ₂,τ₂), decomposes L_η into two nonnegative qEPI deficits and I(C_−;E_+|C_+). Read the commuting circuit in the other order, and put σ_CJ=(id⊗Φ)(ω_CE). The last conditional information equals

I(C;J)_σ−I(C_+;J)_(Φ⊗id)(σ) ≤L_η.

The equality follows by the chain rule and independence of the auxiliary C bath; no near-equality argument is needed for this identity. The two other terms are nonnegative by unconditional/conditionally independent qEPI, with the memory's conditional independence verified by the A-group/B-group product factorization. Therefore (6) applies to σ, with ℓ≤L_η and E_C≤E_A+E_B. It controls the **noisy** CE correlations. Removing Φ quantitatively would require another estimate: its characteristic multiplier e^(−5|w|²/4) is nonzero but has an unbounded inverse. Exact injectivity alone is not a rate. A finite-energy inversion/cutoff argument is plausible; it is not claimed proved here, and Cuesta's fourth-moment constants cannot simply be used after an uncontrolled approximation.

Even a complete solution of that inversion would not settle B. At the *exact* thermal minimizer A=τ_r, B=τ_b, put s=ηr+(1−η)b. Then Δ=0 but

L_η=n[g(s)−ηg(r)−(1−η)g(b)]>0                              (8)

for r≠b, since g''(x)=−1/[x(x+1)]<0. Also the cross-covariance of the two outputs is √(η(1−η))(b−r)I, up to the harmless sign convention for the discarded port, and is nonzero. Thus the desired unequal-temperature optimizers **do not have product outputs**. Equation (8) refutes the proposed inequality L_η≤CΔ^β for any finite C,β>0 even at optimizers; it does not refute B.

Using an unequal thermal auxiliary merely moves this problem: that auxiliary's output pair is correlated, so the clean local-noise factorization and zero baseline used by Li disappear. One would need a new identity comparing to the *correlated Gaussian reference output*, with an error bounded by Δ and a recoverable input-reference structure. Naively replacing qEPI by a conditional EPnI is not an available repair: I07 already records its precise quantum-memory counterexample, using De Palma–Trevisan's conditional optimality theorem. No conditional EPnI or commuting-limit statement is inferred here.

## 5. Counterexample and limit tests with complete proofs

### No energy-cap-free information-loss modulus

Q114 genuinely needs a common E. For one mode and a classical bit reference, let

ω^(k)_XK=½|0><0|⊗|0><0|+½|k><k|⊗|1><1|,   k≥64.

Then ||ω^(k)−ω_X^(k)⊗ω_K^(k)||₁=1 (four orthogonal diagonal blocks of magnitude 1/4), and I(X;K)=log2. Each state has finite energy k/2, but the energies are not uniformly capped.

Under Φ=T_{1/2,2}, vacuum has output thermal mean 1, while the kth Fock input has output number mean k/2+1 and variance 5k/4+2. To compute this, write n_out=(n_a+n_b+a†b+b†a)/2. In the product of a number state and a thermal state, cross terms with an odd ladder factor vanish, Var n_b=6 and <(a†b+b†a)²>=5k+2. Division by four gives 6/4+(5k+2)/4=5k/4+2.

Measure output photon number and classify as bit 1 if it is at least k/4. Markov bounds the vacuum error by 4/k. Chebyshev bounds the Fock error by (5k/4+2)/(k/4+1)²≤20/k+32/k². The average error e_k≤12/k+16/k²<1/2. Data processing and binary Fano give

0≤ℓ_k=log2−I(Y;K)≤h₂(e_k)≤h₂(12/k+16/k²)→0.

Thus no function tending to zero with ℓ alone can bound the correlation distance over *all finite-energy states*. This counterexample concerns the stronger energy-free Q proposal, not B or fixed-E Q114.

### Trace closeness does not imply thermal-relative-entropy closeness at bounded energy

Fix r,c₀>0 and let ρ_k=(1−c₀/k)τ_r+(c₀/k)|k,0,...,0><k,0,...,0| for integers k>c₀. Then ||ρ_k−τ_r||₁≤2c₀/k→0 and Trρ_kN=(1−c₀/k)nr+c₀ is uniformly bounded. The source's energy-entropy continuity gives S(ρ_k)→ng(r). Its exact thermal-relative-entropy identity then yields

D(ρ_k||τ_r)→h(r)c₀>0.

Means are zero. Their entropies are not required to equal ng(r), so this is a topology/transfer counterexample and **not** a counterexample to B. It explains why B114's trace result cannot be silently upgraded to relative entropy. The same rare tail has unbounded higher moments, explaining why finite energy cannot be called a fourth-moment cap.

### Symmetry, endpoints and compactness

A displaced thermal is an exact optimizer, so a conclusion to the undisplaced thermal without centering is false. For two freely varying independent inputs, the same symplectic transformation on both ports commutes with the scalar beam splitter and preserves all three entropies; at equal entropies any equal-covariance Gaussian pair is already a linear-qEPI extremizer. These facts exclude an unjustified “only isotropic thermals” claim for the two-free-port problem. B fixes an isotropic bath and uses centering explicitly. At η=0 or 1 the entropy inequality has many trivial equality cases, so those endpoints cannot be included in B with its proposed extremal family.

A uniform energy cap makes the fixed-mode state set compact and its entropy continuous. Even if uniqueness were proved, compactness would supply only an unspecified inverse modulus. Neither a power rate nor a mode-uniform theorem follows. All displayed quantitative rates above arise from an actual oscillator spectral estimate or a specified cutoff/inverse-filter budget.

## 6. Contribution and evidence disposition

**Author-proved technical claims:** B114 (1)–(5), its scoped regularized-minimizer rate, Q114 (6)–(7), the noisy-correlation consequence of the exact doubling identity, the energy-free and trace/KL counterexamples, and high-precision synthesis S. Their full proofs and parameter costs are above. No independent analytic review has yet occurred. The tests are exact finite diagnostics, not proofs of universal operator assertions.

**Unresolved:** B, the deficit-to-balance estimate for arbitrary near-minimizers, and a correlated-Gaussian-reference replacement for Route II. G was screened but not developed into a theorem. **Excluded:** GAD strong converse is already in current primary literature and in I07; arbitrary-partner additivity and the zero-key channel flag completion are already source operations; conditional EPnI is not a valid generic bridge. No completed partial result is promoted merely because it is absent verbatim from a source theorem title.

The package retains acquisition failures: a mistaken Cuesta v3 HTML URL returned 404 (the current page lists only v1); direct SSRN and QIQCOP requests returned 403, while QIQCOP was readable through web browsing; an initial shell read omitted the required working directory and failed before writing; oversized initial tool outputs were truncated, prompting focused reads. Fang v1 was initially fetched from an indexed search; the ledger's earlier comparison identified the later v2, which was then retrieved and read. A metadata-only title-pass bug initially counted the shared `preprints/` component instead of manuscript components; it was corrected to the 749-directory domain before validation and is retained in `failure-log.json`. None of these failures was erased or relabelled a successful inspection. No PDF re-extraction or source repair was used.

The final verifier is offline and read-only: it checks the exact owned inventory, immutable originals and text views, original Git blobs against the complete tree, frozen references, all lexical occurrence multisets, extracted passages, deterministic HTML text views and finite rational diagnostics. Only README.md, frontier/README.md, frontier/TEN-FINDINGS.md and frontier/iterations/README.md may drift at their live paths; their frozen snapshots never drift. I112/I113 outputs are not dependencies. Validation precedes one final seal; later verification does not write, download, create bytecode, repair or reseal.

Run from the research directory:

```bash
python -B frontier/experiments/i114_quantum_information_discovery/check.py
python -B frontier/experiments/i114_quantum_information_discovery/verify.py
```

Preseal validation passed: 10,373 original positions (627,365,628 bytes), 98 topic and 143 stability occurrences, 27 read sources/34 exact passages, nine HTML text views, and 2,866 exact finite diagnostic cases. All four permitted live ledgers had drifted from their immutable snapshots; every other bound reference matched. The final seal and subsequent default verification bind the final exact owned inventory.

A source-hash replay establishes provenance and scoped reproducibility, not universal proof validity, contribution significance, human review, formal certification or worldwide priority. The parent can review the two paid estimates and the precise remaining obligations without treating this record as a ninth finding.
