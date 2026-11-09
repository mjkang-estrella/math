# I340 kinetic window — a time-translation window lemma and the functional limit

Date: 2026-10-14. Pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. **H** denotes
`preprints/Hard-sphere-fluctuations-on-the-regular-Boltzmann-lifespan-September-23-2026/build`
at that pin; its theorem statements are stipulated true (AGENTS.md). Every deduction
below is new or re-derived here. **None has passed a fresh independent proof gate.**

**Verdict: CANDIDATE FULL THEOREM, pending an independent gate.** The missing operation
recorded in the I340 report was a window-localised bound for the centred collision current
on one pasted process, valid also for *redundant* contacts, together with a microscopic
modulus at the same cutoff. Both are supplied below.

- **Lemma A (§3)** handles redundant contacts with a single argument: a global time-translation flow in
  H's own chronological merger chart. It is measure-preserving, and every contact time moves
  along it at unit speed, including a redundant contact time that is a determined function of the
  merger parameters.
- **Prop. B (§4)** gives the uniform fourth-increment bound C(δ²+δ/μ) with an additive
  error smaller than any power of μ. This replaces the qualitative rᵋ.
- **Prop. C (§5)** gives the microscopic modulus at α=μ⁻⁷ᐟ³. It uses third moments of the number
  of particles that collide in a cell; no two-collision or close-pair estimate is needed.
- **§6–7** apply GRR and transfer to the true gas.

§9 lists the points a referee must check. The two that go beyond H's literal statements are:

- **R1:** an extension of H's record class to a collision flag. It is used only in Prop. C.
- **R2:** use of H's chart on affinely extended histories inside an upper bound.

---

## 1. Exact statement

**Theorem K.** Assume H `ass:kinetic`:

- f₀≥0 is a smooth probability density, and ‖f₀‖_{Bol,2β}+‖∇ₓf₀‖_{Bol,2β}<∞ for some β>0.
- On the **supplied** finite [0,T] there is a nonnegative classical Boltzmann solution with
  sup_{t,x,v} e^{2β|v|²}f(t,x,v)<∞.

Let the initial law be H `eq:grand-canonical`: grand-canonical excluded product activity μ=ε⁻²
on ℝ³ₓ×ℝ³ᵥ, including N=0, with diameter ε. The dynamics are deterministic elastic hard spheres
(DHM Prop. 1.2 a.e. flow), with nothing shortened, periodised, small-data or equilibrium.

For real φ₁,…,φ_m∈C_c^∞(ℝ⁶) put

  Xᵋ_t(φ_j)=μ^{-1/2}[Σ_iφ_j(z_i(t))−E_εΣ_iφ_j(z_i(t))]   (exact microscopic centring at every t).

Then, as ε↓0,

  (Xᵋ(φ₁),…,Xᵋ(φ_m)) ⟹ (ζ^c(φ₁),…,ζ^c(φ_m))   in D([0,T],ℝ^m) with the J1 topology.

Here ζ^c is the continuous coordinate modification of H's Gaussian field (`thm:main`,
`prop:gaussian-target`). Its covariance is the full joint backward covariance

  K_{φ,ψ}(t,s)=∫f₀U(0,t)φ U(0,s)ψ+∫₀^{t∧s}C_r(U(r,t)φ,U(r,s)ψ)dr,

with the Poisson initial term. Because the limit is continuous, the convergence also holds in the
uniform topology.

The FDD part is H `thm:main`. Everything new is tightness (§§3–6) and its assembly (§7).

---

## 2. Inputs used, with their status

| Input | Role | Status |
|---|---|---|
| H `thm:marked-expansion` (i)–(iii) | pasted factorial cumulants = retained connected diagrams + TV error e^{−cΛ_L}; ρ>K tail ≤ε^P | stipulated |
| H `lem:sharp-merger-coordinates` and its proof | chart (V,Ω,S,Y,X), merger Jacobian ε²[u·ω]₊, redundant contacts are indicators, triangular construction | stipulated; construction reused verbatim on affine lines (R2) |
| H `eq:sharp-scaling`, `lem:sharp-factorials`, `lem:sharp-summability` and proofs | μ^{1−h}ε^p normalisation, fresh-label factorial counting, pair-sum flux induction, majorant C_K(1+n)^{d_K}(Cτ√L)^n | stipulated; one step (time volume / link volume) modified and re-proved in §3 |
| H §06 initial-link replacement `eq:sharp-initial-link` and the tail-erasure paragraph | nontrivial initial blocks → physical links (gain ε^p) or erased tails (O(ε^M μ^{1−h})) | stipulated |
| H `prop:initial` `eq:initial-N-moments` | sup_ε E(N/μ)^p<∞ | stipulated |
| H `prop:cumulant-clt`, `eq:limit-factorial-ordinary` | FDD of the **pasted** process; factorial→ordinary cumulants | stipulated |
| H `prop:cutoff`, `lem:center-transfer` | discrepancy P≤Cε^{1+η}, η=1/20 | stipulated |
| Prior I340 §2 (parent §1) | continuous Gaussian coordinate modification with covariance K | proved before; re-checked, carried forward |
| Prior I340 §3 (parent §2) | sup_t‖Xᵋ−X̂ᵋ‖→0 in probability, simultaneously in t | proved before; re-checked, carried forward |
| Garsia–Rodemich–Rumsey (1970) | real-variable modulus inequality | classical |

X̂ denotes the pasted process of H `thm:marked-expansion`, centred by its **own** exact
expectation. Throughout, h≤4, P is a fixed accuracy power (P=12 suffices, see §8), and K is
chosen after P, h and the record list as in H `thm:marked-expansion`(iii).

**Uniformity in pulse positions.** This was re-checked in H §04 and §06 proofs, and the prior §6
records the same conclusion. The observation list enters H's estimates only through:

- the number of record-bearing labels (dummy-line cost ε^{−C_m}, root slack A_i/2);
- polynomial record-placement counts;
- the sup-norm of record tests.

No estimate uses pulse **times**. Hence for a fixed number of pulses and recorded labels, the
thresholds ε₀ and K and the constants in the e^{−cΛ_L} and ε^P errors are uniform in the pulse
times and in the window W below.

---

## 3. Lemma A — the time-translation window bound

### 3.1 Setting

Fix a bounded "datum" in the sense of H §06:

- a finite line graph G on m particle lines;
- C/O flags;
- a **total chronological order** of its atoms;
- the set of redundant atoms in that order;
- a physical initial-link forest with p links (lines born at 0);
- slab assignments and slab sizes (n_i), with a_i mergers in slab i and a=Σa_i=m−1−p.

The graph is connected (c=1), with h designated roots. H `lem:sharp-merger-coordinates` uses the
following coordinates:

- V∈ℝ^{3m}: birth velocities;
- Ω∈(S²)^a and S∈ℝ^a: merger normals and times;
- Y∈ℝ^{3p}: the link vectors;
- X∈ℝ³: one translation.

The absolute contribution of the datum, tested against a bounded record functional Ψ, is bounded by

  μ^{m−h}ε^{2a}∫dV dΩ dS dY dX Π_k[u_k·ω_k]₊ · 𝔟(V,Ω,S,Y,X) · 1_{Dom}(V,Ω,S,Y) · |Ψ|.   (A.1)

The factors are as follows.

- 𝔟 is the product of birth envelopes (|f₀|, the initial-block f₀ products, and |g_i| at interface
  births) evaluated at the physical birth points.
- Dom is the realisability domain:
  - every merger is an incoming contact on its prescribed segments, in its slab, in the
    prescribed order;
  - every prescribed redundant atom occurs on its prescribed segments, in its slab, in the order;
  - every link vector lies in the ball B_{Rε}.
- All other acceptance, compatibility and selection indicators are in [0,1] and have been dropped,
  exactly as in H §06.

Integrating the ball volumes gives H's normalisation μ^{1−h}ε^p (`eq:sharp-scaling`).

**Affine extension (R2).** H's chart construction proof runs "in increasing contact time" in the
prescribed order. It solves each merger's contact equation X−X_*=−d(t)−εω for the relative
translation, and determines each redundant contact as the unique incoming crossing of a straight
relative flight. The construction uses births only as affine origins.

Apply it to lines extended affinely beyond their births and ends. Time-0 and interface quantities
(link vectors, birth points) are defined through the affine extension of each line's **first**
segment. A redundant atom r is required to be an incoming ε-crossing after the previous event in
the prescribed order and before the next merger in that order (or at any later time if there is
none). This defines, for **every** (V,Ω,S,Y), an *extended history*. It consists of piecewise
affine elastic paths with breakpoints at the atoms of each line, in increasing order along each
line.

Write E_G for the indicator that the extended history is realisable: all merger fluxes are
positive and every prescribed redundant atom occurs in the extended sense. Then

  Dom ⊂ {E_G=1} ∩ {S∈Δ_G} ∩ {Y∈B_{Rε}^p},

where Δ_G is the set of merger-time vectors ordered as prescribed with each merger in its slab.
On Dom the extended history coincides with the actual prescribed one. Indeed, the prescribed
atoms occur inside the lines' lifetimes, and a straight relative flight has at most one incoming
crossing on any interval.

**Causality.** In the extended history, the occurrence, time, normal and velocity update of a
redundant atom r are determined by the data of atoms preceding r in the prescribed order. The
lines of r are joined by contacts that precede r, whose translations are already solved, and the
detection interval is bounded by events before r and by fixed merger times. Likewise the incoming
velocities at the k-th merger depend only on earlier atoms. This is the property used by H's
pair-sum induction ("all earlier velocities and all intervening specified redundant contacts are
already determined"). It holds for extended histories verbatim.

### 3.2 Translation integral

For fixed (V,Ω,S,Y), nothing in (A.1) except 𝔟 depends on X. The X-integral of 𝔟 is at most

  𝔅(V):=C^m Π_p e^{−b|v_p|²},

uniformly in all displacements. This is H's argument in `lem:sharp-summability`: one input in
L¹_x, every other input in sup_x, both from the Bol bounds `eq:sharp-input-bounds`. Hence, for
any event 𝒲 not depending on X,

  (A.1) restricted to 𝒲 ≤ ‖Ψ‖_∞ μ^{m−h}ε^{2a} ∫ dV dΩ dS dY Ξ(V,Ω,S,Y) 1_{Dom} 1_𝒲,
  Ξ := 𝔅(V)·Π_k[u_k·ω_k]₊·E_G.                                            (A.2)

Here the u_k are the incoming relative velocities of the extended history.

### 3.3 The flow

For λ∈ℝ define the map T_λ by

  T_λ(V,Ω,S,Y)=(V, Ω, S+λ𝟙, Y−λΔV),  where (ΔV)_ℓ=v_{p_ℓ}−v_{q_ℓ} for link ℓ=(p_ℓ,q_ℓ).

**(F1) Measure preservation.** For fixed V, T_λ is a translation in (S,Y), so it preserves
dV dΩ dS dY.

**(F2) Covariance.** Delay every extended path by λ: z̃_e(t)=z_e(t−λ). The result has the same
velocities on corresponding segments. Its mergers occur at S+λ with the same normals, since the
relative positions at the delayed contact times are unchanged. Its link vectors are the
first-segment extensions at 0, equal to the originals at −λ, namely Y−λΔV.

H's construction is triangular with multiplicity one on each prescribed branch. So the extended
history at T_λ(V,Ω,S,Y) is exactly this delay. Each redundant atom's detection interval is
bounded by events in the prescribed order, which are all delayed. A straight flight has a unique
incoming crossing, so every redundant atom of the delayed history occurs, with the same normal,
at its old time plus λ.

Consequences:

- E_G∘T_λ=E_G, Ξ∘T_λ=Ξ;
- for **every** atom a of G, merger or redundant, t_a∘T_λ=t_a+λ on {E_G=1}.

This is the point that the I340 report found missing. A redundant time has no own coordinate,
yet along the free direction 𝟙 of the chart it has derivative exactly one.
`checks/shift_covariance.py` verifies (F2) on 400 random prescribed histories with up to six
lines, 27 of which contain redundant elastic scatterings; the maximal discrepancy is 1e-13.

### 3.4 The averaging inequality

Let W⊂ℝ be an interval, a an atom, and Λ>0. For each λ∈[0,Λ], substitute ξ=T_λη in (A.2) with
𝒲={t_a∈W}. By (F1)–(F2),

  ∫Ξ 1_{Dom}1{t_a∈W} dξ = ∫Ξ(η) 1_{Dom}(T_λη) 1{t_a(η)+λ∈W} dη.

Average over λ∈[0,Λ]. For fixed η the set {λ∈[0,Λ]: t_a(η)+λ∈W} has length at most |W|, so

  ∫Ξ 1_{Dom}1{t_a∈W} ≤ (|W|/Λ) ∫ Ξ 1_{Dom_Λ},   Dom_Λ:=⋃_{λ∈[0,Λ]}T_{−λ}Dom.        (A.3)

Moreover

  Dom_Λ ⊂ {E_G=1} ∩ {S∈Δ_G^Λ} ∩ {Y∈Π_ℓ(B_{Rε}+[0,Λ]ΔV_ℓ)},

where Δ_G^Λ allows the slab-i merger times anywhere in (θ_{i−1}−Λ,θ_i), still in the prescribed
order. The window indicator has disappeared from the right side. That side is the unconstrained
absolute majorant on a slightly enlarged domain.

### 3.5 Re-running H's summation on Dom_Λ

Every step of H `lem:sharp-summability` applies to ∫Ξ1_{Dom_Λ} for the extended histories:

1. **Energy bins and pair-sum induction** at fixed (S,Ω,V). The fluxes come from an elastic
   affine history, with total energy at most E₀ at every time, determined causally in the
   prescribed order (§3.1). Hence the sum over merger-pair choices is at most ∏_i(n_i^{3/2}√P)^{a_i}.
2. **Normals:** a factor C^a.
3. **Time volume:** ∏_i(τ+Λ)^{a_i}/a_i! ≤ e^{Λa/τ}∏_iτ^{a_i}/a_i!, instead of ∏_iτ^{a_i}/a_i!.
4. **Link volume:** for each link,
   |B_{Rε}+[0,Λ]ΔV_ℓ| ≤ (Rε)³(4π/3+π|ΔV_ℓ|Λ/(Rε)).
5. **Velocity factors:** the polynomial Π_ℓ(1+|ΔV_ℓ|) has degree p≤K. It is absorbed by a fixed
   fraction of the reserved Gaussian, exactly as H absorbs record weights. This changes C_K, not
   the base.

The choice of Λ depends on p.

- **p=0:** take Λ=τ/(1+a). Then e^{Λa/τ}≤e, and (A.3) costs the factor e(1+a)|W|/τ.
- **p≥1:** take Λ=min(ε,τ/(1+a)). The link factor is ≤C_K, and (A.3) costs
  e|W|(1/ε+(1+a)/τ). Against H's link gain ε^p this leaves |W|·ε^{p−1}(1+a)≤|W|(1+a).

The exclusion correlation at scale ε is singular under a time shift. That costs one 1/ε, which
is paid by one physical link's ε gain.

The counting of `lem:sharp-factorials` (fresh-label denominators ∏j_i!, bounded crossings, at most
C_K redundant atoms) is untouched.

**Lemma A.** Fix K, h and a bounded record list. There are C_K, d_K and the **same** base Cτ√L<1
as in H such that the following holds. For every interval W, every slab-size vector (n_i), and
every rule selecting a set A_G of atoms of each graph (for instance the C-atoms on designated
line 1),

  μ^{h−1} Σ_G |D_G|(1{∃a∈A_G: t_a∈W}) ≤ C_K(1+n)^{d_K+2}(Cτ√L)^n · |W|·(1+τ^{−1}).

The sum runs over the connected retained diagrams of complexity ≤K with these slab sizes,
including those with physical initial links. Summing over (n_i) and the finitely many bounded data
gives a bound C_{K,h}|W|.

*Proof.* Use 1{∃a∈A_G: t_a∈W} ≤ Σ_{a∈A_G}1{t_a∈W}, with |A_G| ≤ b ≤ n+C_K, and apply
(A.2)–(A.3) and §3.5. Λ depends only on (n_i) and the bounded datum, through a and p, so the
pair-sum induction over the whole merger-pair family is performed after (A.3) with one Λ. ∎

**Corollary A′.** Let |Ψ| ≤ M₀[δ₀+1{some C-atom of designated line 1 has time in W}] pointwise on
every refined C/O history of H §06. Then

  |c^ε_h(Ψ)| ≤ C(δ₀+|W|)μ^{1−h} + C_P ε^P,

uniformly in W, δ₀, and pulse times, where c^ε_h is the pasted normalised factorial cumulant.

*Proof.* Apply H `thm:marked-expansion` (ii)–(iii): the variation error e^{−cΛ_L} and the ρ>K tail
are ≤ε^P in TV, and the test is bounded. At ρ≤K:

- the δ₀ part is bounded by H's unwindowed majorant;
- the window part is bounded by Lemma A;
- initial tails are erased at cost O(ε^{D−2K}μ^{1−h}) (H §06), with D large.

Refinement into C/O molecules partitions indicators (H `lem:one-root-bridge` proof, §06
`lem:sharp-factorials`). On each piece the designated particle's trajectory is the prescribed
one, so the pointwise hypothesis applies. ∎

---

## 4. Proposition B — uniform fourth increments, no qualitative remainder

**Prop. B.** For φ∈C_c^∞, B=‖φ‖_∞ and D=‖v·∇ₓφ‖_∞, there is C such that, for all ε≤ε₀ and
0≤s<t≤T, with δ=t−s,

  E|X̂_t(φ)−X̂_s(φ)|⁴ ≤ C(δ²+δ/μ) + C μ²ε^P.

*Proof.* Use two pulses: −φ at s and +φ at t. Each designated particle's record is
y=φ(z(t))−φ(z(s)), and S=Σ_iy_i. On every refined history the designated trajectory changes
velocity only at its C-atoms; O-atoms and interfaces leave it unchanged. Hence

  |y| ≤ Dδ + 2B·1{some C-atom of that line in (s,t]}.

By H `eq:limit-factorial-ordinary`,

  κ_k(S)=Σ_{π∈𝒫([k])}μ^{|π|}c^ε_{|π|}(∏_By_B^{|B|}).

Bound one factor y of the first block as above and the rest by 2B. Corollary A′ with W=(s,t],
δ₀=δ, gives

  |κ_k(S)| ≤ C_k(μδ+μ^kε^P),   k=2,4.

Since X̂_t−X̂_s=(S−ES)/√μ,

  E|X̂_t−X̂_s|⁴ = κ₄/μ²+3κ₂²/μ² ≤ C(δ/μ+μ²ε^P)+C(δ+με^P)². ∎

This replaces prior estimate (8): (δ+rᵋ)²+μ⁻¹(δ+rᵋ) with an unquantified rᵋ becomes δ²+δ/μ with
an additive error smaller than any fixed power of μ. Trees, cycles and initial-link diagrams are
treated by one mechanism. No cycle-vanishing (dominated-convergence) argument is used.

---

## 5. Proposition C — microscopic modulus at α=μ⁻⁷ᐟ³

### 5.1 Lemma R (collision-flag records)

Fix an interval W. Give a designated particle the record ϑ∈{0,1}, initially 0, which becomes 1
at its first **accepted** collision in W in the pasted dynamics. With finitely many flagged
labels, H `thm:marked-expansion` (i)–(iii) holds with constants independent of W. On every
refined C/O history of H §06, ϑ=1{some C-atom of that line has time in W}.

*Verification against each use of records in H (R1).*

1. **§04 `lem:autonomous-partition`.** κ_C, a(C,D), χ do not involve records. The flag update is
   a function of the particle's own accepted collisions. These coincide in the full history and
   in the autonomous cluster history on the support of each partition summand, which is exactly
   the identity proved there. The lemma itself allows arbitrary tests H(Ψ_V|_S) of root histories.
2. **`lem:one-slab-expansion`.** The root-output map δ_{Ψ_C(X)|_S} carries any deterministic
   record update performed by Ψ_C. H's proof uses only that "compatibility factors do not use
   records, and root-output maps carry them without alteration except for the prescribed
   updates".
3. **`lem:marked-regrouping`.** Flagged labels are put in R⊂H and continued to 0. Forgetting a
   flag is a pushforward that commutes with each kernel, since the weights use unmarked histories.
4. **`lem:diagram-labels`.** No placement choice arises: the flag is a function of C-atom times.
   The counting is unchanged or better.
5. **`lem:stopped-variation` and `thm:marked-expansion`(iii).** Records enter only through their
   number and sup-norm (ϑ≤1).
6. **§06.** Only TV bounds are used for ϑ. The convergence statements requiring continuous record
   tests are never applied to ϑ.

The second assertion holds because, on each refined piece, the autonomous accepted collision
history equals the prescribed C-graph. ∎

The flag is a legitimate but **new** record type. H states records as test values at pulses, or
"a finite list of phase points along each designated trajectory". It is used only here.

### 5.2 Statement and proof

**Prop. C.** With α=μ⁻⁷ᐟ³,

  sup_{0≤s<t≤T, t−s≤2α}|X̂_t(φ)−X̂_s(φ)| → 0 in probability.

*Proof.* Cover the pairs by cells W_j=[jα,jα+4α], 0≤j≤T/α; s∈[jα,(j+1)α) gives t≤jα+3α. Let Z_W
be the number of particles with an accepted collision in W. A particle with no accepted collision
in W flies freely there, so |φ(z(t))−φ(z(s))| ≤ |t−s|D. Hence, for s,t∈W,

  |S_t−S_s| ≤ 4αD·N + 2B·Z_W,
  |ES_t−ES_s| ≤ 4αD·EN + 2B·EZ_W.

**Moments of Z_W.** We have E(Z_W)_j=μ^jF_j(ϑ^{⊗j}), and F_j=Σ_π⊗_{B∈π}c^ε_{|B|} with flagged
records. By Lemma R and Corollary A′ (δ₀=0), each block satisfies

  μ^{|B|}|c^ε_{|B|}(ϑ^{⊗|B|})| ≤ C(μ|W|+μ^{|B|}ε^P).

With μ|W|=4μ^{−4/3}≤1, this gives E(Z_W)_j ≤ C_j(μ|W|+μ^jε^P) for j≤3, and hence

  EZ_W³ ≤ C(μα+μ³ε^P).

**Union bound.** With k=η√μ/(4B),

  P(max_jZ_{W_j}≥k) ≤ (T/α+1)·C(μα+μ³ε^P)/k³ ≤ C_η(μ^{−1/2}+μ^{7/3+3−P/2−3/2}) → 0

for P≥12. Each of the O(1/α) cells is a **separate** expansion with one flag record, and its
constants are uniform in W (§2). This is not a growing pulse grid inside one expansion.

**Remaining terms.**

- 4αDN/√μ → 0 in probability, since N/μ is tight (H `eq:initial-N-moments`).
- The centring term is ≤ C√μα+C√μα+tiny → 0.

Therefore sup over these pairs of |X̂_t−X̂_s| ≤ μ^{−1/2}(4αDN+2B max_jZ_{W_j}) + o(1) → 0 in
probability. ∎

**Comparison.** BGSS 2008.10403v2 Lemma 6.2.5 (read, §6.2.4) requires P(two collisions in the
whole periodic gas in a 2α-cell) ≤ Cαμ^{−1/3}, through their Proposition 3.3.1. In the whole
space, that event concerns ~μ particles over all of ℝ³. Here only a jump-count bound
Z_W=o_P(√μ) is needed, which needs only the one-window Lemma A. H's primitive-pair lemma is not
used.

---

## 6. Lemma G — GRR on the grid interpolation

**Lemma G.** Let Yᵋ be real càdlàg processes on [0,T], α=α_ε↓0, μ=μ_ε→∞ and 2<γ<3. Suppose:

- (G1) Yᵋ₀ is tight;
- (G2) E|Y_g−Y_{g′}|⁴ ≤ C₀(|g−g′|²+|g−g′|/μ)+e_ε on the grid αℤ∩[0,T];
- (G3) ω_Y(2α):=sup_{|t−s|≤2α}|Y_t−Y_s| → 0 in probability;
- (G4) α^{3−γ}+α^{2−γ}/μ+e_εα^{1−γ} stays bounded.

Let Ỹ be the piecewise-linear interpolation of Y on the grid. Then ‖Y−Ỹ‖_∞≤ω_Y(α)→0 in
probability, and Ỹ is tight in C([0,T]) with ω_Ỹ(θ) ≤ C_γ B^{1/4}θ^{(γ−2)/4}, where
B=∫∫|Ỹ_t−Ỹ_s|⁴|t−s|^{−γ}ds dt and sup_εEB<∞.

*Proof.* Take s<t and δ=t−s.

- In one cell, Ỹ_t−Ỹ_s=(δ/α)ΔY_cell.
- Otherwise Ỹ_t−Ỹ_s is the sum of two end pieces with coefficients ≤min(1,δ/α) times cell
  increments, plus a grid increment over a span ≤δ. That middle term is present only when δ≥α.

By (a+b+c)⁴≤27(a⁴+b⁴+c⁴) and (G2),

  E|Ỹ_t−Ỹ_s|⁴ ≤ C[min(1,δ/α)⁴(α²+α/μ+e) + (δ²+δ/μ+e)1_{δ≥α}].

Integrating against δ^{−γ},

  EB ≤ C(α^{3−γ}+α^{2−γ}/μ+eα^{1−γ}+1) = O(1).

The GRR inequality with Ψ(x)=x⁴ and p(u)=u^{γ/4} gives

  |Ỹ_t−Ỹ_s| ≤ 8(4B)^{1/4}(γ/4)∫₀^δ u^{γ/4−3/2}du = C_γB^{1/4}δ^{(γ−2)/4}.

The integrand exponent is −11/12>−1 at γ=7/3. Markov's inequality then gives
P(ω_Ỹ(θ)>η) ≤ Cθ^{γ−2}/η⁴. With (G1), Arzelà–Ascoli (Billingsley 1999, Thm 7.3) gives tightness
in C. Finally |Y_t−Ỹ_t| ≤ max(|Y_t−Y_g|,|Y_t−Y_{g+α}|) ≤ ω_Y(α). ∎

Lemma G is a self-contained form of the modified GRR route in BGSS (their Prop. 6.2.4); it is
credited old machinery.

Apply it with Y=X̂(φ), γ=7/3, α=μ⁻⁷ᐟ³ and e=Cμ²ε^P:

- (G2) is Prop. B;
- (G3) is Prop. C;
- (G1) is H `prop:initial`(iii);
- (G4) holds with exponents −14/9, −2/9 and 2−P/2+28/9, which is <0 for P>92/9.

---

## 7. Proof of Theorem K

1. **Pasted, interpolated.** Each coordinate Ỹ(φ_j) is tight in C([0,T]) by §6, so the vector
   Ỹ=(Ỹ(φ_j))_j is tight in C([0,T],ℝ^m). For fixed times t₁,…,t_k we have
   Ỹ_{t_i}−X̂_{t_i}→0 in probability. H `prop:cumulant-clt` applies to the pasted dynamics with
   multitime records, and Cramér–Wold gives FDD convergence of X̂, hence of Ỹ, to those of ζ.
   A law on C is determined by its FDD, and ζ^c (prior §2) has these FDD and continuous paths.
   So Ỹ ⟹ ζ^c in C.
2. **Pasted, D.** ‖X̂−Ỹ‖_∞→0 in probability, and d_{J1}≤‖·‖_∞. The inclusion C↪D is continuous
   for J1. Slutsky in the metric space (D,d_{J1}) (Billingsley Thm 3.1) gives X̂ ⟹ ζ^c in
   D([0,T],ℝ^m).
3. **True gas.** Prior §3 (H `prop:cutoff` with η=1/20, H `eq:initial-N-moments`, p=22) gives
   ‖Xᵋ−X̂ᵋ‖_∞→0 in probability. That estimate is simultaneous in t, uses the exact centring of
   both processes, and holds for every finite vector. Slutsky again gives Xᵋ ⟹ ζ^c in
   D([0,T],ℝ^m) with J1. ∎

Nothing in the proof shortens T, replaces the initial law, restricts the data size, periodises,
or uses equilibrium. The exact centring of the true gas enters only through step 3.

---

## 8. Reproducible checks (`checks/`, standard library only, deterministic)

| Script | What it checks | Result |
|---|---|---|
| `shift_covariance.py` | (F2) on random prescribed charts with redundant elastic scatterings: all event times shift by λ, and normals, fluxes and velocities are invariant | PASS, 27/400 charts with redundant contacts, max error 1.2e-13 |
| `exponents.py` | every μ-power in §§4–7 (exact rationals) | PASS at P=12. An earlier P=7 run failed the union remainder, and the GRR remainder needs P>92/9, so P=12 is fixed |
| `toy_window_density.py` | Monte Carlo of the 3-line cycle: windowed recollision mass divided by the Lemma A bound (illustration only) | PASS, worst ratio 0.0033 |
| `verify_sources.py` | re-fetches the 11 pinned H files; SHA-256 and git blob vs `sources/preprints-tree.json` | PASS |

The outputs are in `checks/OUTPUT.txt`. Numerics illustrate algebraic identities and do not
replace §§3–7.

---

## 9. What a referee must check (residual risks)

- **R1 — flag records (Prop. C only).** §5.1 checks every place where H uses records. If a
  referee rejects the extension, Prop. C needs another count of colliding particles. Every other
  part of the proof is unaffected.
- **R2 — affine extension of H's chart.** It is used only to define Ξ and E_G on the swept domain
  in an *upper* bound; the actual integrand is Ξ·1_{Dom}. Three things must be checked:
  - H's triangular construction is pure affine algebra;
  - the multiplicity one makes (F2) an identity of extended histories;
  - the pair-sum induction (energy plus causality in the prescribed order) holds off the
    physical lifetimes.
- **R3 — uniformity in pulse and window positions** (§2). This is an inspection claim about H §04
  and §06 proofs, also made in the prior report.
- **R4 — exchange of the averaging with the merger-pair sum.** Λ must be constant on each
  family summed by the pair-sum induction; it depends only on a and p, which are fixed by
  (n_i) and the bounded datum.
- **R5 — measurability and càdlàg paths** of X̂, Xᵋ and the cell suprema. These are standard;
  the pasted flow has finitely many accepted collisions per slab.

No counterexample to any step was found. The prior failed shortcuts are not used (see
`objections.md`).
