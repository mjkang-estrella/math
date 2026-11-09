# r98 durable notes (author working notes, not sealed claims)

Runner: Factory Droid / claude-opus-5-5 / high. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## Selection (2026-10-20)
- Read AGENTS.md, both briefs, r97 REPORT/public report/screens/reading-limits, r97 parent intake.
- Screened via catalogue + authored history: 242 (integer version T242Z archived by r72-recovery-r4; excluded),
  194 Lech (source main.tex + charp.tex read; history AB194 contribution review, r10/r77/r82/r86; Dutta non-domain case is the source's own prime-filtration step -> routine),
  198 (r73, r106 history), 168 (r92, r126), 116 (i103), 039 (r84/r90), 031 (r61 classical; function-field Hom-form likely Saidi-Tamagawa, navigation only),
  266 (computational binary64 main; not proof-friendly).
- Chosen: 009, classification of noninjective compatible maps for ALL p.
- Scratch: an accidental /tmp/r98fam.txt (catalogue titles only) was created outside root early and immediately deleted; disclosed.

## Carter-Vogt primary transcription (PNAS 77(7):3756-3757, 1980; doi 10.1073/pnas.77.7.3756; PMC349703)
Page images: packet/private/primary/pnas00494-0047.png (p.3756), -0048.png (p.3757). Crops work/scratch/cv00{47,48}_{00,01,10,11}.png.

### p.3756 left column (crops cv0047_00, cv0047_10)
- PNAS 77(7):3756-3757, July 1980, Mathematics. "Collinearity-preserving functions between Desarguesian planes", David S. Carter (Oregon State) and Andrew Vogt (Georgetown). Communicated by Garrett Birkhoff, April 4, 1980.
- Abstract: characterization of all lineations between affine/projective Desarguesian planes via valuation theory; projective with quadrangle range treated previously; key theorem = extension theorem except order-2/3 embeddings.
- Lineation: pointwise function sending collinear triples to collinear triples. "In this note we announce a solution" (announcement; no proofs).
- Full = range contains a quadrangle; such lineation between projective planes induces a place, characterizing it up to coordinatizations (refs 2-5). Exceptions: special embeddings of affine planes of order 2, 3 (harmonic relation degenerates).
- Reduced = range contains triangle but no quadrangle. Collapsed = range collinear. Collapsed are trivial; axial (all points off one distinguished line -> one point) and radial (all points other than one distinguished point -> points on a single line) are trivial reduced kinds.
- Footer: page-charge "advertisement" notice.
- Read extent: both pages 3756-3757, all four columns, now fully viewed and transcribed in substance.

### p.3756 right column (crops cv0047_01, cv0047_11)
- Title: "...s between Desarguesian planes" (keywords "...place/valuation ring"); affiliations incl. Georgetown University.
- Reduced lineations have trivial range; reduced lineations with Desarguesian domains come in two types characterized by fractional ideals. All reduced lineations on affine Desarguesian planes have the extension property.
- Daykin (6) asked for nontrivial lineations R^2 -> R^2. No full lineations of R^2 into itself other than affine isomorphisms; many reduced lineations neither axial nor radial; triangle-range ones partition the plane into three totally path-disconnected dense sets, each line meets exactly two.
- EXTENSION THEOREM (stated, no proof): affine Desarguesian 𝒟 with division ring D, projective closure 𝒟̄, projective Desarguesian 𝒯 with ring T, f: 𝒟 -> 𝒯 lineation. Then a lineation f̄: 𝒟̄ -> 𝒯 extends f, except when all hold: f an embedding, |D| ∈ {2,3}, char T ≠ |D|. f̄ unique except when f is collapsed or axial.
- S† = {x ∈ D : x = 0 or x^{-1} ∉ S} for subsets S ∋ 0. Valuation ring: subring V with V† ⊆ V. Place of D into T: ring hom whose domain is a valuation ring of D and range a division subring of T (no conjugation invariance required; = Radó's "total ring"). V† is the unique maximal left and right ideal; ψ: V -> V/V† is a place.

### p.3757 left column (crops cv0048_00, cv0048_10)
- Set multiplication XY = {xy : x∈X, y∈Y}. Prevaluation group: additive subgroup G of D with G†G ⊆ (G†G)† [† = a complement-type operation defined on p.3756]. Then G† is also one; (G†G)† and (GG†)† are valuation rings; with trivial exceptions G, G† are fractional ideals (Schilling p.17).
- P(D): left-homogeneous triples; A(D)=D^2 via (x1,x2) -> [x1,x2,1].
- Five canonical types:
  * Full Type: ψ a place of D into T, V = dom ψ. P(ψ)[x1,x2,x3] = [ψ(a x1),ψ(a x2),ψ(a x3)] for any a with (a xi) ∈ V^3 and image ≠ 0.
  * Reduced Type 1: G a prevaluation group, V = (G†G)†, ψ: V -> V/V† the quotient place. g1[x] = [1,0,0] if x2,x3 ∈ x1 G, else [0,ψ(a x2),ψ(a x3)] with (a x2, a x3) ∈ V^2, image ≠ 0.
  * Reduced Type 2: E1,E2,E3 noncollinear in 𝒯; prevaluation groups G1,G2,G3 with Gi Gj = Gk† and Gj† Gi† = Gk for even permutations (i,j,k). For each x ≠ 0 exactly one even (i,j,k) has xj ∈ xi Gk and xk ∈ xi Gj†; g2[x] = Ei.
  * Special Affine Order 2: D = F2, T of char ≠ 2, h: A(F2) -> P(T) by the four points [0,0,1],[1,0,1],[0,1,1],[1,1,1]; embedding not extendable to P(F2).
  * Special Affine Order 3: D = F3, T of char ≠ 3 containing a root γ of x^2 - x + 1; γ̄ = 1-γ = γ^{-1}; table (right column) gives h.

### p.3757 right column (crops cv0048_01, cv0048_11), transcribed verbatim-in-substance
- End of a counterexample: a table defines an embedding h: A(D) -> P(T) (D = Z_3, T = GF(4) = {0,1,γ,γ̄}) that cannot be extended to a lineation P(D) -> P(T):
  (0,0)->[0,0,1], (1,0)->[1,0,1], (0,1)->[0,1,1], (1,1)->[1,1,1], (2,0)->[γ,0,1], (0,2)->[0,γ̄,1], (1,2)->[1,γ,1], (2,1)->[γ̄,1,1], (2,2)->[1,1,2].
- Coordinatization: for a Desarguesian plane 𝒟 with division ring D, an isomorphism onto A(D) or P(D) (affine/projective). Projective coordinatization of an affine 𝒟: embedding into P(D) whose range is all points except one line.
- CHARACTERIZATION THEOREM. Let 𝒟, 𝒯 be affine or projective Desarguesian planes with division rings D, T, and f: 𝒟 -> 𝒯 a noncollapsed lineation. Then f is obtained from exactly one canonical type:
  (i) If f is reduced, f = τ∘g1∘d or g2∘d, g1/g2 a Reduced Type 1 / Type 2 canonical lineation, d a suitable coordinatization (projective if 𝒟 affine); in Type 1, τ is a point function from range g1 into 𝒯 taking points [0,ψ(a x2),ψ(a x3)] to two or more points on a line L of 𝒯 and [1,0,0] to a point not on L.
  (ii) If f is full, f = t^{-1}∘P(ψ)∘d or t^{-1}∘h∘d, P(ψ) a Full Type canonical lineation, h a Special Affine Order 2 or Order 3 embedding, d, t suitable coordinatizations (possibly projective).
- Remarks: Desarguesian hypothesis on 𝒯 not essential in (i); τ is a trivial reduced lineation. Axial and radial lineations have the form τ∘g1∘d with prevaluation group G of g1 equal to D or {0}.
- Corollaries stated without proof: P(D) embeds in A(T) iff D ≅ division subring D' of T with dim_{D'} T ≥ 3 (left). Unique pair with A(D) embeddable in P(T) but not A(T): D = Z_3, T = GF(4).
- Proofs deferred to ref. 8: Carter & Vogt, Mem. Amer. Math. Soc. (1980, "in press"). Refs 1-7: Artin; Klingenberg 1956; Skornyakov 1957; Radó 1970; Garner 1972; Daykin 1971; Schilling 1950.
- READ-EXTENT NOTE: PNAS is an announcement; no proofs. The plane theorem cannot be cited as proved from this source alone; the Memoir was not obtained.

## Additional primary reads (2026-10-20, after CV)
- Havlicek, "Weak linear mappings - a survey", arXiv:1210.2053v1 (11 pp., read in full via pdftotext; private/primary/havlicek-arXiv-1210.2053v1.pdf sha256 86dcbc83...b970). Secondary survey: points to Radó 1969 Math Z 110 (non-injective collineations of projective SPACES via generalized semilinear maps) and Machala 1975 (generalization). Lineation literature for total non-injective maps: Radó, Machala, Klingenberg, CV, Brezuleanu-Rădulescu (J. Geom 23, paywalled; not obtained).
- Machala, Cas. Pest. Mat. 100 (1975) 142-154, DML-CZ dmlcz/108761 (14 pp. incl. cover; read in full via pdftotext; private/primary/machala-CasPestMat_100-1975-2_6.pdf sha256 350945b6...5f43). THEOREM (p.145, proof to p.153): every homomorphism chi of projective spaces P(A)->P(B) over division rings F,G, A of any dimension, i.e. (1) collinear->collinear, (2) every line has three points with pairwise distinct images, (3) image contains a non-collinear triple, is induced by a generalized semilinear map (phi, sigma) w.r.t. an R-module W subset A: R total subring of F, phi:R->G ring hom with kernel R_0, sigma:W->B additive, (tx)^sigma = t^phi x^sigma, each point Fx has rep in W*, (Fw)^chi = G w^sigma for w in W*. Satz 1,2 (total-ring facts) cited to Radó [5]; for commutative F they are standard valuation facts.
- Radó 1969/1970, Brezuleanu-Rădulescu 1984, CV Memoir 235: not obtained (paywalled / not located open).
- Harness note: one long pdftotext listing was auto-saved by the tool harness to /tmp/droid-terminal-*/...log (harness behaviour, not an author write).

## Derivation after Machala (author screen, p=2) -- "Theorem D"
- Prop A => theta is a collinearity-preserving map P_H(K)->P_C(L), H=K^2, C=L^2. If (N) every line has 3 points with distinct images and (T) image has a triangle, Machala gives (R,psi,W,sigma).
- Lemma 1: w in W*: W cap Hw = Rw, tw in W* iff t in R^x. Lemma 2: for w,u in W*, theta[w]!=theta[u]: R = {t: theta[w+tu] != theta[u]}.
- Uniqueness U: two triples for the same theta sharing a W*-vector agree (R, psi, W) and sigma up to C^x.
- Gluing: normalise 1 in W*, sigma(1)=1; for x in W*, (psi, X^{-1}sigma(x.), x^{-1}W) also induces theta; U gives xW=W, sigma(xw)=sigma(x)sigma(w). Then W* group, W ring, valuation ring of K, sigma place, K^x = H^x W*, value group 2-divisible.
- Line analysis: (N) <=> (BA) every x notin K^2 has a best approximation from K^2, and (S) beta(kappa\kappa^2) cap L^2 = empty.
- Converse via Prop B. Example: Hahn field kappa((t^Q)), kappa imperfect: noninjective, satisfies all.
- JUDGEMENT: this is Machala + Prop A + the source's own multiplicativity trick (05-fields proof of thm:main), i.e. a classical place theorem plus the pinned proof. The brief warns this pattern is technical. NOT frozen as nominee; recorded as screen. Remaining gap = strata with a collapsing line (Gamma/2Gamma != 0, defect/no best approximation, beta failing (S)).
- Lemma E: plane lineation into a no-three-collinear set has <=3 image points. Example G: rank-2 model; every H-plane image is reduced (triangle) -> collapsing stratum needs reduced-type theory (CV announced; proofs in Memoir, not obtained).
- Example F: odd p, theta = 2*id is compatible, not a lineation (1,x,x^2 independent over C).
- Decision: PREFREEZE.
