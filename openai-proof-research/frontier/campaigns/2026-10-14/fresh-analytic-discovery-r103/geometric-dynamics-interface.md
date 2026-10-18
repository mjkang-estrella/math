# Geometric birth–death dynamics: pre-freeze interface

Family224's actual near-critical proof is stronger than its headline. Its Section05 expansion and Section07 common calibration accept arbitrary centered weights on finite color-history spaces. Consequently changing monotone histories to independent color-refresh histories does not by itself supply a substantial operation. This screen does not nominate frozen-color dynamics.

The selected distinct mechanism changes the Poisson geometry itself. Start from stationary fair-colored Poisson nuclei of intensity epsilon^-2. Each nucleus dies at rate1; independent fair-colored nuclei are born at intensity epsilon^-2 dx dt. Every snapshot has the critical marked Poisson law. Cells are recomputed, so a death or birth changes both cell shapes and connectivity. This is the standard Poisson OU dynamics, not a new model.

## Exact local identity, with primary credit

For a fixed old configuration and a proposed new site z, let F0 be an increasing crossing indicator before addition, and Fb,Fw after adding z black or white. Deterministically Fw<=F0<=Fb: a black addition only enlarges the black set, while a white addition only shrinks it. Therefore

 E_color[(Fadd-F0)^2]=(Fb-Fw)/2.

Mecke gives birth crossing-flip intensity EN_e(Q)/2, where N is the COLOR-pivotal count. Reversibility gives the same death intensity. Total unit-speed birth–death flip intensity is exactly EN_e(Q), twice that of rate-one color refresh. Thus time acceleration t->r_e t/2, r_e=1/EN_e(Q_*), matches color-refresh time t->r_e t, including the factor2.

This exact intensity comparison is already PAID: Bhattacharjee–Peccati–Yogeshwaran, arXiv2407.13502v1, Proposition3.15 and its use of Proposition2.17 identify the same factor through spectral/pivotal processes. The local proof here verifies conventions; it is not proposed novelty. Their full Section3.4 also gives covariance domination by frozen dynamics (Proposition3.16) and sharp small/large noise scale (Theorem1.4), not the full normalized critical-time process law.

## A multi-observable defect that scalar calibration does not determine

For two increasing Boolean crossings F,G set pF=Fb-Fw, pG=Gb-Gw. When both are insertion-pivotal their inserted black state is (1,1) and white state (0,0), but the OLD state can in principle be (0,1) or (1,0). Exact enumeration yields

 E_color[(Fadd-F0)(Gadd-G0)]
   = (pF pG/2) 1_{F0=G0}.

Thus a scalar flip-rate calibration does not determine cross-observable generator coefficients. The discrepancy from the common-color insertion kernel is precisely (pF pG/2)1_{F0!=G0}. A proof that its normalized spatial integral vanishes for separated macroscopic tests would be a necessary first geometric replacement interface, not a conclusion of the one-observable identity.

The source amplitude companion describes rank-one transmission through annuli with exactly four surviving interfaces; its Section00 explicitly separates an enhanced signed cancellation for fair geometric insertions from the leading four-interface sector. The near-critical sewing proof Section06 protects inactive replicas against changed cells under inside/outside exchanges. These operations are promising but do not literally give the birth–death space-time expansion: inserted/deleted sites appear in some time slices and not others, and the tessellation changes across slices. A source color-history kernel has one fixed tessellation and cannot silently be used for this operation.

The possible new route is (i) reduce geometric update histories to a single connection bit on successful four-arm screens, (ii) bound multi-state defects by extra-arm events uniformly over update histories, (iii) control repeated updates and close spatial birth/death clusters, and (iv) obtain path tightness and two-replica conditional concentration. These steps remain unproved. A mere comparison of two-time covariances is insufficient.

## Actual reading limits at this checkpoint

Source220: complete introduction, and geometry.tex from its crossing estimate (5) through the end. That proof already supplies super-polynomial regeneration duration tails, so ordinary finite-moment CLT transfers were excluded before proposing a target. Other220 files retained but not read fully.

Source224: full near-critical introduction; expansion.tex1–190 (exact histories, arbitrary signed kernels, uniform coefficient theorem and beginning forest proof); identification.tex1–158 (full common-calibration proof and square normalization); sewing.tex545–600 (geometry protection and start of annular trials). Full pivotal-amplitude introduction. Cardy and remaining companion bodies retained and authenticated, not yet semantically read. No full-source read is asserted.

Primaries retained separately: GPS1305.5526v4 extracted1–135 and385–435, including Theorem1.8 dynamical triangular path limit and1.9 Markov/reversibility; Vanneuville1906.12256v2 extracted1–120, actual frozen/moving dynamics definitions; Bhattacharjee–Peccati–Yogeshwaran2407.13502v1 extracted1–110,345–377 and2231–2354 (complete Section3.4). Their earlier spectral proof sections are referenced but not read in full. Further primary/source integration remains required before a complete author proof.

All pinned text identities are in source224-receipts.json against the complete canonical tree; third-party bodies are private/ignored. Bounded history excluded147/I138,236/r14–r18,225/r21,096/R012,084/I36–I37,364/kinetic,351/r55,217/O217 and368/I07–I331. No exhaustive semantic or literature clearance is claimed. Family224 history currently shows near-critical bounds rather than this geometric process operation; absence of a lexical hit is not contribution evidence.
