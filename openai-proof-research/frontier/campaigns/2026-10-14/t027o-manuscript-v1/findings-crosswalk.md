# Manuscript findings crosswalk

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Author response, not an independent verdict or acceptance. Frozen r36 is unchanged. The theorem is all g>=2 and r>=2, one actual SL_r(O_L) representation, one orientation-preserving Mod orbit, entire complex character variety. No generic-input, marked-locus, punctured, finite-rank or union-of-orbits replacement.

## Proof review E1–E6

| Finding | Manuscript location | Exact implementation |
|---|---|---|
| E1 | Lemma 4.1, public/sections/04-linear.tex | H12=H21=H23=H31=1; **all other off-diagonal entries zero**. The two projected square entries differ by exactly one. |
| E2 | Lemma 6.2 | Each band spectral map explicitly avoids its discriminant as well as the Weyl images of all nontrivial character kernels. |
| E3 | §1.3 and §7, before Lemma 7.3 | Ambient neighborhood is in the smooth irreducible Goldman D/G locus. For Ω=Re ω, real Hamiltonians of Re h and Im h correspond to X_h and −iX_h. Goldman Lemma 1.11 and Theorems 4.3–4.7 are identified. Ideal preservation and holomorphic ODE uniqueness handle singular Z0. |
| E4 | Lemma 3.1 and following paragraph | The maps b→ba^m and d0→d0c^n are identified as actual annular twist powers, with cut-and-follow description and exact relator identities. The seed twist a→ab is a twist about b. |
| E5 | Proposition 4.3, equation (4.3) | The global augmented map on sl_r⊕h⊕h is written explicitly. Its injectivity is equivalent to the residual condition plus h∩h_C=0. |
| E6 | Proposition 5.2, equation (5.9) | After core gauge, core variation is already zero; extra traces detect only δA_i and δB_i. No subtraction is asserted. |

## Required contribution credit R1–R4

| Finding | Manuscript location | Actual source reading and resolution |
|---|---|---|
| R1 | §1.1–1.2; references [4],[5] | GT PNAS Theorem I and §2.4 higher-rank remark read in actual PMC body; detailed preprint abstract/contents read. Rank-two strength and the unproved SL_d extension are explicit. PNAS exact title corrected to **Closure of orbits...**, distinct from preprint **Orbit closure...**. |
| R2 | Abstract; §1.2; Appendix A.2 | The theorem is stated as a special case of the anticipated higher-rank picture. Claim restricted to new to this project, bounded search, no worldwide priority clearance. |
| R3 | §1.1; references [6],[12] | Actual Litt §5.4.10–5.4.14, including full Thm5.4.13 proof sketch, read. Shimura/unitary-conjugate route credited. GT exceptional-locus caveat attached to PX02b Thm1.4; that uncaveated theorem is not a proof input. Rank2 is proved by cited CL actual representation construction and dense-orbit theorem. |
| R4 | §1.2; references [1],[9] | Actual MO332994 question/answers/comments read as discussion pointers. Newly retrieved BKMS NYJM paper: pp242 and248–249 (Prop1.2, Thm5.1, full proof of Prop1.2) read. Its published statement is GL_n infinite-image fixed characters, not the distinct MO high-rank dense-image assertion. Neither is a proof input. |

No verdict is asserted by this author crosswalk. Parent/independent manuscript review decides whether these required credits are discharged.

## Other credit and source precision

- Source027 already gives all-rank integral-set density and the fixed-spectrum-fiber saturation/Baire/submersion operation. §1.2 and §7 credit that operation.
- §1.3 expressly imports SL_r irreducibility from the **intermediate assertion in the proof** of `prop:surface-irreducibility`, not from its GL_r statement. Canonical surfaces.tex125–265 read, especially197–248 and249–258.
- Pickrell–Xia Prop2.1.24/Lemma2.1.34 are next to §5, with compact/generic/centralizer-power distinction. Loewy/Mantelos credited next to Lemma4.2; Loewy body remains unread and is not used as an axiom.
- Rank2 is entirely credited to Coccia–Litt. The golden-ratio unit meets their actual Prop5.0.1 hypothesis; their Prop3.1.10 supplies single-orbit density. No new rank2 contribution claimed.

## Scoped formal review F1–F4

- F1: Appendix A.1 says the rational control prevents deleting genericity, not that every triangle inequality is necessary in every larger matrix.
- F2: Appendix A.1 and Lemma4.2 make the lower-order identities explicit before identifying the pair/cycle expressions with minor derivatives. Reviewer derivative-bridge additions are distinguished from the author package.
- F3: no formal build is rerun by this manuscript author. Any documented formal invocation uses `GIT_OPTIONAL_LOCKS=0`; receipt flags for network/cache are constants, not measured evidence. The formal reviewer separately checked actual axioms and cache state; the author scanner is not advertised as a general security audit.
- F4: no strengthening is attributed to the frozen formal author's controls. Its controls tested exit codes; the reviewer checked diagnostic reasons. The manuscript's separate inventory controls check both exit status and expected reason.

These are presentation/provenance clarifications within the reviewed proof. No substantive mathematical change or additional theorem hypothesis was introduced. Parent author assistance and the superseded pre-candidate word route remain recorded in the frozen provenance, not silently rewritten.
