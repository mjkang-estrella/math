# Review implementation crosswalk

Role: author implementation, not independent checking. The theorem quantifiers in the copied frozen original-scope.txt are preserved. No source packet was edited.

## Full-proof review E1–E8

| Item | Manuscript implementation |
|---|---|
| E1 reduction order | §7 explicitly compresses first, selects representatives, dilates, applies the finite estimate, then takes the trace-norm limit. |
| E2 universal moment estimate | §3 records m^(-q), word norm ≤1, all m^(2q) words, and the bounded Hoeffding regime. |
| E3 repeated Wick indices | §2 states repeated-index Isserlis identity and gives crossing-register contraction. |
| E4 changed parameters | §5 gives p/Dp/D²p without sqrt(S), DB_s, feature and angle errors, repair logarithm and mesh. |
| E5 cube inequality | §6.2 normalizes coefficients by sqrt(2/pi), proves contraction, obtains sqrt(pi/2). |
| E6 arbitrary H | §7 proves trace-class compression convergence and handles nonseparability. |
| E7 constant convention | Theorem 1.1 has c^(-1); the surrounding prose fixes C accordingly. |
| E8 explicit selector constant | Lemma 4.1 displays 2sqrt(8e) N t sqrt(q/m)+2e. |

## Contribution r1 editorial E1–E5 and RQ1–RQ4

The c^(-1) convention is fixed. §§2–3 credit operator Khintchine/Wick and design antecedents (Haagerup–Pisier, Buchholz, Seymour–Zaslavsky). Matrix M_s/P_s, geometric B_s/R_s and Hilbert features are distinct throughout. Appendix A discloses Tropp as earlier browser-only orientation, and the companion as keyword-screened rather than proof-read.

RQ1: §8.1 treats NPS, Naor–Young, KNT Theorem34 and quantum expansion; §8.2 corrects CEE to a pushforward pair-average bound. RQ2: abstract, §§1 and8 limit novelty to project/bounded search and disclaim Heisenberg/quantum-question claims. RQ3: §8.3 credits sharp cotype and nonlinear smoothing and gives the exact ≤3 grid average and six-point CND violation. RQ4: §1 states method-shaped exponent/chart choice, honest freeze chronology and weaker diagonal ell1 consequence.

## Contribution r2 required R2-A–D

| Item | Manuscript implementation |
|---|---|
| R2-A | §8.2 retains corrected CEE pair-average reading; proves cap 2 t^(-1) max log(e+1/sigma_i); explicitly rejects the earlier unjustified O(loglog number-of-classes) cap; credits L1/S1 type symmetry and identifies the polynomial cancellation versus influence-representation debt. |
| R2-B | §8.3 gives the actual diagonal sqrt(m) Gaussian/ell2-gradient loss; distinguishes upper Gaussian estimate from cotype; states the missing torus pair-law map and local-jump conditions; no impossibility claim. |
| R2-C | §1 qualifies every bi-Lipschitz consequence. §8.3 derives torus distortion sqrt(d)/64 from JLW Cor6.1, then uses MN Lem6.12 to obtain the stronger general-metric grid bound c sqrt(log N/loglog N). Only negative-type specialization could be new under bounded-search wording. |
| R2-D | All preceding RQ items appear in the manuscript itself. JLW arXiv2610.21445v1 is credited as posted October15, before this candidate. KNT, quantum expansion, method-shaped exponent and weaker ell1 consequence remain explicit. |

Optional r2 E2 is implemented: JLW Bessel, dilation and finite-rank steps credited. Optional E1 expander strengthening and E3 NPS S1→Sq non-reduction are not added; the required conclusions do not depend on them. The original six-point certificate is retained with its exact limitation.

## Scoped formal review

§9 records PASS_SCOPED, 31+15 declarations, actual versus abstract zero-threshold distinction, reviewer-added noncommuting interface checks, eigenbasis-choice caveat and trusted cached objects. It lists all unformalized inputs and makes no full formal proof claim. Optional formal changes were not made to the immutable formal packet.

The full-proof and contribution gates review prior frozen mathematics/response. This manuscript remains for separate manuscript review; these implementation statements are not a self-issued pass.
