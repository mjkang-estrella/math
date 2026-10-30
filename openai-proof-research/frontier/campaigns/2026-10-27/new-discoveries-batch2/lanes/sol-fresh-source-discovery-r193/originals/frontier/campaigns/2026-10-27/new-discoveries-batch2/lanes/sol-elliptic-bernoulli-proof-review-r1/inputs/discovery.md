# Disposition: routine classical corollary, credit 0

Full literal arXiv Conjecture2 admits the classical formula

    Â^(m)=(2m−2)! (6g₃∂g₂+(g₂²/3)∂g₃)c_m,
    B̂^(m)=2m(2m−2)!c_m,                 m≥2,

where ℘(t)=t⁻²+Σ_{m≥2}c_m t^(2m−2). The coefficients c_m are positive rational
polynomials by the Laurent recurrence printed in the source itself. The invariant
derivation has positive polynomial coefficients and preserves coefficientwise
positivity. This settles all orders as a short classical corollary, not an eligible
new discovery. PROOF.md supplies the complete analytic period bridge and a
second, independent ODE verification of the classical identity. Stop investment.

## Exact source scope and conventions

Grosset–Veselov arXiv:math-ph/0508066v1, 31 August2005, §5 Definition(21),
pp11–13; §7 Conjecture2 p17. Current landing page lists only v1. Definition is
ℬ₂ₙ=(1/2)∮γ(∂z^(n−1)℘)²dz. Γ:Y²=4X³−g₂X−g₃, γ avoids poles;
2ω=∮dz, η=−(1/2)∮℘dz. No real-order or positive-numerical-invariants condition.
The conjecture is ℬ₂ₘ=(−1)^(m−1)(Â^(m)ω−B̂^(m)η), the two universal
polynomials having positive rational coefficients on their supports.
A nonoccurring monomial has coefficient zero; B̂^(1)=0 is legitimate, as zero
period polynomials already occur in Proposition4. No endpoint defect is nominated.
Weights are 2a+3b=m+1 for Â and m for B̂, using weights2,3 for g₂,g₃.

Proposition6 uses Halphen coefficients with signed correction terms.
Proposition7 is the IBP identity (−1)^(n−1)D_n[K]/2, D_n=x A_(n−1),
A_(n−1)(℘)=℘^(2n−2). Proposition4 proves positivity only of K_n,
not of this signed combination. We do not conflate them.

Important printed normalization discrepancy: the PDF p13 actually prints
ℬ₂=3g₂ω (visually checked; not merely extraction damage). Definition(21),
K₂=g₂ω/6 and Proposition7 give ℬ₂=g₂ω/12. This does not alter any sign and
is not used for credit. Orders m=2..8 printed in that display agree with the
literal checker and formula. For example m2 has Â=3g₃/5,B̂=2g₂/5;
m3 has Â=2g₂²/7,B̂=36g₃/7. The proof uses literal Definition(21) throughout.

## Latest/published source and followups

VoR: International Mathematics Research Notices 2006, article62120,31pp,
DOI10.1155/IMRN/2006/62120. Oxford public metadata reports received4Nov2005,
revision2Mar2006, accepted9Mar2006 (metadata publication date1Jan2006).
PDF endpoint403; no bypass attempted. Author institutional hdl.handle.net/2134/565
returned202 with zero bytes; treat as an access/challenge hold, not a manuscript.
Thus published-body comparison remains HOLD; no assertion that VoR retained
exact labels/text or that this arXiv is an accepted manuscript.

Read the current Landau and Loughborough author publication lists. Closest
companion is math-ph/0508068, published Proc.Edinburgh Math.Soc51(2008),635–650.
Both preprint and publisher PDF obtained. Actual Theorems3–5 and final discussion
read: these concern traces of quantum-top powers / odd elliptic Bernoulli
polynomials, with a different parameter s. The final discussion expressly
separates that family from the even complete-period construction. It supplies
no direct resolution of Conjecture2. No later explicitly titled resolution found
in these bounded author lists/searches. This is not worldwide followup clearance.

## Closest classical-body check and chronology

Buchstaber–Bunkova arXiv:1204.3784v1 (17Apr2012), §8.4 p15 Theorem37,
explicitly called Weierstrass's theorem, states
(1/2)σ''+(g₂z²/24)σ−(6g₃∂g₂+(g₂²/3)∂g₃)σ=0,
with exactly our curve/period conventions on the same page. Actual whole relevant
body read and rendered. Taking a logarithm and two z derivatives gives the
classical identity needed here. The period product identity follows just by
matching two double poles and two residues. Combined with the Laurent
recurrence already in the2005 paper, positivity is immediate. We found a
routine subsumer bridge, not an explicit prior-publication claim of the same
conjecture. The proof also verifies the invariant identity directly using the ODE.

## Registry and overlap limits

Current registry-screen.json records unchanged AIM/OpenAI/Count/Omega-main
heads and the19commit/8file Omega-dev delta from r37. No relevant delta path.
Inherited complete subtree/tree screens and exact hashes retained, but NEVER
whole Omega-dev coverage. Searches include elliptic, Bernoulli, Grosset,
Faulhaber, Weierstrass. Current clopen Bernoulli/elliptic filtered claim listings
and Colbrook's current author publication descriptions read, not only pathgrep.
These describe unrelated group-testing/cocycle, elliptic PDE or spectral claims.
The OpenProblemsInNLA recursive tree is TRUNCATED: no completeness assertion.
Its path matches are unrelated probability Bernoulli modules. No relevant
actual claim was found requiring a new paper-body retrieval; r37's actual
TR-26/MF-03 proof-body reads concern unrelated discriminant/Pade questions.
Registry absence and empty MathDB solutions are NOT novelty evidence.
Ledger/prior context and lane-family search found no accepted elliptic-Bernoulli
family; prior r37 only screened this lead. No counts or acceptance files changed.

## Checks, objections and stopping rule

Twenty exact derivative-square reductions agree with independent IBP reductions
and with the classical formula;19 Laurent-convolution coefficient identities
also agree. run-checks.sh is runnable with stdlib alone, hard512MiBAS,
BLAS1,40CPU/50alarm/55wall. No huge enumeration. These are diagnostics only;
PROOF.md is the all-order argument. Strongest objection is the analytic/source
bridge, fully spelled out there, and the inaccessible VoR, candidly left on HOLD.
No Lean, helper, paper, nomination or acceptance request. Credit0;5additional,
35total unchanged. Root independent review remains required for any integration.
