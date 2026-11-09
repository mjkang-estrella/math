# Full source target remains unresolved

Status: no complete ordinary proof or counterexample; credit 0. No acceptance authority. Campaign counts read as 3/30 additional, 33/60 total and unchanged.

## Exact target and current-source screen

Byun–Poznanović, *Unimodality and log-concavity of generalized Glasby–Paseman sequences*, arXiv:2604.14639v1 (submitted 16 April 2026), equation (1.4), Conjecture 1.1(a): for **every** positive integer m, positive integer l, and real a>0, the positive sequence

S_r = N_r/D_r,
N_r = sum_{i=0}^r (binom(m,i) a^i)^l,
D_r = sum_{i=0}^r (binom(r,i) a^i)^l, 0<=r<=m,

is unimodal. Unimodality means there exists j in {0,...,m} with S_0<=...<=S_j>=...>=S_m; ties are allowed. The denominator is a full powered row, not (1+a)^(lr). There is no restriction a>=1, and l is not fixed at 2. Endpoints S_0=S_m=1 are included. A valid interior falsifier would have a strict descent at p followed by a strict rise at q>p.

Actual original HTML body, Theorem 1.2, its proof of part (a), and Section 4 were read. Theorem 1.2 covers l=2,a=1; the earlier l=1 results and these cases receive no credit. Section 4 already reports finite-size failures of log-concavity. No rediscovery of those is nominated.

Before significant proof investment the authorized 2026-10-29 04:39 UTC cached complete registry trees were searched (omega Problems and D5, count-ex-machina registry/tree, OpenAI preprints/CONTENTS). The matching omega dossier `glasby-paseman-powered-ratio-maximum.md` was downloaded at its immutable head 67b4fae085cf19003a33f8027410c383b49e5046. Its exact endpoint body `D5/S3/AnalyticClosure/BinomialPoweredRatioMaximum.lean` was then downloaded and read. It states the all-fixed-parameter **maximum asymptotic**, clause (d), permitting ties and assuming no unimodality. No claim of an upstream Lean replay is made. This positively excludes clause (d) from discovery scope, but does not establish global novelty of clause (a).

The closest current successor located is Alex Chengyu Li, *Peaks and Gaussian Limits for Powered Binomial-Sum Ratios*, Zenodo version 22542574, concept DOI 10.5281/zenodo.22542573. Zenodo metadata gives creation/publication 6 September 2026. Actual PDF Theorem 1.1 proves the asymptotic and shifted localization; Theorem 5.1 and its whole proof establish strict log-concavity for l=2, all a>0. Page 7 expressly leaves general finite-size shape separate. Thus the whole square-power route and asymptotic route are publicly closed and excluded. The remaining full clause (a) is the selected lead; this is not a claim that clauses (b)–(d) are all open. Current original arXiv abstract/history still lists v1. Targeted live search found these bodies, not an all-l resolution. This is bounded coverage only, not a novelty clearance.

## Ordinary attack and exact remaining gap

Fix m,l,a in the literal source domain and put u_r=(binom(m,r)a^r)^l. For 0<=r<m, define

Q_r=N_r/u_{r+1}, T_r=D_r/(D_{r+1}-D_r), H_r=Q_r/T_r.

All are positive: Pascal's identity gives binom(r+1,i)>=binom(r,i), strict for at least one positive-weight term, and adds the positive last term, so D_{r+1}>D_r. Direct common-denominator subtraction gives exactly

S_{r+1}-S_r = u_{r+1}/D_{r+1} (1-H_r).

Consequently the **entire** conjecture is equivalent to the impossibility of H_p>1 followed by H_q<1 at p<q. This is a reformulation, not a solution.

One useful factor really is monotone. Put rho_r=u_r/u_{r+1}=((r+1)/(a(m-r)))^l. It strictly increases with r. Q_0=rho_0, and Q_r=rho_r(1+Q_{r-1}) for r>=1. Induction gives Q_r>Q_{r-1}: the base follows from rho_1>rho_0 and positivity; subsequent steps compare the two factors using the previous inequality. This does not alone prove the necessary single crossing.

A sufficient shortcut would be T nonincreasing; this is exactly log-convexity of D, since T_r>=T_{r+1} iff D_r D_{r+2}>=D_{r+1}^2. It is false in the permitted domain. At l=5,a=1,

(D_0,D_1,D_2,D_3)=(1,2,34,488),
D_2^2-D_1 D_3=180>0,
T_1=1/16 <17/227=T_2.

This interior denominator obstruction holds independently of m and blocks extending the square-power moment proof to arbitrary powers. It is **not** a source counterexample.

A more flexible possible route is the monotonicity of

A_r=(r+1)^l (D_{r+1}/D_r-1).

Indeed Q_r/(r+1)^l=a^(-l)(m-r)^(-l)(1+Q_{r-1}) (with Q_{-1}=0) strictly increases; hence monotone A would make H_r=A_r Q_r/(r+1)^l increase and prove unimodality. **No proof of monotonicity of A is supplied**, and it is not adopted as an established theorem, new named conjecture, or credited helper. The equivalent explicit inequality is

(r+2)^l D_r D_{r+2} - ((r+2)^l+(r+1)^l)D_r D_{r+1} + (r+1)^l D_{r+1}^2 >=0.

The missing bridge is an all-r, all-positive-a, all-integer-l argument for single crossing, or some other complete ordinary proof. A single failure of A-monotonicity would only defeat this sufficient route, not the source conjecture.

## Bounded diagnostics and objections

`check.py`: 3,717 exact rational source sequences: 2<=m<=60; l in {1,2,3,4,5,8,12,20,40}; a in {1/10,1/3,1/2,1,2,3,10}. No strict descent followed by rise. These finite checks are not proof; the source already checked many integral cases.

`check_bridges.py`: 4,485 exact adjacent-sign identities plus Q-monotonicity checks for 2<=m<=24, l in {1,2,3,5,8}, a in {1/10,1,3}. Verifies the denominator obstruction above. Also verifies the known sort of finite-size log-concavity obstruction at m=5,l=6,a=1: S_3=1007813/730, S_4=2031251/54850, S_5=1, and S_4^2<S_3 S_5. The sequence is still unimodal. This does not refute eventual log-concavity, whose quantifiers allow finite exceptions.

`check_crossing.py`: 1,560 exact cases (2<=m<=40, l in {1,2,3,5,8,12,20,40}, a in {1/10,1/2,1,2,10}) found no decrease of H. Again no uniform conclusion follows.

Strongest objection: the report has only a reformulation and proof-route obstructions. No nontrivial ordinary bridge currently controls H at all indices and all source parameters. Local Gaussian maxima and eventual localization in the successor do not rule out a valley elsewhere or finite exceptions. A false stronger all-size log-concavity assertion cannot fill the gap. No eligible full outcome is nominated and no Lean investment is warranted.

## Reproduction and limits

Run from this lane:

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python check.py
    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python check_bridges.py
    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python check_crossing.py

Each sets RLIMIT_AS=512MiB and CPU limit 45s/20s/20s before diagnostics, with BLAS/OMP1; exact integers and Fractions only. Initial source extraction failed because bs4 was unavailable. That failure is preserved in failures.json; a standard-library HTMLParser extracted MathML alttext without installing packages. No limits were raised and no numerical evidence is offered as proof.

The dated cached registry coverage and exact hashes are in provenance.json. No GitHub API traversal or repeated requests to blocked routes were made. Direct MathDB was not re-requested after earlier lanes' 403. Its live solution bodies remain an access gap. Earlier full binomial-power literature was not exhaustively body-read; worldwide priority is not asserted. No children, git, shared/other-lane writes, tabs, public posts/uploads/contacts/account changes, or new formal endpoints.
