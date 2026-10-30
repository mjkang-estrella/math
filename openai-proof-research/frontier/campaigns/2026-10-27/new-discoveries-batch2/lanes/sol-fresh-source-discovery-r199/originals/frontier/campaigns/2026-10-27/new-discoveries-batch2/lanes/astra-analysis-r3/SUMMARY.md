# Astra analysis r3 handoff: no qualifying discovery

**Zero new outcomes proposed. No acceptance or count change requested.** Work was solo and all intentional writes stayed inside `lanes/astra-analysis-r3`. No children, git operations, shared/other-lane edits, contacts, uploads, publishing, accounts or access-control bypass.

## What was achieved

The main effort addressed the full source problem, Horwitz math/0007095v1 Section4 Conjecture16, not only the r2 repeated-input family. `HORWITZ-FULL-REDUCTION.md` gives a rigorous equivalent pair of scalar inequalities H0/H1 for **every p,q>0**, corresponding to every distinct positive triple modulo symmetry and scaling. All original means, positive denominators, transformations, and reverse implications are explicit. A further hyperbolic-sine expression symmetrizes the logarithmic numerator. These are reductions, not a proof of their signs and not a discovery claim.

Independently implemented rational interval arithmetic certifies both original source inequalities at seven positive rational triples, including large separation and near-diagonal inputs. It uses exact fractions and a proved logarithm tail bound, with outward rational rounding; no floating point enters the certificate arithmetic. Results and complete rational enclosures are in `checks/rational_intervals.json`. These finite checks do not settle any full conjecture.

Two tempting one-step envelope shortcuts were disproved by exact interval checks: U0(v)<=G(Tv) already fails at v=(1,2,3), and A(Tv)<=U1(v) fails at v=(1,2,100). This prevents those shortcuts from being used as a false proof. The potentially useful stronger-iteration bounds

    U0(v)<=G(T²v),
    P_(1/3)(Tv)<=U1(v),
    A(T²v)<=U1(v)

survived the numerical scan, but **none is proved**. Either lower bound plus either upper bound would give the weak Conjecture15 statement by the source's invariance/comparison facts. Equality remains an additional issue.

## Validation and source limits

- Main gap formulas compared to independent direct divided differences at110 decimal digits on256 widely separated parameter pairs: no target sign failure, relative formula discrepancy<2e-96. This is explicitly nonrigorous exploration.
- Exact fraction interval checks: seven of seven pass for both target inequalities. These certify individual triples only.
- Actual source pp12–13 read and visually checked; current arXiv version/publication metadata rechecked live.
- Actual Pasteczka2024/2025 invariant-extension theorem and comparison proof read. They do not themselves supply H0/H1 in the inspected statements.
- **Material unresolved source gap:** actual2002 Horwitz publication body remains unread, inherited publisher403 from r2. No current novelty clearance is claimed.
- Main secondary lead: actual Byczkowski–Małecki source and partial2013 successor around equation4.6 read. Correct source parameter rho=(n-2)/2, not the database paraphrase. A complex-root search failed with `NoConvergence`; no result or exclusion follows.

Full URLs, audit boundaries and strongest objections are in `SOURCE-AND-NOVELTY.md`; downloaded source hashes and inherited-input hashes are in `provenance.json` and `sources/fetch-log*.json`.

## Remaining gap and formal status

A complete ordinary proof of H0/H1 (or a rigorously certified negative witness) is still missing. Proving a one-dimensional subfamily, any helper, or merely correcting source metadata would not qualify. The unproved full sign assertions are displayed verbatim in the reduction note so a next worker need not repeat this algebra.

No Lean module was started: the task explicitly required a complete ordinary proof before meaningful initial Lean work. There is no claim of a literal source endpoint, standard-three axiom audit, independent review, paper, or extracted replay. The requested Lean4.34.1/mathlib pin remains the required environment if a complete eligible proof is found later.
