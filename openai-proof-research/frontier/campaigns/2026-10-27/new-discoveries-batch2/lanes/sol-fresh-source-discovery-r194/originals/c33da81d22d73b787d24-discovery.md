# r164: three screens, zero eligible full-scope resolutions

Credit 0. No fresh substantive source resolution, eligibility clearance, Lean implementation, paper, or acceptance is claimed. Counts remain 9 additional /39 total, next40. Work is confined to this lane. Actual research date is 2026-10-30 UTC /2026-10-29 America/Los_Angeles.

## Screen 1: Ma–Weigert, Conjecture 4.6

Read the actual published full HTML of *Complete monotonicity of log-functions*, Analysis and Mathematical Physics 15:141 (2025), DOI10.1007/s13324-025-01136-9. The exact question concerns every degree bound n, f(x)=p(log x)/x on x>0, and the regions D_k where (-1)^k f^(k)>=0 everywhere: D_(k+1) subset D_k and their intersection is the completely monotone cone. The printed final conjecture's quantification over real x is interpreted using the positive domain stated throughout the paper; this domain correction earns nothing.

The original r44 discovery body was reopened completely. Its Question1.2 screen is a different question in the same paper, already answered by source Theorems1.3/1.4. That earlier exclusion does not itself settle Conjecture4.6. The actual current Omega LogFunctionMonotoneChain.lean and its complete 7,965-byte proof were obtained at observed head 1b21e83cbf01011a1f0c1520c421fe6dfd076a32. It proves exactly this all-degree chain and intersection by the polynomial recurrence q_(j+1)=(j+1)q_j-q_j'. The minimum/leading-coefficient proof in the body supplies the essential implication aq-q'>=0 => q>=0 for a>0, not just a status badge.

An independent ordinary classical bridge is also complete: every derivative f^(j) is x^(-j-1) times a polynomial in log x, and hence tends to zero at infinity. If (-1)^(j+1)f^(j+1)>=0, then h=(-1)^j f^(j) is nonincreasing and has limit zero, so h(x)>=0. This includes j=0 and supplies the intersection claim. Polynomial-log growth versus positive powers justifies each limit. Thus this candidate is both publicly answered and a routine calculus adaptation. No discovery or formalization credit.

## Screen 2: Hao Li, arbitrary even-order Split CIF convexity

Primary actual full statement: arXiv:2606.27260v1, Section2.1 Eq.(1), Section2.2 Eqs.(7a,b). Current abstract history lists only v1, submitted 25 June2026 16:44:20UTC. For every dimension, symmetric PSD A,B,C,D with A+B and C+D positive definite, put

P(w)=((A/w+B)^(-1)+(C/(1-w)+D)^(-1))^(-1).

Both (log det P)^(2k)>=0 and (tr P)^(2k)>=0 are conjectured for every k>=1 on 0<w<1. Endpoints use limits; no new endpoint claim is made here. Source Section3.1 proves the constant case A=C=0 and the affine-inverse case B=D=0, by actual all-order inverse derivative formulas. Source AppendixA expands low-order noncommutative derivatives. These do not by themselves resolve general mixed inputs.

The public current registry has the EXACT general semidefinite all-k statement. Fetched the actual 49,714-byte SplitCovarianceIntersectionEvenConvexity.lean, rather than inferring proof from the Blueprint badge. The body constructs the full affine pencil with top-left w A^-1+(1-w)C^-1, hidden diagonal blocks w A^-1+B^-1 and (1-w)C^-1+D^-1, and couplings -w A^-1, -(1-w)C^-1. Schur complement and inverse-corner identities identify P and det P=det K/det M. The all-order affine inverse congruence proves trace signs. The weighted even-power compression inequality proves the logdet signs. The final regularization-continuity argument extends positive definite inputs to the exact PSD hypotheses. This is an actual matching proof body predating this lane, not a nearby special case. No independent kernel replay or audit of all 49KB is asserted. It is sufficient to block fresh discovery investment; no attempt to claim the same pencil proof as ours.

The original exact-title/claim/word-boundary author scan found no earlier local disposition for this target. That absence is immaterial in view of the actual public body. The two mistaken guessed repository URLs returned404, then were corrected from the qualified r157 receipts. No404 was used as absence evidence.

## Screen 3: Matkowski, full Conjecture2.4 — reopened, still unresolved

The publisher PDF is the actual nine-page published *Convexity of Generators of Lp-like Paranorms*, J.Convex Analysis33(2026),293–301, DOI10.68381/jca33018. Received7February2024, accepted7April2025. Its complete text, Theorems2.1/2.2 and proofs, Example2.3, Conjecture2.4 and Remarks2.5/2.6 were read. For every measure space having two disjoint sets of finite positive measure and every bijection phi:(0,infinity)->(0,infinity), define P_phi(f)=phi^-1(integral over nonzero support phi(|f|)), with zero for zero support. If P_phi is subadditive on ALL nonnegative simple functions, must phi be convex? Monotonicity, differentiability, normalization, and strictness cannot be added to that endpoint.

Before sustained work the ID/claim scan reopened r116's complete original discovery. It already pursued precisely this source, so this is explicitly a reopened old target, not a fresh nomination. Expanded word-boundary Matkowski screening also locates the different scalar functional equation373182 and beta/gamma characterization references. These are not paranorm resolutions. Theorem2.1 needs increasing phi, strictness and infinite asymptotic slope; Theorem2.2 needs masses 0<min(a,b)<=1<=a+b. Neither covers the two atoms of mass1/10 considered below. The exact published source itself, not an abstract, establishes these known-case limits. A full current semantic registry clearance for Matkowski remains unavailable: inherited capped comparisons persist and the obtained Carlen–Lieb body is a matrix trace theorem, not a theorem about arbitrary scalar generators. No eligibility PASS follows.

### New diagnostic reduction on the old candidate

Keep the r116 candidate

phi(t)=t^2/(1+t) -(1/1000) [t^2/(1+t)^2]/[1+10000(t-2)^2].

r116 proves positivity, strict increase, onto, and nonconvexity; our exact symbolic differentiation independently confirms phi''(201/100)=-17578551005/8208541201<0. No inference about P-subadditivity follows from this.

For two equal atoms a=1/10 let F(u,v)=phi^-1(a(phi(u)+phi(v))), extending phi(0)=0. Near zero phi(t)=c t²+O(t³) with c=1-1/40001000>0, hence F(epsilon h)/epsilon -> sqrt(a)||h||_2. If F is subadditive, for every x>0 coordinatewise and h>=0,

DF(x)h <= sqrt(a)||h||_2.

Indeed apply F(x+epsilon h)-F(x)<=F(epsilon h), divide by epsilon and take epsilon down to zero. Since its gradient is positive, choosing h=gradient F(x) gives the necessary pointwise inequality

a[(phi'(u))²+(phi'(v))²] <= [phi'(F(u,v))]².

This is a useful falsification condition, not a sufficient condition. The bounded 60-digit grid of196 positive pairs has positive margin throughout; minimum observed a-||gradient F||² is about0.000110421 at u=v=.001. There are no interval enclosures and no claim of coverage between points, at zero, or infinity. Such a violation, if rigorously found, would reject only this generator, not Conjecture2.4.

The tempting replacement by convexity of F is wrong even for the source's established subadditive example phi0=t²/(1+t). On one axis at a=1/10, F0(1,0)=1/4 and F0(2,0)=(1+sqrt31)/15<1/2. Thus F0(1,0)>[F0(0,0)+F0(2,0)]/2. More generally a convex subadditive continuous F with F(0)=0 would have to be homogeneous (convexity and subadditivity force equality at integer dilations, then rational dilations and limits), whereas F0(t,0)/t tends to sqrt(a) at zero and a at infinity. This rules out a convex-functional shortcut without prejudging the source conjecture.

For fixed s,t>0 and T->infinity, phi(T)=T-1+o(1) and phi^-1(z)=z+1+o(1). Consequently

F(s+t,T)-F(s,T) -> a[phi(s+t)-phi(s)].

Subadditivity would require a[phi(s+t)-phi(s)]<=phi^-1(a phi(t)). This boundary test and the gradient test together still leave the full four-variable inequality. No claim that they imply it is made. A robustness proof for a localized perturbation needs uniform triangle-margin control near vanishing arguments, both-large arguments, and mixed scales; compact finite tests do not provide it.

### Exact remaining gap and strongest objection

We have NOT proved F(x+y)<=F(x)+F(y) for every x,y in [0,infinity)^2, nor exhibited a violating pair. That universal inequality for the displayed admissible nonconvex bijection would refute the full source. Alternatively a proof of the conjecture must handle arbitrary bijections and arbitrary nontrivial spaces, not merely the smooth two-atom example. Public-source/registry eligibility remains HOLD independently of the mathematical gap. The strongest objection is therefore decisive: none of these three screens is a fresh eligible complete resolution. No fourth claim was screened and no PROOF.md is warranted.

## Audit scope and chronology

history-receipt.json unions qualified r157/r159 records and r162 supplemental records and refreshes changed/new original SUMMARY/discovery/PROOF/review/DECISION bodies across all dates. It records1671 paths,19 changed/new,43 lexical hits in the final scan, with exact hashes and all hit bodies locally retained. No whole r111–r113 lane or arbitrary date cutoff is excluded; nine original scientific paths from those lanes remain. Inherited copy aliases are provenance aliases, not independent mathematical evidence. Lexical scanning is not complete semantic understanding. Full original r44/r116 bodies supply the actual matched dispositions; other author-only aliases cannot clear a new target.

Observed current heads: Omega1b21e83cbf01011a1f0c1520c421fe6dfd076a32 and OpenAI4eaee87548250b2682affda7d05d947c05554bae. The supplied b627 head advanced; one comparison b627->1b21 reports27commits17files. No repeated HEAD chase. Actual proof files were pinned to the new observed head. Exact last-path-change commits and timestamps are preserved in cif-history.json/log-history.json and provenance.json; last-change dates are not asserted to be first publication dates. Inherited aa026->a19a and a19a->490f 300-path caps remain. No old-tree or path-absence clearance is claimed. Current proof exclusions are affirmative body matches and do not depend on absence.
