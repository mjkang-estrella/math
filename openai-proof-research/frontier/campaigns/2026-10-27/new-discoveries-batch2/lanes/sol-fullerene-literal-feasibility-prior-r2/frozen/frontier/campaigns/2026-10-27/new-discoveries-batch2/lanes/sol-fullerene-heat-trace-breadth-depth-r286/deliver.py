from pathlib import Path
import sys,runpy,json,re,hashlib,subprocess,datetime
L=Path(__file__).resolve().parent
sys.argv=['work','freeze',str(L.parent/'sol-primary-diverse-certifiable-scout-r285/primary/fullerenes.pdf')];ns=runpy.run_path(str(L/'work.py'));freeze=ns['freeze'];sha=ns['sha']
# Freeze the primary PDF and every acquired scientific body before report extraction.
for p in (L/'primary').glob('*.pdf'):freeze(p)
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-euler-turan-final-review/fresh/trureturing')
terms=r'fullerene|Buchstaber|Spodarev|Coutinho|Kornowski|Shamir|Dimca|Thamrongthanyalak|Ganikhodjaev|Rozikov|Bregman|1.almost.greedy|1.semi.greedy|ordered Banach|Cuenin|Goel.*Hess|Mussi|Caruso.*Michelangeli'
cache=[]
for p in (R/'Problems').glob('*.md'):
 if re.search(terms,p.read_text(errors='replace'),re.I):
  q=freeze(p);cache.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=sha(q)))
(L/'broad-cache-hits.json').write_text(json.dumps(cache,indent=2))
# Preserve complete primary statement contexts, with PDF-page/line locators.
specs=[
('fullerene','2410.19322v1','Bille–Buchstaber–Spodarev','Conjecture 3','For every fixed alpha,beta in (0,1), character equality iff dual-fullerene isomorphism; feasible original orders may differ.','FULL mathematical refutation; rank 1. Exact crossing below. Entire-function equality is a different assertion.'),
('free-curves','2312.07591v1','Dimca','Conjecture 3.1','Freeness of complex projective line arrangements is determined by the intersection lattice.','Park: Terao endpoint, 40-year problem; no new universal mechanism. Do not count singularity or weak-combinatorics variants.'),
('quantum-walk','2404.02236v1','Coutinho–Guo','2.1 Open Problem','For graphs with perfect state transfer, improve the universal cubic edge-versus-diameter growth to m=Omega(D^k) for some k>3.','Hold: finite spectral bounds do not supply a supercubic universal exponent. Strong cospectrality alone is not sufficient.'),
('friedrichs','2406.05777v1','Caruso–Michelangeli','QUESTION 2','Identify additional assumptions on closed realizations of joint abstract Friedrichs operators under (4.1) that transfer normal-equation Krylov solvability to standard Krylov solvability.','Park: sufficient-conditions endpoint is open ended; scalar symmetric-part and compatible smooth-vector case is already provided in the body, lines 606–611. Cached quantum Krylov-complexity proof concerns another object.'),
('gradient','2406.13888v1','Kornowski–Shamir','Open Problem 1','Does one infinite stepsize sequence give a dimension-free anytime T^(-alpha) error bound with alpha>1 uniformly over all smooth convex functions?','Hold: a schedule tuned to final horizon does not answer the anytime quantifier. Current successors not exhaustively screened; not ranked.'),
('bandits','2407.06321v1','Mussi–Drago–Metelli','3.2 Open Problem 2','Find concentration bounds tight for Bernoulli observations under the bounded-RKHS and bounded-kernel hypotheses of Assumption 2.1.','Park: tightness and estimator not pinned to one exact minimax endpoint; do not count ordinary subgaussian concentration already printed in Eq.(2).'),
('greedy','2408.08935v1','Andrea García','Question 3','Is 1-almost-greediness equivalent to 1-semi-greediness for Banach and quasi-Banach spaces?','Hold: bi-monotone 1-semi-greedy to 3^(2/p)-almost-greedy Theorem 4.20 does not establish constant 1. No full-scope basis construction or proof here.'),
('schrodinger','2409.11285v1','Cuenin–Frank','Question 1.','For d>=1, 0<gamma<1 (gamma>=1/2 if d=1), sigma>d/2, does the displayed weighted complex-eigenvalue Lieb–Thirring estimate hold for every V in L^(gamma+d/2), uniformly in h>0?','Park: universal analytic estimate; tensor or scalar examples do not give a complete sharp estimate.'),
('ordered-banach','2409.19768v1','Jochen Glück','Open Problem 2.5.','If every increasing net with a supremum converges to it in norm in an ordered Banach space, must every order-bounded increasing sequence converge in norm (Levi property)?','Rank 2, provisional only. Attempt a cone whose bad bounded nets have no supremum. Normality is already forced by Remark 2.6; a nonnormal-cone example fails. Need all-net proof and successor/registry clearance.'),
('toric','2411.06468v1','Goel–Hess–Kuhlmann','Open Problem 1.','Give a membership test for every strictly separating intermediate cone Ci in filtration (6), preferably via Gram matrices.','Park: intrinsic membership characterization is not supplied by ordinary SDP; source states such cones are not spectrahedral shadows. No uniquely specified complexity target.'),
('fixed-point','2411.14661v1','Masato Fujita','Theorem 1.1.','Does definable completeness and strong Banach fixed point property imply o-minimality?','Exclude as publicly resolved: source gives a negative answer using definably complete locally o-minimal non-o-minimal expansions, Theorem 1.1 and curve-selection proof. This is not an unresolved survivor.'),
('semigroup','2411.16284v1','Trevor Jack','Problem 9.4','Is there a finite semigroup whose Otto conjugacy is a congruence but whose quotient is not cancellative?','Exclude exact cached proof duplicate. FiniteOttoCongruence.lean defines the literal witness relation, uses idempotent powers, and proves result : claim. Infinite example does not refute the finite theorem.'),
('fermat','2412.19338v1','Xu–Mandal–Biswas','Open problem 1.1.','Do the source Fermat-type PDDEs (1.3),(1.4) have finite-order transcendental entire solutions on C^2 when n>2,m=1?','Exclude: this paper expressly resolves this question in its main theorems; Theorem 2.2 has a no-solution branch m1>=3. No result is claimed from a bare open-problem label.'),
('bregman','1003.3127v1','Bauschke–Macklem–Wang','Problem 3.','Does a full-domain nonquadratic Legendre function exist such that every nonempty closed convex subset is right-Bregman-Chebyshev?','Park pending successor and classical affine-convexity-preserver screening. Source explicitly ties the question to a nonaffine gradient preserving convexity; dimension and one-dimensional degeneracies must be checked, no discovery claim.'),
('quadratic-stochastic','0902.4207v1','Ganikhodzhaev–Rozikov','Problem 2.','Find necessary and sufficient conditions on heredity coefficients P_ij,k for a quadratic stochastic operator to be transversal.','Park: source already gives the even-principal-minor condition in the Volterra subclass. Repeating it does not solve the general QSO question; no fresh full classification mechanism.')]
contexts=[];scout=['# Breadth with a sustained fullerene route\n\nFifteen distinct source-question families across spectral graph theory, algebraic geometry, operator theory, optimization, learning, ordered spaces, logic, semigroups, complex analysis, convex geometry and nonlinear dynamics. Fourteen are additional to the assigned fullerene lead, not extra claims about that lead. Primary bodies span 2009–2024; older attributions are not counted as independently read originals. All dispositions are bounded screens, not universal novelty clearance.\n']
for ident,id,authors,label,scope,status in specs:
 if ident=='fullerene':p=next((L/'frozen').glob('*-fullerenes.txt'))
 else:p=freeze(L/'primary'/(id+'.txt'))
 text=p.read_text();lines=text.splitlines();hits=[i for i,x in enumerate(lines) if label.lower() in x.lower()]
 # avoid title-only or references when a literal statement label occurs repeatedly
 selected=hits[:4];parts=[]
 for i in selected:
  page=text[:sum(len(x)+1 for x in lines[:i])].count('\f')+1
  parts.append(dict(line=i+1,pdf_page=page,context='\n'.join(lines[max(0,i-3):i+24])))
 contexts.append(dict(family=ident,source=id,url='https://arxiv.org/pdf/'+id,label=label,copy=str(p.relative_to(L)),sha256=sha(p),contexts=parts))
 scout.append(f'## {ident}: {authors}\n\nPrimary: https://arxiv.org/pdf/{id}, {label}. Frozen body: `{p.relative_to(L)}`.\n\n{scope}\n\n{status}\n')
scout.append('## Prior filters and ranking\n\nRank 1: fullerene crossing, full mathematical endpoint established; needs independent adversarial review and wider live novelty clearance. Rank 2: ordered-Banach Problem 2.5, source-specific cone construction route only, not a solution. No rank 3. Cached proof bodies were an early exclusion filter rather than a claim that unmatched topics are open. Full registry scans are unavailable: regular public repository pages establish current heads, while prohibited API/raw/codeload routes remain parked. Full source bodies, cached finite-Otto proof, campaign r285 handback and degree-weighted distinctions were read. Zeckendorf mixing, reserved Claude octahedron and parked recent targets were not taken over.\n')
(L/'SCOUTING.md').write_text('\n'.join(scout));(L/'primary-statements.json').write_text(json.dumps(contexts,indent=2))
graphs={x:json.loads((L/(x+'-edges.json')).read_text()) for x in ['G','H']}
rows=[]
for v in range(32):
 ns=[]
 for x in ['G','H']:ns.append(','.join(str(b if a==v else a) for a,b in graphs[x] if a==v or b==v))
 rows.append(f'| {v} | {ns[0]} | {ns[1]} |')
proof=r'''# A counterexample to Conjecture 3 (full mathematical endpoint)

Source: Bille–Buchstaber–Spodarev, *Some open mathematical problems on fullerenes*, arXiv:2410.19322v1, 25 October 2024, Definition 5 and Conjecture 3, PDF p13; degree convention and graph class, Section 2 pp2–3. The current arXiv record retrieved 30 October 2026 lists v1 only. Source PDF SHA256: 244ea62bb54ea6ac818a924f16c5729629dc0d36c6e756e57da110ef4105eb64.

The quantified claim is: for each alpha,beta in (0,1), and each pair of dual fullerenes of feasible original orders, equality of tr exp(alpha A+beta D) implies isomorphism (and conversely). It is not the weaker claim that equality as a function of both parameters implies isomorphism. We refute the printed pointwise claim.

## Explicit graphs

Let G,H be the simple undirected graphs on {0,...,31} specified by the following neighbor table. Adjacency is symmetric; each edge is included once in the JSON edge lists. These exact graphs, not a graph-generator enumeration claim, are the witness.

| Vertex | G neighbors | H neighbors |
| --- | --- | --- |
'''+ '\n'.join(rows)+r'''

Each has 32 vertices, 90 edges, 12 vertices of degree 5 and 20 of degree 6. `graph-certificates.json` supplies rotation systems and 60 triangular faces. Their dart-face permutation has only 3-cycles and Euler characteristic 32−90+60=2. Connected orientable cellular embeddings with Euler characteristic 2 are sphere embeddings. The independent checker verifies connectivity after deletion of every pair of vertices in both graphs and both dual graphs. The duals are simple 3-connected cubic planar graphs with 60 vertices and 32 faces: 12 pentagons and 20 hexagons. By Steinitz, each is the graph of a convex polytope of the source class. Thus G,H really are dual fullerenes of feasible order n=60; n is not their dual order 32. No IPR premise is present in Conjecture 3.

## Exact heat-trace bounds

For graph X put M_X(alpha,beta)=alpha A_X+beta D_X with D_X(v,v)=deg_X(v). Define f(beta)=tr exp(M_G(9/10,beta))−tr exp(M_H(9/10,beta)). All matrices at the two endpoints beta=1/50,9/10 have nonnegative entries and maximum row sum R=6(alpha+beta). For K=90 define

S_X=sum_{k=0}^90 tr(M_X^k)/k!,  E=32 * 3^ceil(R) * R^91/91!.

Entrywise positivity gives S_X <= tr exp(M_X) <= S_X+E. Indeed tr(M_X^k) <= 32 R^k by the induced infinity norm, and

sum_{k=91}^infinity R^k/k! <= (R^91/91!) exp(R) < (R^91/91!) 3^ceil(R),

since (91+j)!>=91!j! and exp(1)<3. Hence the exact rational interval for f is [S_G−S_H−E,S_G−S_H+E]. All arithmetic in these inequalities is rational. `exact-signs.json` stores the full rational endpoints; `independent_check.py` reproduces them using standard-library integers/Fraction and sparse matrix multiplication, without NumPy or NetworkX.

At beta=1/50 the integer matrix is 45A+D divided by 50; at beta=9/10 it is 9A+9D divided by 10. The independently checked exact rational comparisons are

1/1000 < f(1/50) < 1/500,

−2 < f(9/10) < −1.

The decimal indications 0.00151005689 and −1.66314024 are dispensable: the inequalities above follow by integer cross multiplication of the stored rational endpoints. No float sign or numerical near-equality is used in the proof.

## Nonisomorphism and an interior zero

For B_G=45A_G+D_G, B_H=45A_H+D_H, exact integer multiplication gives

tr(B_G^6)=540051518791920,

tr(B_H^6)=540051567999420.

An isomorphism simultaneously conjugates A and D by a permutation matrix and preserves every pencil moment. These distinct integers prove G and H are nonisomorphic, independently of a graph-isomorphism algorithm.

The matrix exponential is analytic in its entries, so f is continuous on [1/50,9/10]. Its rigorously opposite endpoint signs imply an interior beta_* in (1/50,9/10) with f(beta_*)=0. Thus alpha=9/10 and beta_* both lie strictly in (0,1), and two nonisomorphic source-class dual fullerenes have equal character at that same pair. This refutes the complete universal Conjecture 3. Existence of beta_* is exact; a closed form or floating approximation is unnecessary.

## Scope, alternative mechanism and novelty limits

This is a full mathematical refutation of the printed source endpoint. It is not a refutation of injectivity at the singled-out default (1/2,1/4), nor of entire-function injectivity, nor a proof of a degree-weighted isospectral pair. No universal lemma remains missing for the pointwise refutation. Classical continuity, matrix-norm tail bounds, surface classification and Steinitz are routine supporting bridges, not separate discoveries.

A deterministic-seed walk through 600 WL-distinguished C60 dual candidates sustained the alternative pencil route. Exact moments k=1..8 for A+tD, t=0,1,2 left three candidate pairs; exact moments 9 or 10 at t=0 rejected all three. Those are finite exclusions, not an impossibility theorem. No switching theorem was imported without hypotheses; the successful witness is certified directly in the source class.

The 2019 Bille–Buchstaber–Spodarev paper, arXiv:1910.00846v1 Section 3 pp8–9, gives a C44 adjacency-cospectral pair and Conjecture 1 about adjacency spectra. Its fragment flip is explicitly not generally spectrum preserving. Neither that construction nor adjacency cospectrality alone settles a nonconstant degree-weighted pencil. This C60 witness is not adjacency cospectral and uses an interior parameter crossing instead. The 2024 source itself cites the 2019 paper and nevertheless poses Conjecture 3.

Bounded prior work: r285 source and parent handback read, semantic cache filter applied, current author arXiv listings and source record retrieved, current regular GitHub registry heads recorded. No matching fullerene proof body was found in the inspected cached Problems corpus. That does not clear all current registry files, all citations, or the full specialist literature. No worldwide novelty or campaign acceptance is asserted. Root must commission independent adversarial source/prior review and decide eligibility. No Lean or manuscript was written.
'''
(L/'PROOF.md').write_text(proof)
(L/'discovery.md').write_text('# Full-scope mathematical counterexample, unaccepted\n\nSee PROOF.md for explicit C60 dual graphs and the exact interior crossing at alpha=9/10, beta in (1/50,9/10). Finite graph-class and rational-sign obligations have complete certificates and a second implementation. Nonisomorphism follows from unequal sixth weighted moments. The claimed endpoint is the literal pointwise Conjecture 3, not the default parameter pair or entire-function injectivity.\n\nThe full mathematical proof is present. Independent adversarial review, broader current prior-art clearance and any subsequent formal endpoint remain root obligations. Discovery credit here: 0; counts remain 9 additional / 39 total / next 40.\n')
(L/'SUMMARY.md').write_text('# Research handback\n\nFull mathematical refutation of Bille–Buchstaber–Spodarev Conjecture 3 obtained. Two explicit nonisomorphic 32-vertex triangulations dual to C60 fullerenes have equal character at alpha=9/10 and some beta strictly between 1/50 and 9/10. Exact rational Taylor bounds certify the sign change; a standard-library checker independently verifies both signs and all graph-class certificates. See PROOF.md, G-edges.json, H-edges.json, graph-certificates.json and exact-signs.json.\n\nPencil mechanism sustained on 600 candidates: three low-moment survivors all rejected by exact higher moments. Breadth: 15 distinct primary source-question families, 2009–2024, with exact cached finite-Otto proof duplicate excluded. Rank 1: fullerene proof; rank 2 provisional: ordered-Banach net/supremum question.\n\nNovelty remains bounded and unapproved. Current public registry heads were retrieved, but full current proof-body coverage and independent adversarial review remain necessary. No Lean/manuscript/shared/git/public/MathDB/count edits. Root alone accepts; credit 0 here.\n')
(L/'progress.md').write_text('# Progress and remaining work\n\nCompleted: rules/context snapshots; primary literal scope; frozen references; 2019 body and source-successor screen; cached semantic/proof endpoint screening; two sustained mechanisms; exact graph and sign certificates; independent stdlib reproduction; fifteen-family breadth.\n\nChronology: 2019 source gives adjacency spectral questions; 2024-10-25 v1 poses the pointwise heat-trace conjecture; 2026-10-30 this lane constructs and certifies a crossing. Regular GitHub pages give trureturing head 42292d94c64d845dcba519c3bc33b1d9800881fc and openai/math head 4eaee87548250b2682affda7d05d947c05554bae. Full current trees were not downloaded: prohibited routes were not retried.\n\nRemaining: root independent adversarial source/math/prior review and eligibility decision. No unsolved universal mathematical bridge remains in the pointwise counterexample. No claim about (1/2,1/4). No formal certificate or paper requested or produced. Administrative counters are snapshots only.\n\nFailures preserved: direct fullgen.c path 404, successful archive discovery via official index, unavailable gcc prevented compilation; finite pencil collisions rejected, not hidden. A broad navigation scan completed in 117s under the unchanged guard; targeted immutable references replaced further historical recursion. No denied route, browser bypass or cap increase used.\n')
with (L/'failures.jsonl').open('a') as f:
 f.write(json.dumps(dict(action='compile fullgen',error="FileNotFoundError: gcc absent; no cc/clang available",preserved_in='prepare.py initial execution',disposition='use directly certified graph construction'))+'\n')
provenance=dict(date=datetime.datetime.now(datetime.timezone.utc).isoformat(),lane=str(L),guard=str(L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),limits=dict(AS_MiB=512,group_RSS_MiB=512,CPU_seconds=210,wall_seconds=230),env=dict(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1'),status='full mathematical refutation; acceptance and novelty not cleared',credit=0,counts_snapshot=dict(additional=9,total=39,next=40),bindings='bindings.jsonl',source_statement_bindings='primary-statements.json',freeze='freeze.json',current_registry_heads=dict(trureturing='42292d94c64d845dcba519c3bc33b1d9800881fc',openai_math='4eaee87548250b2682affda7d05d947c05554bae'),access_limits='Regular public pages and lawful arXiv/ANU HTTP only; no API/raw/codeload/diff/patch/ScienceDirect/Google challenge retries; current head is not complete current proof clearance',independent_check='independent_check.py',external_mutations=False)
(L/'provenance.json').write_text(json.dumps(provenance,indent=2))
print('REPORTS WRITTEN',len(specs),'families;',len(cache),'broad cached problem hits')
print('Cache hits:',[Path(x['original']).name for x in cache])
