from pathlib import Path
import json,hashlib,shutil,zipfile
p=Path(__file__).parent
notes={
324848:'Literal omits minimum-degree-two restriction encoded in gamma_sd(2,2,n), and equality for every n ignores divisibility/rounding. Edgeless-graph or n not divisible by five objections would be wording fixes; no credit. Genuine simultaneous domination upper bound needs a uniform paired-graph structural argument.',
324860:'General nef effectiveness on surfaces over algebraic finite fields: numerical triviality/torsion special cases do not handle nef square-zero nontrivial classes. No source-body or constructive full-scope route developed.',
324870:'Sarwate distance bound requires arbitrary primitive exponents for every even extension degree; Walsh moment bounds alone give weaker square-root bounds. No full-scope mechanism; small codes are instances.',
324969:'Random Turan identity at threshold requires stability and exact random extremal structure, not just expected clique counts. No tractable complete route or source-body clearance.',
324973:'Derived-invariance of all canonical cohomology support components AND dimensions. Known low-i clauses are in record already. No full derived-category infrastructure or route.',
325026:'Record reference labels refuted but quoted vanishing-sum example is not itself a Hadamard-matrix counterexample. Do not conflate auxiliary conjecture with literal defect bound. Primary-body gap; parked.',
325039:'Uniform bound for all numbers of transitive colors: two-color transitivity is known. A reachability result for arbitrary colored tournaments could subsume it, but full contemporary primary theorem not checked; no novelty claim.',
325041:'Requires almost-every-moduli attainment, not a finite collection of short geodesics on a sample surface. Source definition of K and measure body missing; parked.',
325042:'Sublinear-hop asymptotic DoF claim: neither fixed-hop instances nor a linear-hop construction resolves it. Channel model and operational coding proof absent; parked.',
325168:'Recursive extremal construction yields lower bound, not global induced-density upper bound. Optimizing scalar alpha is helper only. General k needs symmetrization or global certificate; parked.',
325209:'Congestion exactly two and every proper minor-closed family; generic constant congestion rounding does not suffice. No bounded certificate/full rounding proof route.',
325241:'Full packing/MFMC equivalence for arbitrary squarefree ideals is major open structural problem. Bipartite/graph ideals are known instances; no full route.',
325293:'Selected for exact spectral analysis, then excluded by public primary proof: Hu-Qi-Shao, Cored hypergraphs, Propositions 3.5,4.1,4.2. Odd loose paths of length >=3 have lambda=2=max degree and are not hyperstars. Proof body read; 2013 published companion predates investigation.',
325365:'Only a particular complete intersection X is intended; literal summary omits ambient weights/equations. General Cox quotient may fail but would not settle intended X. Primary body gap; parked.',
325386:'Basis independence for all n needs faithful representation/normal forms. Bell times Catalan dimension is target, not an allowable assumption. No complete route.',
325415:'Normalized statement is visibly corrupted (missing defining polynomial and index definition). Must reconstruct primary number-field hypotheses before Newton-polygon computations. No credit from corrected wording.',
325420:'NP-completeness for k=3 needs uniform reduction with variable number of trees. Fixed-parameter algorithms cannot settle; no full reduction route.',
325435:'Unrestricted-length partition maximum: fixed-length counterexample does not imply total-size violation after summing lengths. Canonical injection/compression for all lengths remains missing. Primary Borg body read for family; not claimed solved.',
325436:'Selected partition family excluded from new discovery: published counterexamples include P_8,3 four-family versus three-star; Person-Schweser 2610.01747v1 gives general scales and explicit P_31,8 family 620>618. Exact common-parts rather than same-coordinate relation checked.',
325437:'Unrestricted multiplicity t-intersection does not follow/refute from fixed-length comparison. Primary Borg conjecture 2.1 read; source proof only gives implication from fixed-length theorem, not converse. No all-length counterexample/injection survives.',
325438:'Selected partition family excluded: Person-Schweser 2610.01747v1 Theorems 1.2,5.2 refute general fixed-length conjecture by a first complete-intersection pattern; construction and exact counting Lemma 5.1 read. Prior 2016 exceptions also matter.',
325439:'Proper t-intersection counts distinct parts, whereas source 325437 counts multiplicity. Fixed-length counterexample does not automatically defeat all-length distinct-part maximum; no global proof developed.',
325453:'Full fractional matching/space-barrier threshold across all k,d. Partial ranges are in literal record. Requires general extremal theorem, not finite hypergraph checking.',
325502:'Visibility realizability depends on full geometric blocker conventions. Edge bound conjecture would imply target but is not proved. k=0/domain counterexamples would not earn credit; no representation route.',
325519:'Selected surviving exact refutation. B={2,3,5,7}; Omega2(B union {0}) has 118 values, while positive A={1,2,4,8,16} has at most115, hence r5<=115. Full kernel endpoint and genuine finite-checker soundness build. Candidate pending independent novelty/significance/fidelity review and paper; journal body inaccessible403.',
325576:'Clique condition relates chi>=Delta and high-degree induced graph. Critical-graph machinery needed; small Delta instances are already known. No uniform construction or proof.',
325577:'Entropy on Mandelbrot wakes requires primary definitions and entire interval control. Numerical Hubbard-tree samples cannot prove maximization. No full route.',
325580:'Non-nilpotent subsets of every simple-group conjugacy class: small simple groups sharp cases already in source. Classification/commuting graph bound needed; no full route.',
325625:'Contactomorphism and virtual Legendrian destabilizations require a full uniqueness theorem; no useful small certificate. Current related theorem body unreviewed, so neither novelty nor current openness asserted.',
325638:'O(n) priority-queue queries requires precise algorithm/query model; a generic planar max-flow time bound does not settle query count. Source implementation body absent.',
325651:'Literal corrupted and cutoff/covariance hypotheses underspecified. Gaussian shifts/covariance perturbations would target wording unless compared to primary regularity class. No analytic maximum-limit proof route.',
325698:'Classification of all hyperbolic doubly primitive knots in nonprime manifolds; constructing another parametrized instance does not settle classification. Primary construction/surgery definitions gap.',
325703:'Zero-sum sets allow zero subset sums; sign reversal from minimum-subset-sum problems loses ties. All-zero multiset is not a set, and tie loopholes would not earn credit. Need substantial set-level extremal route and primary assumptions; none developed.',
325729:'Sufficiently large ell precludes finite-small-ell refutations. Need an unbounded family beating M(q,q), controlling all U2 minors. Rank-three truncation/linear-space construction route lacks verified contraction bounds; parked.',
325733:'Uniform cubic bridgeless graph lower bound m3>=4/5 needed; Petersen establishes opposite inequality only. Searching finite graphs or verifying Petersen not a new solution.',
325742:'Requires constant additive slack for every oddness-two snark. Finite examples do not refute any unspecified constant; need unbounded excess family and minimum-cover proof. No complete route.',
325831:'Empirical exponential fit plus dispersive shock timing lacks exact analytic quantifiers in corpus. Scaling/soliton exceptions risk domain fixes; primary hypotheses needed; parked.',
325867:'Historical reference says solved while status field says open; monochromatic-cycle degeneracy convention also missing. No novelty from stale status; needs contemporary public-counterexample body screen before any investment.',
325889:'Historical references say solved while status open; uniform algorithm above threshold cannot be replaced by decidability for fixed n. No full algorithm route/current body review.',
325900:'Tightness iff unit ball non-parallelogram needs norm-dependent geometric construction for arbitrary norm. Three-terminal experiments not sufficient. Primary bead definition and rounding/tie convention missing.'}
rows=json.loads((p/'literal-records.json').read_text());old=json.loads((p/'old-note-filtered.json').read_text());results={}
for x in rows:
 r=x['record'];i=r['mathdb_id'];selected=i in [325293,325436,325438,325519]
 results[str(i)]={'mathdb_id':i,'title':r['title'],'literal_statement':r['statement'],'corpus':{k:x[k] for k in ['chunk','line','sha256']},'source_url':r['source_url'],'literal_read':True,'primary_body_read':i in [325293,325435,325436,325437,325438,325439,325519],'related_proof_body_read':i in [325293,325436,325438,325519],'depth':'full_literal_Lean_refutation_candidate' if i==325519 else ('primary_related_proof_screen' if selected else ('primary_statement_screen' if i in range(325435,325440) else 'literal_technical_screen')),'disposition':notes[i],'accepted':False,'discovery_credit':0,'old_note_hits':[dict(file=y['file'],line=y['line']) for y in old if y['id']==i],'historical_limits':'Bounded prior-note navigation found inventory/routing entries, not target-specific clearance. Stale reviewed flags ignored; absence not novelty.'}
(p/'results.json').write_text(json.dumps(results,indent=2,ensure_ascii=False))
formal=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal')
shutil.copyfile(formal/'lake-manifest.json',p/'lean/lake-manifest.json');shutil.copyfile(formal/'lean-toolchain',p/'lean/lean-toolchain')
# Bind exact read-only cache paths without dependence on another candidate lane.
paths=sorted(str(x.resolve()) for x in (formal/'.lake/packages').glob('*/.lake/build/lib/lean'))
(p/'lean/leanpath.txt').write_text(':'.join(paths))
(p/'lean/run.sh').write_text('''#!/bin/bash
set -eu
cd "$(dirname "$0")"
export LEAN_PATH=.:$(cat leanpath.txt)
exec /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean -DwarningAsError=true -j2 "$@"
''')
