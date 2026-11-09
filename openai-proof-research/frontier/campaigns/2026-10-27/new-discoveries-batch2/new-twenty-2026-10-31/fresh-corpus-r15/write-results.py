from pathlib import Path
import json,hashlib,datetime,re
w=Path(__file__).resolve().parent
reasons={
334582:'Density supremum and diophantine max-min are genuinely infinite. Zero in D only gives a wording/domain issue, excluded; no finite full-scope bridge established.',
334645:'Current primary abstract for 1611.06557 explicitly claims settlement; literal routing missed this. Known-result exclusion, not a fresh solution; proof body not audited here.',
334675:'Contains full Tuza-type packing/transversal problem for arbitrary 3-uniform hypergraphs; no eligible finite witness or complete proof obtained.',
334730:'Asymptotic equality with O(1) cannot be refuted by one small pebbling exception; needs unbounded-size lower/upper bounds. No such construction obtained.',
334784:'Degree assertion concerns every moment order after nonfilling begins; missing secant ideal/degree bridge prevents finite arithmetic certificates.',
334786:'General complete intersections with sufficiently large degrees and all hyperplanes; topology/geometric genericity is not a tractable finite witness here.',
334790:'Order-four hypercube classification and transversal counts require actual quasigroup semantics; group instances already in source are not new. No extremal violation obtained.',
334830:'Uniformity is existential in s and C, universal in mesh. One failing s or small matrix does not refute; no all-s obstruction obtained.',
334851:'Bounded remainder for arbitrary poset needs construction uniform in dimension; exact finite packing cases insufficient. Historical substring hits were hashes, not prior reviews.',
334858:'Metaplectic integral identity has representation-theoretic hypotheses and normalization; no source-faithful finite reduction or full proof obtained.',
334880:'Universality threshold is asymptotic for each bounded degree, not a finite graph enumeration. No new threshold mechanism obtained.',
334900:'Sustained legal-schedule search found no violation. Full even-case proof depends on parity-specific extreme-label uniqueness, which fails in odd case; no invariant controlling total inversions found.',
334911:'Universal chromatic-to-subdivision bound needs scalable chromatic obstruction or new proof. Small graph cases/endpoint issues do not resolve it.',
334924:'Intersection matroid cover inequality not tested via arbitrary complexes: exchange and full-cover bridges essential. No finite pair of genuine matroids violating the bound obtained.',
334944:'Literal record itself says source proves this. Held as known-result exclusion cue; no new-credit route and no primary proof-body audit here.',
334963:'Two circular orders must work simultaneously for every independent edge pair in a planar graph; no planarity-certified finite obstruction obtained.',
334975:'Three-node persistence needs filtered chain complexes and natural isomorphism, not equal Betti counts alone. No full persistent-module proof/refutation attempted.',
334986:'Canonical-word enumeration plus targeted quotient optimization found a barrier to alphabet-merging proof, not a counterexample to arbitrary binary-word extremality.',
335009:'Local automorphic transfer, positive type and nonzero trace require deep analytic representation bridges; no eligible short proof identified.',
335034:'Minimum ranges over all graphs at each order; dumbbell-like family must be defined and exhaustively compared. Numerical index comparisons would not alone prove a radical inequality; no witness found.',
335059:'Full majority three-coloring problem for every digraph; no substantive counterexample or full constructive argument found; loop/domain artifacts excluded.',
335070:'Nonnegative measures and support maximum are essential; signed-measure refutations are explicitly known and out of scope. No nonnegative counterexample obtained.',
335071:'Asymptotic implicit constants and source-specific equal separation preclude counting a finite small point anomaly. No full obstruction family obtained.',
335076:'Sufficiently large n excludes isolated small exceptions; color-critical Ramsey-extremal construction must beat an asymptotic Turan bound. No such family obtained.',
335136:'Sharp geometric volume comparison with injectivity-radius hypothesis; elementary degenerate-radius issues excluded. No valid metric construction obtained.',
335183:'High-probability order bound for fixed p; finite random instances do not resolve it. No new covering/encoding mechanism obtained.',
335184:'High-probability clique-cover chromatic index bound; needs joint edge cover by cluster graphs, not only clique cover counts. No proof obtained.',
335208:'Sampling stability requires uniform frame bounds in full spline space and actual index ordering; density-only or finite sample arithmetic insufficient.',
335209:'General generator scope is a potential transcription issue requiring source-specific hypotheses; an arbitrary degenerate generator would be a wording correction, excluded. No significant source-faithful resolution obtained.',
335224:'Literal text says C-matrix seed uniqueness is proved in source setting. Treat as known-result cue, not novelty. No source-body audit here.',
335230:'Complete real-valued Lean counterexample: K_2^(4), three colors, feasible maximum 5/3<2. Exact minimum predicate and numeric infimum universal statements refuted. Independent acceptance remains.',
335257:'Bounded-degree spanning-tree threshold is a known-literature-sensitive asymptotic question; no finite counterexample route. Full current theorem/source comparison not undertaken.',
335258:'Bounded-degree spanning graph threshold needs uniform asymptotics; trivial degree endpoints do not earn credit. No proof obtained.',
335259:'Local resilience quantification is stronger than containment. A scalar normalization correction is excluded; no sharp sparse resilience mechanism obtained.',
335303:'GLSM categories, discriminant components and spherical functors need geometric definitions/bridges; no tractable exact finite route identified.',
335364:'Two connected spanning edge factors with degree bound requires partition of all edges; two arbitrary trees or restricted graph instances insufficient. No full argument obtained.',
335369:'Snark cyclic connectivity is prior-construction sensitive. No genuine new snark construction/cyclic-cut and noncolorability certificate obtained; no claim of current openness.',
335392:'Original expansion/torsion definitions and conjecture passage read, but not all orbit proof bodies; no new attempt beyond source interpretation. 2026 group-theory partial-result search hit is not full-proof clearance.',
335442:'Definition of smallest exponent has boundary-constant subtleties; existing subfield example at equality is motivation, not fresh refutation. No new full-scope finite-field mechanism obtained.',
335497:'All integers through algebraic degree require actual likelihood critical-point counts for scaled Segre varieties; parameter examples already in source are excluded. No full construction obtained.'}
prov={int(r['id']):r for r in json.loads((w/'literal-provenance.json').read_text())}
rows=json.loads((w/'literal-records.json').read_text());out={}
for r in rows:
 i=r['mathdb_id'];depth='literal_record';body=[]
 if i==335230:depth='selected_full_proof_body';body=['arXiv1702.01442v1/v2 Section2 Equation1, Lemmas1-3 and Proposition1; Section3.3 Propositions4-6, Observations1-3, Lemmas5-7; author preprint Section3.3 definitions, Conjecture1 and divisible-case proof']
 if i==334900:depth='selected_full_proof_body';body=['1612.06816v1 Lemma12, Theorem13 and full internal Lemmas14-15; odd-case Conjecture26 passage; Klivans-Liscio2020 Section4 Conjecture4.2 passage (not whole successor proof audit)']
 if i in [334986,335392]:depth='primary_passage';body=['original definitions and conjecture passage; no full relevant theorem-proof audit claimed']
 if i==334645:depth='primary_abstract_search_passage';body=['current arXiv abstract claims settlement; full proof not read']
 out[str(i)]={'mathdb_id':i,'title':r['title'],'literal_statement':r['statement'],'canonical_url':r['canonical_url'],'source_url':r['source_url'],'provenance':prov[i],'review_depth':depth,'reviewed_source_scope':body,'disposition':'complete_lean_candidate_pending_independent_review' if i==335230 else 'no_completed_exact_solution','reason_and_remaining_obligations':reasons[i],'accepted_credit':0,'novelty_claim':False,'old_exclusions':'Historical exact-token reconciliation in historical-exact-hits.json; reservation alone is not historical/worldwide clearance.'}
(w/'results.json').write_text(json.dumps(out,indent=2,ensure_ascii=False))
# Preserve actual selected literal line bytes, not a reserialization.
raw=[]
for p in sorted(set(x['chunk'] for x in prov.values())):
 for n,line in enumerate(Path(p).read_bytes().splitlines(keepends=True),1):
  if any(x['chunk']==p and x['line_number']==n for x in prov.values()):raw.append(line)
(w/'literal-lines.jsonl').write_bytes(b''.join(raw))
files=['reservation.json','literal-lines.jsonl','literal-records.json','literal-provenance.json','results.json','PROOF.md','proof-packet.zip','diagnostics.py','diagnostics.cpp','quotient-search.py','fraction.log','chip.log','words.log','quotient-search.log']
manifest={f:hashlib.sha256((w/f).read_bytes()).hexdigest() for f in files};(w/'artifact-hashes.json').write_text(json.dumps(manifest,indent=2))
