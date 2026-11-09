from pathlib import Path
import json,hashlib,datetime,re
w=Path(__file__).parent
notes={
327695:'Asymptotic quantifier k→∞ and uniform little-o are essential; small chromatic endpoint examples are irrelevant. Need uniform long-cycle bound approaching extremal order, not a fixed proportion.',
327714:'Reduction index depends on actual singularity-resolution construction. No bound proved; need primary definition and uniform stabilization lemma, not termination for one polynomial.',
327738:'Universal vertex-transitive chromatic bound. No certificate found; clique blowups/cycles only recover standard test families. Requires new bound or explicit transitive finite violation.',
327739:'Strong coloring quantifies over every equal-block partition, with padding conventions to restore from primary. Testing ordinary colorings cannot refute this. Parked before primary investment.',
327765:'Definition of dependent rigidity and ambient dimension m requires primary restoration. No generic-framework/MLT equivalence established; cannot replace genericity with one sample.',
327769:'Uniform graph-class separator-to-expansion theorem; bounded-degree case explicitly insufficient. No full-scope proof; later polynomial-expansion literature not cleared.',
327818:'Read actual Graver definition, fiber setup, Theorem4 proof route and Conjecture3. Exact box-intermediate edge test derived; 623 bounded fibers checked with no counterexample. Conformal shortest paths alone do not supply degree-many edge-disjoint paths across arbitrary cuts. Next lemma: transport all neighbors of a minimal cross-cut pair to distinct cut edges without violating nonnegativity. Unproved.',
327822:'Compound claim about four inequivalent power indices and concentration constants. No single index definition restored, no uniform bound. A k-voter numerical example would not establish stated generality.',
327841:'Read collapse-free definition, Lemmas3.3/3.4/4.1, basis construction and 5.1–5.4 proofs. Independent-set→basis injection fails as a shortcut: domination annihilates a whole nonzero-parameter connected block even when only a different vertex of that block is chosen. Need a cardinality-preserving replacement for lost independent sets, uniformly on bipartite diagrams. No such injection proved.',
327876:'Categorical/Hodge determination assertion lacks a tractable finite semantic bridge. No proof and no claimed formulation beyond literal record.',
327884:'Circuit steps must be maximal and feasible; a non-Hirsch combinatorial diameter does not imply circuit violation. No explicit circuit certificate or general bound obtained.',
327918:'Literal itself says authors prove full symmetry. Exclude known-in-source; no claim of fresh resolution from open tag.',
327965:'Piecewise divisibility cases overlap at multiples20; cannot count wording repair or small-cycle exceptions. No general distinguishing extension mechanism proved.',
327967:'Full Euclidean isometry action and every precoloring matter. Finite dihedral witness gives only a lower bound; no seven-blank extension proof.',
327972:'Planar edge Roman domination bound requires all planar graphs. No exact planar witness/certificate; matching or vertex domination replacement is not an equality of invariants.',
327973:'All girth parameters k and all planar graphs; forests do not refute tending coefficient. Need uniform discharging or exact planar witness. None proved.',
328018:'Requires lowest Neumann spectral branch on every sector angle and unique nondegenerate critical point. Neither finite discretization nor numerical critical point proves full assertion.',
328029:'Two fixed knot types but mosaic equivalence needs Reidemeister/topological semantics and exhaustive lower obstruction. No new proof; later source cache exists historically but not reread here.',
328045:'Uniform zero forcing process and girth. No new full-scope lower bound; finite seed sweeps would not prove it. Later-literature scope not cleared.',
328046:'Specialization of328045; even a proof cannot earn a separate family credit. No proof attempted beyond literal mechanism assessment.',
328048:'Record omits precise specified induced-cycle type; cubic-graph NP-hardness needs source reduction and complexity semantics. Not a literal well-specified Lean target yet.',
328054:'Literal states source corollary solves it. Exclude known-in-source; parser open status has no mathematical force.',
328077:'Literal explicitly records classical proved Tait conjecture. Exclude known; formalization would not be a new result.',
328167:'Literal expressly says precise formulation remains to be established. No exact quantifiers/technical conditions to prove; cannot invent narrower conjecture.',
328185:'Surface, genericity and stress-matrix construction require primary restoration. Removing PSD not justified by rank alone without full rigidity argument. No result.',
328198:'Recursive group W_n not defined in record; count2^n and n=4 commentary have indexing tension. Do not count index repair; need actual group/central character definition.',
328212:'BEL gadget exact color-extension definition absent; no uniform gadget construction. Special cycles/3-connected cases already known according to literal.',
328213:'Uniform Ramsey-minimal construction needed for every connected H, preserving δ(n−1). No construction; standard clique instances uncredited.',
328259:'Gap-vector definition required, especially no-positive-component cases. No generic interpolation or exact Gram-rank argument; endpoint low-degree issue alone ineligible.',
328283:'Manifold contractibility/action hypotheses and L2 homology must remain literal. No full vanishing theorem. Dropping contractibility to get sphere counterexamples is a wording correction, not valid research.',
328299:'Technical conditions explicitly unspecified. No exact universal AMP-UD endpoint available; cannot promote empirical recovery to MMSE theorem.',
328365:'Planarity, triangle distance and exclusion of5-cycles all essential. Steinberg counterexamples do not automatically satisfy this stronger triangle condition. No exact graph witness.',
328367:'Full ordinary finite refutation and Lean endpoint completed. EXCLUDE_ROUTINE_COROLLARY: same authors2009Theorem4 and its shadow-guard proof supply upper bound immediately. Zero accepted credit despite correctness.',
328376:'Degree0 discrepancy is only endpoint correction. Full nodal-domain maximization for arbitrary degree not established; no topological bound certificate.',
328389:'Full ordinary Gram/spectral optimizer argument in PROJECTIVE-328389.md. Key scalar minimization found explicitly in Aliyev2024 primary proof; strong routine-corollary objection. No Lean endpoint; zero credit.',
328415:'Read GDN definition and section4 actual proof bodies. Lemma4.3 plus Proposition4.4 force MIP3=3; Corollary4.5 gives CE3=2, contradicting strict Conjecture4.1 in dimension3. This is a same-source parameter/strict-endpoint inconsistency, excluded by policy, not a new significant refutation. Generic derivative heuristic only gives non-strict bound; no larger-dimension full result.',
328458:'Exact minimax component size for sufficiently large n at fixed epsilon. Rounding/nonintegral bias is ineligible wording issue. No full game strategy or counterstrategy found.',
328474:'Uniform generator AND relation degrees for every factor count, further arbitrary polarizedGIT varieties. No bounded presentation theorem; special Veronese evidence insufficient.',
328494:'minnonmer/potprec definitions absent and complexity conjunction global. No double-exponential algorithm or separation; finite function values insufficient.',
328505:'Uniform critical-graph edge recurrence across all admissible orders. Known lower-edge bounds alone do not identify both minima for all residues. No new construction or exact counterexample.'}
primary={327818,327841,328367,328389,328415}
res={}
for x in json.loads((w/'extracted.json').read_text()):
 r=x['record'];i=r['mathdb_id'];res[str(i)]={'mathdb_id':i,'title':r['title'],'literal_statement':r['statement'],'canonical_url':r['canonical_url'],'source_url':r['source_url'],'normalized_record_file':x['file'],'line_1based':x['line'],'line_sha256':x['line_sha256'],'statement_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'depth':{'literal_review':True,'primary_definitions_theorem_proof_bodies':i in primary,'diagnostic':i in {327818,327841,328367,328389,328415},'rigorous_full_ordinary_proof':i in {328367,328389},'full_Lean_endpoint':i==328367},'disposition':('EXCLUDE_ROUTINE_COROLLARY' if i in {328367,328389} else 'EXCLUDE_KNOWN_IN_LITERAL_SOURCE' if i in {327918,328054,328077} else 'EXCLUDE_ENDPOINT_PARAMETER_CORRECTION' if i==328415 else 'PARKED_NO_FULL_RESULT'),'assessment':notes[i],'accepted_credit':0,'novelty_cleared':False,'significance_pass':False if i in {328367,328389,328415,327918,328054,328077} else None}
res['328367'].update(endpoint='Eternal.exact_source_refuted',packet='eternal-328367-zero-credit.zip',replay='fresh-extraction/lean.log',axioms=['propext','Classical.choice','Quot.sound'],semantic_limit='Closed-family safety-game semantics; forward infinite-play bridge proved in Lean. Converse to a separate history-dependent strategy datatype explained mathematically, not a separately formalized equivalence theorem. Excluded candidate only.')
res['328389']['proof']='PROJECTIVE-328389.md'
(w/'results.json').write_text(json.dumps(res,indent=2))
receipts=[]
for p in sorted((w/'sources').iterdir()):
 if p.is_file():receipts.append({'file':str(p.relative_to(w)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size,'mtime_utc':datetime.datetime.fromtimestamp(p.stat().st_mtime,datetime.timezone.utc).isoformat(),'timestamp_limit':'filesystem receipt time, not asserted server publication timestamp'})
(w/'source-hashes.json').write_text(json.dumps(receipts,indent=2))
