import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent;B=L.parent
notes={
383839:'All components for fixed d,g,n require a uniform sharp deformation-theoretic lower bound. Expected-dimension estimates alone do not control obstructed components; no full-scope low-cost mechanism identified.',
383841:'The referent “these curves” is absent from the literal record. Recover source family and incidence hypotheses before testing interpolation; a selected easy family would not resolve scope.',
383855:'Requires genuinely interesting field classes and a uniform finiteness-transfer theorem, not a single algebraically closed field. No new class with a proved transfer mechanism identified.',
383857:'The meaning of u_k and the admissible fields must come from the primary definition. Computing one quadratic-form system would be a narrow instance, not the requested invariant theory.',
383870:'Maximum over non-Q-Gorenstein local rings of each fixed dimension needs an upper bound and sharp examples under exact F-singularity hypotheses. Toric examples alone cannot prove maximality.',
383871:'Primary definitions and existing calculations read. Miller–Swanson already treats generic rings of 2x2 minors via staircase monomials; the literal request includes other minors and both e_HK and s. No uniform new calculation for that full scope identified; no full-resolution exclusion claimed.',
383893:'A posterior concentration theorem requires topology, sampling, prior support and uniformity assumptions. Finite-model Laplace arguments would only give a restricted sufficient-condition instance; no new substantive general bridge identified.',
383905:'Requires an algorithm over arbitrary finitely generated fields, with representation and termination proofs. Enumerating Fourier–Mukai kernels only offers a semidecision route without the negative-termination bridge.',
383930:'Boundary perturbation must retain F-purity and make the canonical index prime to p for every strongly F-regular pair. D=0 does not settle the index condition; no proved uniform perturbation bridge established.',
383944:'Linear-algebra rank computation looks small, but source definitions must distinguish generic independent constraints from special correspondences and tensor-variety restrictions. Source unavailable; no claim that a generic matrix rank answers all scope.',
383963:'A moduli construction from differential/integral invariants needs specified objects and separation/equivalence properties. The literal text is a program, with no concrete full-scope low-cost construction identified.',
383965:'Requires a natural Lie-groupoid action and a relationship to quasi-invariants. A chosen tile action supplies only an example unless source scope is recovered; no uniform construction identified.',
383967:'Visual event surfaces require the source definition and allowed geometric inputs. Eliminating one chosen surface is a narrow calculation; no uniform effective-equations mechanism qualified.',
383969:'Silhouette reconstruction needs visibility, tangency and degeneracy hypotheses. Epipolar tangencies may suggest constraints but do not yet reconstruct the fundamental matrix for the source scope.',
383978:'Motivic Eilenberg–Moore construction requires convergence and base/coefficients hypotheses, not just a formal bar complex. No low-cost mechanism addressing those bridges identified.',
383979:'Motivic Serre sequence needs the precise fibration class, coefficients and convergence. Importing a topological sequence without these bridges would not answer the literal motivic question.',
383981:'“Above notions” is unresolved source context. No endpoint or quantifiers can be manufactured from the mirror; hold for definitions rather than declare a wording fix.',
383990:'Decompleted Tate spectrum needs a universal construction with the required compatibility properties; those are not in the record. No bounded full-scope construction identified.',
384010:'The untwisting R-module request and relative Gorenstein question for tmf maps are both retained. Familiar KU/KO examples are already in the statement and cannot resolve the requested extensions.',
384029:'Needs a complex cubic fourfold with the specified conjectural irrationality and rational reductions, including the meaning of most reductions. A single rational reduction does not meet the arithmetic scope.',
384032:'Maximum-dimensional families over the stated hypersurface parameter space need optimality as well as construction. Exhibiting a special unirational family supplies only a lower bound.',
384037:'Requires rational curves on A_g in characteristic p plus an obstruction to characteristic-zero lifting, with g and lift sense recovered from source. No qualified construction and nonlifting proof identified.',
384042:'“Those techniques” and degree threshold require primary context. A chosen differential form on one hypersurface would not establish improvement of the specified technique.',
384043:'Novel examples must be unirational and have nonzero differential forms; classical positive-characteristic examples may already answer weak literal readings. No new source-qualified example identified.',
384045:'Degeneration must respect the source flatness and singularity conditions and the second Brauer-class request. Nonflat examples or unrestricted singularities would only exploit missing wording.',
384052:'All Fano degree/dimension pairs over each F_p require a uniform construction and separable rational connectedness proof. Smoothness or a rational curve alone is insufficient.',
384053:'Supersingular K3 surfaces suggest a familiar witness, but source definitions of supersingular cohomology and simply connected must be checked before using it. No novelty or source-scope exclusion asserted without primary body.',
384061:'A smooth proper variety over Spec Z must have good reduction at every prime and irrational generic fibre. An irrational variety over Q with finitely many bad primes is insufficient; no global mechanism found.',
384089:'Both tropical Hilbert constructions and their comparison need precise tropical scheme definitions and functoriality. Point-set tropicalization alone cannot establish the requested comparison.',
384112:'Requires a genuinely new tropical ideal prime in the source naive sense. Classical realizable prime ideals could be known examples; no source-qualified new example found.',
384132:'Minimum toric ambient dimension for each marked tropical curve and universal faithful tropicalization require optimality and realization. A high-dimensional embedding alone misses the minimum question.',
384133:'A modular interpretation must identify represented objects and equivalences for both Dressian and Grassmannian. Their familiar valuated-matroid descriptions are leads, not a verified new resolution.',
384134:'Explicit tropical Hilbert examples and Hilbert–Chow map need the scheme structure, not classical Hilbert schemes or their supports alone. No bounded complete calculation qualified.',
384135:'Recovery of scheme properties must specify enriched tropicalization; ordinary support loses nilpotents. Such a support-level counterexample may only expose domain/wording loss, not resolve the intended program.',
384139:'Requires principal generalized parabolic Hitchin pairs, moduli and Hitchin maps for other complex algebraic groups. A definition alone or one group does not cover the full construction.',
384142:'High-rank Morse theory and degree-independence must avoid the character-variety route as expressly requested. Existing cohomology comparisons cannot be imported without a new geometric bridge.',
384148:'Full Fukaya category and comparison with DAHA representations require analytic foundations and categorical equivalence data. No tractable finite certificate identified.',
384151:'Explicit gauge groups and representations from elliptic fibrations require the precise geometric/physical dictionary. Standard Kodaira examples risk reproducing known outcomes; no qualified new construction identified.',
384163:'Fourth integral grading must work for general braids and match the matrix-factorization grading, requiring functorial/categorical compatibility. One computed braid is insufficient.',
384164:'A computational capability question from the geometric definition needs algorithm, effective input class, and verified output. A finite timing benchmark would not resolve that program.',
384167:'Parity conditions and preservation operations require the source HHH grading convention and quantified braid classes. One parity-preserving example would be a narrow known-risk instance.',
384168:'Every algebraic braid must satisfy parity and have a recursive HHH formula. Torus knots alone are insufficient; no source-qualified uniform mechanism identified.',
384169:'All positive products of nested full twists require parity and a recursive HHH formula. This resembles existing categorical recursion work; no primary proof/subsumption audit completed, so neither novelty nor full public resolution asserted.',
384171:'Recovering HHH from Milnor fibres requires a functor or invariant construction and comparison theorem for algebraic links. Matching a few Poincare polynomials would not suffice.',
384182:'Both general and every-smooth complex hypersurface unirationality questions demand new pairs relative to source baseline. Classical low-degree examples are not new outcomes; no new full-scope family found.',
384207:'For any rationally connected non-universally-CH0-trivial variety, construct a nonzero unramified cycle-module class. Abstract detection and explicit extraction are distinct; no effective general extraction bridge established.',
384211:'Sharp large alpha for K-unstable smooth Fanos needs the dimension range, stability definition, upper bound and examples. A selected Fano example cannot establish optimality.',
384215:'Second-volume gap across K-semistable Fanos and the quadric maximizer assertion require a uniform extremal theorem. Computing quadric volume only gives the candidate value, not the decisive upper bound.',
384216:'A volume upper bound for birationally superrigid Fanos needs dimension/singularity hypotheses and a uniform rigidity-to-volume bridge. No such new bridge identified.',
384223:'Hacking–Prokhorov v1 definitions, local smoothing formula, Prop3.2 proof and Thm4.1 Markov family read. They supply public deformation machinery, not a verified explicit global isotrivial family answering this request. Source Markov restrictions and explicitness threshold remain unverified; park rather than repackage a known smoothing.'}
rows=json.loads((L/'statements.json').read_text());assert set(notes)=={x['record']['mathdb_id'] for x in rows}
out=[]
for x in rows:
 r=x['record'];i=r['mathdb_id'];s=r['statement'];primary=i in (383871,384223)
 out.append(dict(mathdb_id=i,url=r['canonical_url'],statement=s,statement_sha256=hashlib.sha256(s.encode()).hexdigest(),exact_scope={'literal_quantifiers':s,'interpretation_limits':notes[i]},source_url=r['source_url'],source_name=r['source_name'],corpus_chunk=x['chunk'],disposition='PARK_SOURCE_QUALIFICATION' if i in (383841,383857,383944,383981,384042,384053,384135) else 'PARK_NO_QUALIFIED_FULL_SCOPE_MECHANISM',reason=notes[i],evidence_level='selected_primary_definitions_and_proof_sections' if primary else 'full_literal_statement_read',statement_review=True,primary_body_read=primary,complete_dependency_audit=False,live_registry_clearance='HOLD_NOT_OBTAINED',successor_dedup_status='bounded_public_overlap_read; not full-scope clearance' if primary else 'not cleared',accepted_credit=0))
(L/'dispositions.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
(L/'proposals.json').write_text(json.dumps({'proposals':[],'count':0,'reason':'No genuinely tractable source-qualified full-scope mechanism survived this screen.','credit':0,'registry_status':'HOLD'},indent=2)+'\n')
# Inspect bound historical administrative records only for assigned IDs; no recursive copies.
H=B/'root-mathdb-accepted-exclusions-r304';matches=[]
def walk(v,p):
 if isinstance(v,dict):
  if v.get('mathdb_id') in notes or any(i in notes for i in v.get('mathdb_ids',[]) if isinstance(i,int)):matches.append({'file':p,'entry':v})
  for w in v.values():walk(w,p)
 elif isinstance(v,list):
  for w in v:walk(w,p)
for n in ['accepted-exclusions.json','historical-dispositions.json']:walk(json.loads((H/n).read_text()),str(H/n))
(L/'historical-matches.json').write_text(json.dumps({'assigned_id_matches':matches,'limits':'Exact assigned-ID administrative search only; absence is not content or live-registry clearance.'},indent=2)+'\n')
refs=[]
for p in [B/'AGENTS.md',B.parents[3]/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:
 if p.is_file():
  b=p.read_bytes();refs.append(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b)))
(L/'administrative-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
(L/'provenance.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'freeze_order':['input-bindings.json: intake and actual originals, r304 history/exclusions, Cayley disposition, corpus manifest','corpus-bindings.json: all20 chunks verified before schema/record reading','exactset/disjoint check','assigned record schema then literal statements','retained primary PDF and URL/version/UTC/hash metadata before extraction'], 'primary_retention':[str(p.relative_to(L)) for p in (L/'primary').glob('*.meta.json')],'MathDB_requests':0,'live_registry_status':'HOLD; not obtained; no cached absence treated as clearance','counts':{'additional':9,'total':39,'next':40,'delta':0}},indent=2)+'\n')
print('built exact50; zero briefs; historical assigned-ID matches',len(matches))
