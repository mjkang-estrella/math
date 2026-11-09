import json,pathlib,hashlib,datetime,re
D=pathlib.Path(__file__).resolve().parents[1]; E=json.loads((D/'extracted.json').read_text())
notes={
364153:'Folded-form polynomial and arbitrary-word lower bound require primary definitions; no assertion that optimizing the displayed polynomial settles global minimality.',
364166:'AGI and determined by are not formal predicates in the cached statement. A counterexample to an invented function-class formulation would not qualify.',
364203:'Innermost and inner polynomials depend on the source construction and its Jacobian hypotheses. No arbitrary-polynomial surrogate attempted.',
364205:'Full literal signed-cube refutation candidate: 34-point maximal rigid diameter-5 subset of Q_8. Ordinary proof and full Lean endpoint retained for independent review, zero credit.',
364331:'Sufficient positivity and r-spin stabilizer require source quantifiers. No feasible full mapping-class-group Lean bridge selected.',
364363:'Inverse-limit transition maps and Lambda action must be recovered before rank testing. No finite-level rank diagnostic claimed as a refutation.',
364398:'Cached literal itself says the source refutes the conjecture; primary proof not read here. Resolution lead only, no discovery investment.',
364417:'Missing colour-degree notation and possible k-range require source recovery. Large k violating vertex capacity would be a scope correction, not a new solution.',
364441:'Genus-equals-ribbon special cases are acknowledged in the literal. No new connected-sum mechanism established.',
364442:'Alternating non-ribbon hypotheses prevent borrowing arbitrary ribbon connected-sum examples. No source-level counterexample selected.',
364460:'Equivalent Borodin-Kostochka reformulation; no new nine-chromatic construction or proof mechanism survives literal screen.',
364479:'Graph H_{m,m} and signal metric require source definitions. A radius proof could be feasible, but no full literal graph construction recovered this pass.',
364507:'Flow exponential singularity is an infinite-dimensional analytic endpoint. Periodic-orbit heuristics do not cover arbitrary nontrivial flows.',
364518:'Literal explicitly says the procedure is imprecise. No theorem about a substitute cut-and-project procedure would settle it.',
364574:'Primary body downloaded with shared chordal source, but relevant definitions and conjecture proof context not read. No primary review claimed.',
364575:'Same downloaded body remains unread for this claim; literal even contains n/k variable ambiguity. No formula typo used as discovery.',
364576:'Same downloaded body remains unread for this claim. Full directed-distance and admissible parameter semantics still needed.',
364596:'Exact published registry theorem result states all four greatest-index clauses. Definitions and complete 11,858-byte proof body plus imported Pell definitions inspected. Treat as existing public resolution, not a new candidate; no local upstream rebuild claimed.',
364630:'Stable-case proof noted in literal does not imply general SSOT energy formula. No finite statistic reconstruction or all-rank Lean route selected.',
364696:'O(n log n) does not imply O(n); hereditary smallness needs literal enumeration convention before trace-family construction.',
364717:'The displayed definition is suspicious for (n,m)-complete coloured mixed graphs. No counterexample to the paraphrased bounded-walk definition would qualify; primary definitions unread.',
364740:'Source hypotheses and limiting spectrum are explicitly unspecified in literal. No generic sub-Riemannian replacement statement attempted.',
364746:'Literal supplies an explicit routine bridge m/3 and m<=5n/2. Body not read: reported-resolution lead, not an independently verified source theorem.',
364747:'Strong connectivity alone does not convert m/3 into 2n/3 at maximum degree five. Source proof and sharper structure remain unread.',
364801:'Backbone colouring constraints and spanning-tree convention need recovery before finite SAT/search certificates. No small graph counterexample asserted.',
364803:'Spectrality requires actual selector and Reeb dynamics definitions. No finite or scalar surrogate selected.',
364811:'Literal explicitly credits Fei with a counterexample. Counterexample proof body unread; reported prior-resolution lead only.',
364814:'NP-hardness needs a precise input model and EMST tie conventions. No reduction or assumption P!=NP used as proof.',
364857:'Source singular vector and universal module relations must be recovered. No dimension computation identifies full maximal submodule.',
364916:'Literal says the paper confirms the conjecture. Actual theorem/proof body unread: existing-resolution lead, not a new result.',
364931:'References in raw record report Rowlinson resolution while statement text is equivocal. No prior-body clearance or rediscovery investment.',
364937:'Root-of-unity imbalance and asymptotic constant uniformity require exact m,n scope. The m=1 endpoint is not a qualifying domain correction.',
364941:'Sphere geodesic angle versus projective acute angle is material. Antipodal measure refutes the paraphrase but not the source projective problem; no correction counted.',
364998:'Full-star threshold needs source t,k range; small endpoint anomalies would not justify a discovery. No all-parameter extremal-family proof found.',
365046:'Source already proves k>=6; a parameter-instance proof receives no credit. Cases k=4,5 remain untouched.',
365074:'Positive p includes degenerate endpoints in paraphrase; no endpoint correction counted. Source title alone cannot identify which four different conjectures are disproved.',
365079:'Surplus over the random-cut baseline and multiedge semantics need primary definitions; induced subgraph versus whole hypergraph scaling not replaced by a finite diagnostic.',
365126:'Source title suggests a non-Markovianity refutation, while literal reports no status. Actual proof body unread; do not rediscover from title.',
365143:'Primary Conjecture 5.1, Theorem 1.5 and proof read. Odd-set-cover reduction loses floor(k/2); no removal of that loss proved. 16,153 finite random spectral diagnostics produced no certified positive excess. Park full claim, not a known/routine exclusion.',
365145:'Inherited r130 original-00-discovery.md explicitly reports Z-curve questions screened but not promoted. Retain historical screen and do not repeat investment. No inherited complete proof or mathematical exclusion inferred.'}
results={}
for k,e in E.items():
 i=int(k);r={**e,'inherited_matches':[],'new_review_depth':{'literal_statement_read':True,'primary_definitions_read':False,'primary_theorem_or_proof_body_read':False},'outcome':'PARK_LITERAL_ONLY_NO_ENDPOINT','reason':notes[i],'remaining_lemmas_or_gates':'Recover exact primary definitions and scope; establish a substantive full-scope mechanism and bounded prior-art status before Lean investment.','accepted_credit':0,'source_receipts':[]}
 if i==365145:r['inherited_matches']=[{'path':str((D.parent.parent/'lanes/sol-fresh-source-discovery-r130/sources/original-00-discovery.md').resolve()),'line':24,'depth':'Inherited report of screening, not a primary proof review'}];r['outcome']='RETAIN_INHERITED_SCREEN_NO_REPEAT'
 if i in [364398,364746,364811,364916,364931,365126]:r['outcome']='PARK_REPORTED_PRIOR_RESOLUTION_BODY_UNREAD'
 if i in [364574,364575,364576]:r['new_review_depth']['primary_body_downloaded_unread']=True;r['source_receipts']=['sources/chordal.receipt.json']
 if i in [364205,364596,365143]:
  name={364205:'rigid',364596:'pell',365143:'laplacian'}[i];r['new_review_depth'].update(primary_definitions_read=True,primary_theorem_or_proof_body_read=True);r['source_receipts']=[f'sources/{name}.receipt.json',f'sources/{name}-current.receipt.json'];r['remaining_lemmas_or_gates']={364205:'No mathematical or Lean bridge remains in candidate. Independent statement-fidelity, significance, prior-art, paper and root acceptance reviews remain. No worldwide priority claim.',364596:'No new discovery route: exact registry theorem inspected. Registry proof not locally rebuilt or independently trusted as an acceptance certificate.',365143:'Sharpen odd-set-cover/Ky Fan decomposition to eliminate floor(k/2) for k<=n_nonisolated-2, or find an exact nonbipartite counterexample with a spectral certificate.'}[i]
  r['outcome']={364205:'FULL_LEAN_REFUTATION_CANDIDATE_PENDING_INDEPENDENT_REVIEW',364596:'EXCLUDE_EXISTING_PUBLIC_EXACT_REGISTRY_RESULT',365143:'PARK_PRIMARY_PROOF_ATTEMPT_HARD_GAP'}[i]
  if i==364205:r['source_receipts']+=['sources/rigid-v2.receipt.json','sources/rigid-new1.receipt.json','sources/rigid-new2.receipt.json'];r['new_review_depth']['prior_art_depth']='Current source v1/v2 definitions, Conjecture 1, Theorem 4 and Proposition 5 proofs; later primary theorem statements and selected proof bodies, not complete later-paper proof audit.';r['lean_endpoint']='MathDB364205.literal_source_refutation';r['packet']='364205-proof-source.zip'
  if i==364596:r['source_receipts']+=['sources/pell-registry.receipt.json','sources/pell-defs.receipt.json']
 results[k]=r
assert len(results)==40
(D/'results.json').write_text(json.dumps(results,indent=2,ensure_ascii=False)+'\n')
# Consolidate receipts, including byte-verified reused scope references.
r=json.loads((D/'registry-screen.json').read_text());p=D/'sources/omega-problems.body';o=json.loads(p.read_text());r.append({'path':str(p.resolve()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'tree':o['sha'],'truncated':o['truncated'],'entries':len(o['tree']),'path_hits':[h for h in o['tree'] if re.search('364205|364596|365143|rigid|PellPartial',h['path'],re.I)]})
(D/'registry-screen.json').write_text(json.dumps(r,indent=2)+'\n')
