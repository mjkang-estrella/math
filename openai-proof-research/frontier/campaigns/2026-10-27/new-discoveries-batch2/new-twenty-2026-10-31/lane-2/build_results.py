import pathlib,json,hashlib,datetime,re
P=pathlib.Path('.')
old=pathlib.Path('../../lanes/sol-mathdb-primary-qualified-breadth-r728')
rows=json.loads((old/'literal-records.json').read_text()); ass={int(s.split('\t')[0]):s.split('\t')[1:] for s in (old/'assessments.tsv').read_text().splitlines() if s}
selected={319825,320868,321049}
http=json.load(open('http-manifest.json')); hmap={x['name']:x for x in http}
results={}
for x in rows:
 r=x['record'];i=r['mathdb_id'];a=ass[i]
 results[str(i)]={
  'mathdb_id':i,'title':r['title'],'canonical_url':r['canonical_url'],
  'literal_statement':r['statement'],'cached_record_sha256':x['canonical_record_sha256'],
  'primary_source_url':r['source_url'],
  'review_level':'primary_definitions_and_target_passages' if i in selected else 'cached_record_statement_only',
  'new_primary_body_review':i in selected,
  'inherited_statement_completeness':a[0],
  'restoration_or_scope_gap':a[1],
  'prior_lane_mathematical_disposition':a[2],
  'disposition':'HOLD_NOT_INVESTIGATED_BEYOND_CACHED_STATEMENT',
  'reason':'No renewed primary-body review. Inherited route assessment retained verbatim; neither unresolved status nor rejection as false is established.',
  'formal_status':'No complete source-statement Lean theorem; zero credit',
  'literal_lean_endpoint':None,'independent_review':'not performed; separate root-assigned task only',
  'discovery_count_credit':0,
  'prior_lane_evidence':str(old.resolve()/'assessments.tsv')
 }
for i,k in [(319825,'bspline'),(320868,'boolean'),(321049,'weyl')]:
 r=results[str(i)];r['source_evidence']={z:hmap[k][z] for z in ['url','sha256','file','date','status']};r['live_record_access']=dict(status=hmap['mathdb-'+str(i)]['status'],evidence=hmap['mathdb-'+str(i)]['file'],consequence='403: no access bypass; current solution state not verified');r['proof_attempt_file']='ORDINARY-PROOFS.md';r['bounded_prior_art_file']='PRIOR-ART.md'
r=results['319825'];r.update(disposition='EXCLUDE_ROUTINE_CLASSICAL_SAME_OBJECT_COROLLARY',reason='Complete ordinary root-pair factorization route; exact spline/Euler-Frobenius identity and negative simple roots already classical, explicitly in Janson Theorem 3.2 and Remark A.2. No credit for routine corollary or partial formalization.',ordinary_proof='complete for d>=2 and admissible m>=2*floor(d/2)+1; d=1 constant-symbol minimizer qualification',formal_feasibility='Possible but substantial exact sample/root/DFT bridges; no formal investment on excluded route',significance='Improves understanding of the stated circulant spectrum, but lacks a substantive new mechanism under this campaign standard')
r=results['320868'];r.update(disposition='HOLD_UNRESOLVED_AFTER_PROOF_ATTEMPTS',reason='Exact union/intersection definition restored. Coordinate compression loses squares in explicit example. Closure does not preserve cardinality; pair bound is too weak. No universal extremal proof.',remaining_mathematical_gap='Exact-cardinality extremal inequality for arbitrary n,d>=2 and arbitrary ambient ground sets',diagnostics='boolean-diagnostic.json',significance='Full resolution would be a substantive uniform set-family extremum; benchmark count and compression obstruction are not solutions',formal_feasibility='Finite counting feasible; unrestricted extremal theorem missing before Lean')
r=results['321049'];r.update(disposition='HOLD_UNRESOLVED_AFTER_PROOF_ATTEMPTS',reason='Source classical includes exceptional/nonreduced types. Exact A-type adjacency dynamic program and BFS only confirm ranks 2–5. Connectivity induction and empirical generator density do not give uniform diameter.',remaining_mathematical_gap='Uniform <=3 core-covering path for all irreducible integral-reflection root systems, including BC and E/F/G types',diagnostics='weyl-diagnostic.json',significance='A uniform diameter theorem would be substantive; finite-rank computation and adjacency restatement are not solutions',formal_feasibility='Root-system/Borel/core infrastructure and uniform witness missing; finite A-type certificate insufficient')
(P/'results.json').write_text(json.dumps(results,indent=2,ensure_ascii=False)+'\n')
# Record bounded registry scans and input reconciliation without overclaiming body search.
head=json.load(open('registry-head.txt')); tree=json.load(open('registry-preprints.txt'))
qs=['B-spline','small Weyl','Boolean algebra','Euler–Frobenius','319825','320868','321049']
scan={f:{q:pathlib.Path(f).read_text().lower().count(q.lower()) for q in qs} for f in ['registry-pinned-contents.txt','proofsearch.txt','prove2me.txt']}
scan.update(openai_head=head['sha'],head_date=head['commit']['committer']['date'],preprints_tree_truncated=tree['truncated'],preprints_tree_entries=len(tree['tree']),scope='Catalogue/path/landing-page lexical screen only; not full-body/full-registry clearance')
(P/'registry-scan.json').write_text(json.dumps(scan,indent=2)+'\n')
res=json.load(open('reservation.json'));assert set(map(int,results))==set(res['ids']);assert not set(map(int,results))&set(res['protected_ids']);assert len(results)==50
print('50 exact reserved IDs; 3 new primary passage reviews; no protected IDs; zero credit.')
