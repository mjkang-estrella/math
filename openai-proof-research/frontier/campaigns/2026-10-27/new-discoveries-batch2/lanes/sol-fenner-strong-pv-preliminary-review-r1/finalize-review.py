import resource,signal,os,json,pathlib,hashlib,datetime,re
resource.setrlimit(resource.RLIMIT_AS,(536870912,)*2);resource.setrlimit(resource.RLIMIT_CPU,(15,)*2);signal.alarm(25)
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
p=pathlib.Path(__file__).parent; lanes=p.parent
f=json.loads((lanes/'root-fenner-preliminary-freeze-r1/review-freeze.json').read_text());c=pathlib.Path(f['candidate'])
def sha(x):return hashlib.sha256(x.read_bytes()).hexdigest()
a={n:sha(c/n)==v for n,v in f['sha256'].items()}; b={n:sha(p/'candidate-copy'/n)==v for n,v in f['sha256'].items()};assert all(a.values()) and all(b.values());(p/'freeze-after.json').write_text(json.dumps({'original':a,'private_copy':b},indent=2))
reg=[]
for row in json.loads((p/'candidate-copy/final-registry-screen.json').read_text()):
 q=pathlib.Path(row['file']); local=p/'candidate-copy/sources'/q.name
 if not local.exists():local=q
 h=sha(local);assert h==row['sha256'];d=json.loads(local.read_text());paths=[x['path'] for x in d.get('tree',[])];reg.append({'path':str(local),'sha256':h,'entries':len(paths),'truncated':d.get('truncated'),'matches':[x for x in paths if re.search('fenner|strong.?pv|aperiodic|a.convex|extrapolation',x,re.I)]})
d=json.loads((p/'sources/omega-delta.json').read_text());delta={'total_commits':d.get('total_commits'),'returned_commits':len(d.get('commits',[])),'changed_files':len(d.get('files',[])),'matches':[x['filename'] for x in d.get('files',[]) if re.search('fenner|strong.?pv|aperiodic|a.convex|extrapolation',x['filename'],re.I)]};(p/'registry-review.json').write_text(json.dumps({'verified_base_trees':reg,'fresh_omega_delta':delta},indent=2))
assert sha(p/'sources/jin.pdf')==sha(p/'sources/jin-original.pdf')
coverage={
'candidate-copy/sources/fenner.html':'Actual journal HTML: introduction; hull definitions; Theorem3.6 and surrounding Bernstein discussion; sPV Definition4.1; uniform-discrete Definition4.4; norm/model-set context; Conjecture11.1. No journal PDF claimed.',
'candidate-copy/sources/fenner-extended.pdf':'Actual extended manuscript text read: Theorem8.2, section8 hypotheses and density/reduction proof chain, concluding proof and Lemma8.4; earlier hull dichotomy. arXiv1212.2889v6 header.',
'candidate-copy/sources/fenner-open.pdf':'Actual companion body: initial definitions, main results, Theorem1.9 and equations1-2, Conjecture2.1 and following model-set/open-problems discussion.',
'sources/jin.pdf':'ALL five pages actual body: Theorem1, Lemmas2-4, Proposition5, proof of theorem and references. Complete same-object prior proof.',
'sources/jin-original.pdf':'Original-commit bytes hash-equal to all-pages-read pinned PDF.',
'sources/campbell.html':'Actual full proof body: Lemmas1-6, Ferguson theorem quotation, Theorem2 and proof. Totally-real scope only.',
'sources/pinch.pdf':'ALL six pages actual text: finite generation, multiplication, Bernstein description, sparsity dichotomy, Theorem8 proof, Proposition12 proof, Theorem15 proof and final conjecture. Direct HTTP succeeded; web PDF access failed.',
'sources/meyer.pdf':'Selective primary reading: introduction and section1 TheoremsI-IV and related trace/Minkowski proof discussion. Not a full-book or exhaustive theorem audit; 1972 book unread.',
'sources/clopen.html':'Live record and resolution link; only lead generation, not proof verification.',
'sources/aim-history.json':'Actual public API path history: one addition, c1f79e312f2b7bae2636469c506376a873100691, both author/committer 2026-10-14T03:41:33Z.'}
http=json.loads((p/'http-review.json').read_text())+json.loads((p/'http-delta.json').read_text())
up=json.loads((p/'candidate-copy/provenance.json').read_text());old={x['file']:x['url'] for x in up['http'] if x.get('status')==200}
files=[]
for n,body in coverage.items():
 q=p/n;url=next((x['url'] for x in http if 'sources/'+x['file']==n),None)
 if n.startswith('candidate-copy/sources/'):url=old.get(q.name)
 files.append({'path':n,'url':url,'sha256':sha(q),'actual_body_coverage':body})
mathroot=pathlib.Path('openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/Mathlib');mfiles=['Analysis/SpecialFunctions/Bernstein.lean','RingTheory/Polynomial/Bernstein.lean','NumberTheory/NumberField/CanonicalEmbedding/Basic.lean','Algebra/Module/ZLattice/Basic.lean','RingTheory/Trace/Basic.lean']
# Source inventory only; no compilation or assertion that any file proves the target.
minv=[{'path':str(mathroot/x),'sha256':sha(mathroot/x)} for x in mfiles]
out={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'verdicts':{'SOURCE':'PASS','MATH':'ordinary PASS','NOVELTY':'FAIL','SUBSTANTIVE':'FAIL campaign eligibility','recommendation':'EXCLUDE','FORMAL':'NOT VERIFIED; no compilation'},'freeze_files':len(a),'freeze_before':'freeze-before.json','freeze_after':'freeze-after.json','primary_body_coverage':files,'http':http,'registry':'registry-review.json','search_queries':['Fenner strong PV conjecture proof','Pinch a-convexity 1985 63 68 pdf','Meyer algebraic numbers harmonic analysis 1972 pdf Pisot','integer polynomial approximation ideals interval','Fenner Campbell conjecture','Fixed-Parameter Extrapolation proof conjecture strong PV'],'search_limits':'Bounded live web search and direct public HTTP; not worldwide absence. Current AIM same-object proof found via clopen. Web tool Pinch PDF inaccessible but direct public request succeeded without bypass. No challenges or access controls bypassed.','mathlib_pin':'d13f23b723b8a846827a245b89c10fc7d3f11612','mathlib_inventory':minv,'checker':{'script':'check_review.py','sha256':sha(p/'check_review.py'),'results':'checks-review.json','log':'check-review.log','limits':'512MiB AS /20 CPU /25 wall alarm /28 external wall / BLAS1'},'counts_unchanged':True,'candidate_credit':0,'external_mutations':False,'children':False}
(p/'provenance.json').write_text(json.dumps(out,indent=2));print(json.dumps({'freeze':len(a),'original_and_copy_unchanged':all(a.values()) and all(b.values()),'prior_pdf_hash_equal':True,'registry_delta':delta,'verdicts':out['verdicts']},indent=2))
