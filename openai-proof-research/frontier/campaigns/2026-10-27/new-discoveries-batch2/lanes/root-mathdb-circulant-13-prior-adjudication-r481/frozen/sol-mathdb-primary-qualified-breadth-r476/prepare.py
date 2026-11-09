import pathlib,json,hashlib,datetime,collections,re
D=pathlib.Path(__file__).resolve().parent;L=D.parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
bindings={x['path']:x for x in json.loads((D/'bindings.json').read_text())}
# Flat direct bindings only. Do not read bindings belonging to these originals.
for name in ['root-mathdb-cayley-review-intake-r363','root-mathdb-accepted-exclusions-r304']:
 for x in json.loads((L/name/'bindings.json').read_text()):
  for key in ['original','copy']:
   if key in x:
    p=pathlib.Path(x[key]);assert h(p)==x['sha256'],str(p)
    if 'size' in x:assert p.stat().st_size==x['size']
    bindings[str(p)]={'path':str(p),'sha256':h(p),'bytes':p.stat().st_size}
# Write a new supplement, preserve the first freeze and receipt unchanged.
(D/'flat-bindings.json').write_text(json.dumps(list(bindings.values()),indent=2)+'\n')
rows=json.loads((D/'assigned-records.json').read_text());assessment={}
for line in (D/'assessment.tsv').read_text().splitlines():
 a=line.split('\t');assert len(a)==6,a;assessment[int(a[0])]=a
assert len(assessment)==50
assessment[336929][1:3]=['PUBLIC_SUCCESSOR_STATEMENT_MATCH','Meagher-Sin arXiv1911.11252v3 Definition 1.2 and Theorem 1.3 state exactly that every two-transitive group has the EKR-module property. Primary statement read, not a full proof-dependency audit.']
assessment[336790][1:3]=['PUBLIC_SUCCESSOR_RANGE_MATCH_BOUNDARY_HOLD','Binner-Rattan arXiv2006.15287v5 Theorem 3 proves the stronger strict uniform inequality for L>=3 and all impermissible parts. Zang-Zeng Theorem 1.1 independently covers k=L. Literal L=2,s=1 lies outside these theorem hypotheses; closing that elementary boundary is uncredited routine/domain work.']
assessment[337624][1:3]=['HOLD_DOMAIN_STANDARD_OBSTRUCTION','Executed exact endpoint-cell certificate shows the source-proposed epsilon/3 perturbation adds codeword {2} to code {empty,12,23,3}. This code has a standard connectedness obstruction to open convexity. Source Definition 5 restricts minimal open dimension to open-convex codes; exploiting its undefined value outside that domain is not eligible. The restricted conjecture remains unproved here.']
passages=json.loads((D/'passages.json').read_text());pm={p['file']:p for p in passages}
sources=[]
for file in ['sources.jsonl','successor-access.jsonl','successor-bodies.jsonl']:
 for line in (D/file).read_text().splitlines():
  s=json.loads(line)
  if s.get('file','').endswith('.pdf'):
   t=D/pathlib.Path(s['file']).with_suffix('.txt');head=t.read_text().splitlines()[:50];s['version']=next((x.strip() for x in head if 'arXiv:' in x),s.get('version'))
  sources.append(s)
(D/'sources.json').write_text(json.dumps(sources,ensure_ascii=False,indent=2)+'\n')
public={336113,336999,337232,337544,336929,336790};proofpass={336113,336999,337544}
# These target questions were displayed explicitly in primary text. Others get only a partial-reading claim.
matched={336019,336028,336051,336078,336113,336162,336182,336274,336397,336490,336633,336693,336737,336745,336790,336836,336847,336889,336929,336950,336999,337096,337136,337150,337232,337261,337325,337328,337345,337367,337440,337442,337453,337493,337533,337543,337544,337545,337568,337624,337632,337669,337836,337854,337857,337870}
result=[]
for x in rows:
 r=x['record'];i=r['mathdb_id'];a=assessment[i];file='sources/'+r['source_url'].rsplit('/',1)[-1]+'.txt';p=pm[file]
 entry={**x,'mathdb_id':i,'literal_statement':r['statement'],'disposition':a[1],'full_scope_mechanism_or_obstacle':a[2],'decisive_next_check_planned':a[3],'expected_certificate_size':a[4],'formal_dependencies':a[5],'source':{'url':r['source_url'],'version':p['version'],'primary_text_file':file,'primary_statement_passage_read':i in matched,'reading_level':'selected source passages only; incomplete primary audit' if i not in matched else 'target question or matching theorem passage read','whole_body_read':False,'passage_locators':[{'start_line':s['start_line'],'end_line':s['end_line']} for s in p['passages']],'locator_limit':'Extracted excerpts/locator file are not themselves a proof audit; target-specific additional passages described in notes.'},'proof':{'new_full_scope_proof':False,'public_proof_passage_read':i in proofpass,'complete_dependency_audit':False,'formalization_run':False},'registry':{'status':'HOLD','MathDB_requests':0,'reason':'Inherited 429; current MathDB and public proof-registry clearance not obtained. Denied AIProofWatch and routes remain parked.'},'successor_review':{'status':'primary statement passages read' if i in {336929,336790} else 'bounded metadata search only, inconclusive' if i in {337624,337854,337870} else 'HOLD not cleared; source-internal results only'},'bounded_check':{'status':'executed exact endpoint-cell sanity certificate; not eligible endpoint' if i==337624 else 'executed primary statement comparison; no numerical search' if i in public else 'not executed; next calculation is planned only','artifact':'bounded-check.json' if i==337624 else None},'strongest_objection':a[2],'prior_art_gaps':'No current registry head or full successor/dependency audit; absence of located results is not novelty evidence. Public matches already exclude discovery credit.','accepted_credit':0,'proposal':False}
 if i==336929:entry['source']['successor_passages']={'file':'sources/1911.11252v3.txt','lines':'64-101','labels':['Definition 1.2','Theorem 1.3']}
 if i==336790:entry['source']['successor_passages']={'files':['sources/2006.15287v5.txt','sources/2004.12871v2.txt','sources/2205.06033v3.txt'],'labels':['Conjecture 2; Theorem 3','Theorem 1.1','introduction comparison'],'limit':'L>=3 theorem range; L=2,s=1 boundary remains explicitly outside cited theorem'}
 result.append(entry)
(D/'dispositions.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n');(D/'proposals.json').write_text('[]\n')
counts=collections.Counter(x['disposition'] for x in result)
(D/'screening-counts.json').write_text(json.dumps({'exact_assigned':50,'baseline_reported_reviews':3233,'counts':dict(counts),'primary_target_passages_read':len(matched),'source_pdfs_retained':52,'whole_bodies_read':0,'complete_dependency_audits':0,'proposals':0,'accepted_additional':9,'accepted_total':39,'next_global':40},indent=2)+'\n')
print('Prepared exact fifty dispositions, zero proposals',dict(counts))
