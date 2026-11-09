# Scope dedup: search r304 accepted-exclusions families + historical dispositions and r363 coverage for topic keywords / arXiv ids of this batch.
import json,sys,re
L=sys.argv[1]
ae=json.load(open(L+'/root-mathdb-accepted-exclusions-r304/accepted-exclusions.json'))
fam=ae['families']; print('families',len(fam), 'keys', sorted(fam[0]) if isinstance(fam,list) else type(fam))
blob=json.dumps(ae,ensure_ascii=False)+json.dumps(json.load(open(L+'/root-mathdb-accepted-exclusions-r304/historical-dispositions.json')),ensure_ascii=False)
blob2=open(L+'/root-mathdb-cayley-review-intake-r363/coverage-delta.json').read()
ids=json.load(open(sys.argv[2]))
arx=sorted({re.search(r'abs/([0-9.]+)',d['record_source_url']).group(1) for d in ids})
kw=['Banzhaf','abelianis','abelianiz','cyclically presented','resistance','linear 2-tree','2-tree','degree sequence','voting','Lucas','Fibonacci','claw-free','perfect matching','Petersen','permanent','sorting network','Vinogradov','primitive root','Erd','amplituhedron','Hilbert scheme','Penner','spider','conflict-free','dominating']
print('arxiv-id hits:',[a for a in arx if a in blob or a in blob2])
print('keyword hits:',{k:(blob.count(k),blob2.count(k)) for k in kw if k in blob or k in blob2})
for f in (fam if isinstance(fam,list) else []):
    t=json.dumps(f,ensure_ascii=False)
    if any(k.lower() in t.lower() for k in ['banzhaf','abelian','resistance','2-tree','degree sequence','matching']): print('FAMILY:',t[:300])
