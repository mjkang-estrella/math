import pathlib,json,hashlib,resource,os,subprocess,itertools
resource.setrlimit(resource.RLIMIT_CPU,(60,60));resource.setrlimit(resource.RLIMIT_AS,(1536*1024**2,)*2);os.sched_setaffinity(0,{0,1})
L=pathlib.Path(__file__).resolve().parent.parent;B=L.parent.parent;sha=lambda b:hashlib.sha256(b).hexdigest();R=json.loads((L/'reservation.json').read_text());M=json.loads((B/'lanes/pi-mathdb-full-corpus-inventory-r301/manifest.json').read_text());out={}
for x in M['files']:
 if x['path'].startswith('corpus/'):
  p=B/'lanes/pi-mathdb-full-corpus-inventory-r301'/x['path'];h=sha(p.read_bytes());assert h==x['sha256'];out[str(p)]={'sha256':h,'matches_manifest':True}
(L/'chunk-verification.json').write_text(json.dumps(out,indent=2)+'\n')
checks=[]
for p,h in R['input_hashes'].items():
 q=pathlib.Path(p);checks.append({'path':p,'expected':h,'actual':sha(q.read_bytes()),'mutable':q.name=='ledger.json'})
(L/'input-verification.json').write_text(json.dumps(checks,indent=2)+'\n')
p=L.parent/'fresh-corpus-r5/openai-preprints.body';t=json.loads(p.read_text());terms=['roman','cyclotomic','mixed-volume','minkowski-sum','Samuels','equitable','Hurwitz','Sorensen'];hits=[x['path'] for x in t['tree'] if any(w.lower() in x['path'].lower() for w in terms)];(L/'registry-review.json').write_text(json.dumps({'live_head':json.loads((L/'sources/registry-head.json').read_text())['sha'],'tree_path':str(p),'sha256':sha(p.read_bytes()),'tree_sha':t['sha'],'truncated':t['truncated'],'entries':len(t['tree']),'terms':terms,'hits':hits,'depth':'path screen only; hits are not theorem-body findings; no global absence claim'},indent=2)+'\n')
ctx=[]
for p in [B/'ledger.json',B/'prior-campaign-context.json',L.parent/'ledger.json',B.parent/'2026-10-26/new-discoveries/ledger.json']:
 if p.exists():
  d=json.loads(p.read_text());ctx.append({'path':str(p),'sha256':sha(p.read_bytes()),'accepted':d.get('accepted'), 'excluded':{k:v for k,v in d.items() if any(w in k for w in ['reject','exclu','protect'])}})
(L/'ledger-families.json').write_text(json.dumps(ctx,indent=2)+'\n')
# Permanent identity for the chosen determinant-one boxes, an exact symbolic diagnostic.
import sympy as s
t,c=s.symbols('t c',positive=True);A=[t,1/t,1,1];BB=[1/t,t,1,1];C=[c,c,1/c,1/c];mat=[A,BB,C,C];perm=sum(s.prod(mat[i][p[i]] for i in range(4)) for p in itertools.permutations(range(4)));m=s.factor(perm/24);expr=((t+1/t)**2-2)/c**2/12+(t+1/t)/3+c**2/6;assert s.simplify(m-expr)==0;v=s.prod(A[i]+BB[i] for i in range(4));print('mixed-volume',m,'sum-volume',s.factor(v));(L/'box-diagnostic.json').write_text(json.dumps({'m':str(m),'sum_volume':str(s.factor(v)),'scope':'axis-aligned determinant-one boxes in dimension4 only; mixed-volume permanent identification not formalized'},indent=2)+'\n')
print('20 chunk hashes verified; registry entries',len(t['tree']) if isinstance(t,dict) else 'see receipt')
