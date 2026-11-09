from pathlib import Path
import json,hashlib,re,urllib.request
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r157');P=R/'packet/private'
def sha(b):return hashlib.sha256(b).hexdigest()
# Only exact direct exceptions, never their containing namespaces.
completed=['discovery-arithmetic-r155-parent/assessment.md','fresh-arithmetic-discovery-r155/packet/FINAL.md','fresh-arithmetic-discovery-r155/packet/notes/01-operative-comparison.md','fresh-arithmetic-discovery-r155/packet/notes/02-initial-model-accounting.md','fresh-arithmetic-discovery-r155/packet/notes/03-uniformity-and-unpaid-operation.md','fresh-arithmetic-discovery-r155/packet/private/READING-ISOLATION.md']
ext=[]
for i,s in enumerate(completed):
 p=Path('frontier/campaigns/2026-10-14')/s;b=p.read_bytes();q=P/'completed'/f'{i:02d}.txt';q.parent.mkdir(exist_ok=True);q.write_bytes(b);ext.append({'path':p.as_posix(),'read_intervals':[[0,len(b)]],'sha256':sha(b),'copy':q.relative_to(P).as_posix()})
(P/'completed-extents.json').write_text(json.dumps(ext,indent=2)+'\n')
for s,n in [('AGENTS.md','AGENTS.md'),('sources/upstream.json','upstream.json')]: (P/n).write_bytes(Path(s).read_bytes())
with open('frontier/NEW-TEN-2026-10-14.md','rb') as f:f.seek(4801);b=f.read(1546)
(P/'acceptance-4801-6347.txt').write_bytes(b)
auth=json.loads((P/'authentication.json').read_text());cov=[];edges=[]
classread={'README.md','build/main.tex','build/sections/history.tex','build/sections/quasiprojective.tex','build/figures/proof-overview.tex'}
for e in auth:
 path=e['path'];rel='/'.join(path.split('/')[2:]);full=('Symmetry-of-' in path and not path.endswith('.pdf')) or ('Semialgebraic-universal-' in path and rel in classread)
 cov.append({'path':path,'bytes':e['size'],'sha256':e['sha256'],'read_intervals':[[0,e['size']]] if full else [],'unread_intervals':[] if full else [[0,e['size']]],'status':'complete semantic read' if full else 'authenticated only'})
 if full and path.endswith('.tex'):
  t=(P/'upstream'/path).read_text()
  for m in re.finditer(r'\\(?:input|include|bibliography)\{([^}]+)\}',t):edges.append({'from':path,'include':m.group(1)})
(P/'source-coverage.json').write_text(json.dumps(cov,indent=2)+'\n');(P/'include-edges.json').write_text(json.dumps(edges,indent=2)+'\n')
primary=[]
for n,intervals in [('Vey1970',None),('KPv2',None),('Piecewise2026',None),('LiuWu',[[0,27000],[28240,43000],[77208,108305]]),('Zimmer2021',[])]:
 b=(P/'primary'/f'{n}.txt').read_bytes();intervals=[[0,len(b)]] if intervals is None else intervals
 primary.append({'name':n,'text_bytes':len(b),'text_sha256':sha(b),'read_intervals':intervals})
(P/'primary-extents.json').write_text(json.dumps(primary,indent=2)+'\n')
versions=[]
for n,url in [('LiuWu','https://arxiv.org/pdf/1801.00459v3'),('Piecewise2026','https://arxiv.org/pdf/2610.19807v1')]:
 try:
  b=urllib.request.urlopen(url,timeout=30).read();stored=(P/'primary'/f'{n}.pdf').read_bytes();versions.append({'name':n,'versioned_url':url,'sha256':sha(b),'matches_initial_download':b==stored});assert b==stored
 except Exception as e:versions.append({'name':n,'error':str(e)})
(P/'primary/version-confirmation.json').write_text(json.dumps(versions,indent=2)+'\n')
print('Complete source text reads',sum(bool(x['read_intervals']) for x in cov),'of',len(cov),'blobs; version confirmations',versions)
