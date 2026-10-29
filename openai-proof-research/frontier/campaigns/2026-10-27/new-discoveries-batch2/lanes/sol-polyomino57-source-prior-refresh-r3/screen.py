import json,re,resource,signal,hashlib,zipfile
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(220)
D=Path(__file__).resolve().parent;B=D.parent;rows={}
pat=re.compile(r'polyom|395495|exley|container|kakeya|universal.*(shape|region)|animal',re.I)
for p in sorted((D/'live').glob('*.json')):
 j=json.loads(p.read_text())
 if 'tree' not in j:continue
 rows[p.name]=dict(sha=j['sha'],entries=len(j['tree']),truncated=j.get('truncated'),hits=[x for x in j['tree'] if pat.search(x['path'])])
 if p.name in ['omega-D5.json','omega-Problems.json']:
  old=json.loads((B/'sol-steiner-reflection-preliminary-review-r1/live'/p.name.replace('omega-','')).read_text());a={x['path']:x['sha'] for x in old['tree']};b={x['path']:x['sha'] for x in j['tree']}
  rows[p.name]['delta_from_2ad83']=dict(added=[k for k in b if k not in a],changed=[k for k in b if k in a and b[k]!=a[k]],removed=[k for k in a if k not in b])
(D/'tree-screen.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
A=B/'root-polyomino57-full-formal-adoption-r1';ad=json.loads((A/'ADOPTION.json').read_text());bad=[]
for name,m in ad['preserved_files'].items():
 b=(A/name).read_bytes()
 if hashlib.sha256(b).hexdigest()!=m['sha256'] or len(b)!=m['bytes']:bad.append(name)
with zipfile.ZipFile(A/'source-only-component.zip') as z:
 names=z.namelist(); print('ZIP root',names[:12]);print('Manifest type',str(json.loads((A/'source-manifest.json').read_text()))[:800])
 for name in names:
  if name.endswith('/Grid.lean') or name.endswith('/Witness.lean') or name.endswith('/AllCases.lean'):
   print(name,z.read(name).decode()[:16000])
print('ADOPTION mismatches',bad)
