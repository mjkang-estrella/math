from pathlib import Path
import re,json,hashlib,subprocess,urllib.request,datetime
P=Path(__file__).parent; root=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research'); base=P.parent/'root-edge-irregulator-final-freeze-r1'
pat=re.compile(r'2608[.]27583|separable.derange|A393394|373199|composition ideals|composition.{0,35}rank.unimod|rank.unimod.{0,35}composition|2607[.]20595|373200|Pantone.{0,40}derange',re.I)
files=[];matches=[]
for f in root.rglob('*'):
 if not f.is_file() or P in f.parents:continue
 n=f.name.lower()
 if not any(x in n for x in ['summary','discovery','findings','proof','review','ledger','next']):continue
 if f.suffix.lower() not in ['.md','.json','.txt']:continue
 try:
  b=f.read_bytes();t=b.decode();files.append({'path':str(f.relative_to(root)),'sha256':hashlib.sha256(b).hexdigest()})
  for i,line in enumerate(t.splitlines(),1):
   if pat.search(line):matches.append({'path':str(f.relative_to(root)),'line':i,'text':line[:1800]})
 except (UnicodeError,OSError):pass
(P/'duplicate-audit.json').write_text(json.dumps({'all_dates':True,'patterns':pat.pattern,'files':files,'matches':matches},indent=2)+'\n')
# Fully decode required context, record immutable bytes; shared ledgers may later drift.
context=[]
for f in [root/'AGENTS.md',root/'sources/upstream.json',P.parent.parent/'AGENTS.md',P.parent.parent/'ledger.json',P.parent.parent/'prior-campaign-context.json',P.parent.parent/'NEXT.md',root/'frontier/campaigns/2026-10-26/new-discoveries/ledger.json']:
 b=f.read_bytes();t=b.decode();obj=json.loads(t) if f.suffix=='.json' else t
 context.append({'path':str(f),'sha256':hashlib.sha256(b).hexdigest(),'decoded':obj})
(P/'context.json').write_text(json.dumps(context,indent=2)+'\n')
log=json.loads((P/'http.json').read_text())
def fetch(name,url):
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'sources/'+name}
 try:
  with urllib.request.urlopen(url,timeout=30) as f:b=f.read(15000000);r['status']=f.status
  (P/'sources'/name).write_bytes(b);r.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));o=json.loads(b)
 except Exception as e:r['error']=str(e);o={}
 log.append(r);return o
heads={k:json.loads((P/'sources'/f'{k}-head.json').read_text())['sha'] for k in ['omega','openai']}
delta=fetch('omega-delta.json','https://api.github.com/repos/the-omega-institute/trureturing/compare/2130bf544f7858fc3c142bb9623b7ba9464e22ba...'+heads['omega'])
repo=fetch('sepder-repo.json','https://api.github.com/repos/rdbliss/sepder')
h=fetch('sepder-head.json','https://api.github.com/repos/rdbliss/sepder/commits/HEAD')
if h.get('sha'):fetch('sepder-tree.json','https://api.github.com/repos/rdbliss/sepder/git/trees/'+h['sha']+'?recursive=1')
reg={'heads':heads,'delta_files':[x['filename'] for x in delta.get('files',[])],'baseline_hits':[],'limits':'Complete baseline filenames only; inherited intermediate deltas not independently fully re-audited. No semantic all-proof coverage. Latest compare may not be complete.'}
for k in ['omega','openai']:
 for l in (base/f'{k}-tree.txt').read_text().splitlines():
  if re.search('separab|derange|123Avoid|FixedPoint.*Pattern|Pattern.*FixedPoint',l,re.I):reg['baseline_hits'].append({'registry':k,'path':l})
(P/'registries.json').write_text(json.dumps(reg,indent=2)+'\n');(P/'http.json').write_text(json.dumps(log,indent=2)+'\n')
print(json.dumps({'matches':matches,'registries':reg},indent=2))
