import json,hashlib,gzip,re,datetime,sys
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5];B=L.parent.parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
contexts=[R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md',L.parent/'root-r126-r127-handback/DECISION.md',L.parent/'root-r128-r129-handback/DECISION.md',L.parent/'root-r133-handback/DECISION.md',R/'sources/upstream.json',R/'sources/CONTENTS.md']
if sys.argv[1]=='context':
 rows=[]
 for i,p in enumerate(contexts):
  dst=L/'sources'/('context-'+str(i)+p.suffix);dst.write_bytes(p.read_bytes());rows.append(dict(path=str(p),snapshot=str(dst.relative_to(L)),sha256=h(dst)))
 (L/'context-receipts.json').write_text(json.dumps(rows,indent=2)+'\n')
 ledger=json.loads((B/'ledger.json').read_text());print('ledger',[(j['number'],j['title']) for j in ledger['accepted']])
 c=json.loads((L/'sources/omega-compare.json').read_text());r=dict(base=c.get('base_commit',{}).get('sha'),merge_base=c.get('merge_base_commit',{}).get('sha'),head='8a9f34a98b9b36553571808bf4187356a94a25ae',status=c.get('status'),ahead_by=c.get('ahead_by'),commits=len(c.get('commits',[])),total_commits=c.get('total_commits'),files=len(c.get('files',[])),paths=[f['filename'] for f in c.get('files',[])],semantic_clearance=False)
 r['caps_ok']=r['commits']==r['total_commits'] and r['total_commits']<250 and r['files']<300;r['ancestry_ok']=r['base']==r['merge_base']=='e1ff281c3881e633b86be1072f049a778bdbdc1b'
 (L/'registry-delta-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
 science=[]
 with gzip.open(L/'history-aliases.jsonl.gz','rt') as f:
  for line in f:
   sha,p=json.loads(line)
   if re.search(r'sol-fresh-source-discovery-r11[123]/(?:SUMMARY|discovery|PROOF|review|DECISION)',p,re.I):science.append([sha,p])
 (L/'retained-r111-r113.json').write_text(json.dumps(science,indent=2)+'\n');print('original science paths retained',len(science))
elif sys.argv[1]=='final':
 receipts=[json.loads(p.read_text()) for p in sorted((L/'sources').glob('*.receipt.json'))]
 prov=dict(status='UNRESOLVED; no nominee',created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),counts_inherited=dict(additional=9,total=39,next=40),sources=receipts,history='history-receipt.json',registry='registry-delta-receipt.json',external_mutations=False,git=False,children=False,formalization=False,manuscript=False,guard_path=str(L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),guard_sha256=h(L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),limits=dict(AS_MiB=512,group_RSS_MiB=512,CPU_s=210,wall_s=230,sample_ms=40,BLAS_threads=1))
 (L/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
 excluded={'finalmanifest.json','scientific-freeze.json'}
 science=[p for p in L.rglob('*') if p.is_file() and p.name not in excluded and not p.name.startswith('context-') and p.name!='context-receipts.json']
 (L/'scientific-freeze.json').write_text(json.dumps({str(p.relative_to(L)):h(p) for p in sorted(science)},indent=2)+'\n')
 files=[p for p in L.rglob('*') if p.is_file() and p.name!='finalmanifest.json']
 (L/'finalmanifest.json').write_text(json.dumps({str(p.relative_to(L)):dict(sha256=h(p),bytes=p.stat().st_size) for p in sorted(files)},indent=2)+'\n');print('manifest entries',len(files))
elif sys.argv[1]=='verify':
 m=json.loads((L/'finalmanifest.json').read_text());assert all(h(L/p)==j['sha256'] and (L/p).stat().st_size==j['bytes'] for p,j in m.items());print('PASS',len(m),'entries')
