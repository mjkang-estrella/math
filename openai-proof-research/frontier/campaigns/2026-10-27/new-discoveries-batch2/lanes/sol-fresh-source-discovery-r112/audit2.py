from pathlib import Path
import os,re,json,hashlib,datetime
L=Path(__file__).parent;R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
pat=re.compile(rb'(?<![0-9A-Za-z])(?:2409\.12404|2503\.22377|2402\.00949|2605\.09609|367738|361688)(?:v[0-9]+)?(?![0-9A-Za-z])|cycle.assign|Hayashi|Houshan|Filipi|Kubjas|minimal.filling',re.I)
for s in [b'2409.12404',b'367738',b'2503.22377v1']:assert pat.search(s)
for s in [b'12409.12404',b'2409x12404',b'13677380',b'X367738Y']:assert not pat.search(s)
n=hits=0
with (L/'required-content.jsonl').open('w') as co,(L/'required-hashes.jsonl').open('w') as inv,(L/'required-hits.jsonl').open('w') as ho:
 for base,dirs,files in os.walk(R):
  dirs[:]=sorted(d for d in dirs if d not in ['.git','node_modules','.lake','__pycache__'] and Path(base,d)!=L)
  for name in sorted(files):
   p=Path(base,name);rel=str(p.relative_to(R));lo=rel.lower();nm=name.lower()
   wanted=(nm in ['summary.md','discovery.md','proof.md','findings.md','ledger.json','next.md','agents.md','prior-campaign-context.json'] or nm.startswith('screened-out') or 'review' in nm or ('review' in lo and p.suffix.lower() in ['.md','.txt','.py','.lean','.tex']) or ('tools/scripts/agent/openproblem' in lo) or ('agent' in lo or 'openproblem' in lo) and p.suffix.lower() in ['.md','.txt','.py','.sh'])
   if not wanted:continue
   h=hashlib.sha256();size=0
   try:
    with p.open('rb') as f:
     line=0
     while b:=f.readline(32768):
      line+=1;h.update(b);size+=len(b)
      row={'path':rel,'chunk':line,'text':b.decode(errors='replace')};co.write(json.dumps(row)+'\n')
      if pat.search(b):ho.write(json.dumps(row)+'\n');hits+=1
    inv.write(json.dumps({'path':rel,'bytes':size,'sha256':h.hexdigest()})+'\n');n+=1
   except OSError as e:inv.write(json.dumps({'path':rel,'error':str(e)})+'\n')
print(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':n,'hits':hits,'regex_tests':'PASS including version suffix; initial audit suffix omission corrected','scope':'all-date required named files, review trees and agent/openproblem sources; content streamed; no semantic absence claim'}))
