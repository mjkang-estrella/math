from pathlib import Path
import json,hashlib,os,datetime
R=Path(__file__).resolve().parents[1]
E={'MANIFEST.json','FINAL.json','REPORT.md','SHA256SUMS'}
assert not any((R/n).exists() for n in ['MANIFEST.json','FINAL.json','SHA256SUMS']),'already sealed'
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
freeze=sha((R/'packet/public/frozen-scope.md').read_bytes())
assert freeze=='cc916afef1373c1b3c0abdee271a4c2769f887f664e8c9b2b16b1b381c0de221'
rows=[]
for d,ds,fs in os.walk(R,topdown=True,followlinks=False):
 for name in ds+fs:
  s=name.lower()
  assert not (s.startswith(('t373e135-','k369r134-','t088p133-')) or ('analytic' in s and any(v in s for v in ['r135','r136','r137'])) or ('arithmetic' in s and 'r107' in s)),'excluded component'
  assert not (Path(d)/name).is_symlink(),'symlink'
 for name in fs:
  p=Path(d)/name;rel=p.relative_to(R).as_posix()
  if rel in E:continue
  b=p.read_bytes();rows.append({'path':rel,'bytes':len(b),'sha256':sha(b)})
rows.sort(key=lambda x:x['path'])
dump(R/'MANIFEST.json',{'format':'r143-exact-files-v1','scope':'All payload files in exclusive r143 root; only four root envelopes excluded. Includes private bodies under original rights; hashes do not confer redistribution rights.','envelopes':sorted(E),'files':rows})
final={'status':'FULL AUTHOR-PROOF NOMINEE; ungraded','candidate':'T177C143','runner':'Codex / GPT-6 Astra / high / default service tier','sealed':datetime.datetime.now(datetime.timezone.utc).isoformat(),'publication':'STOPPED','manifest_sha256':sha((R/'MANIFEST.json').read_bytes()),'report_sha256':sha((R/'REPORT.md').read_bytes()),'verifier_path':'packet/public/verify.py','verifier_sha256':sha((R/'packet/public/verify.py').read_bytes()),'frozen_scope_path':'packet/public/frozen-scope.md','frozen_scope_sha256':freeze,'hand_off':'packet/public/handoff.md','payload_files':len(rows),'limitations':'Author proof only. Independent correctness/contribution reviews unperformed. No acceptance/count/formal/manuscript/release gate. Reading/search/preservation limits explicit; ledger changed between late observations.'}
dump(R/'FINAL.json',final)
anchors={n:sha((R/n).read_bytes()) for n in ['FINAL.json','MANIFEST.json','REPORT.md']}
(R/'SHA256SUMS').write_text(''.join(anchors[n]+'  '+n+'\n' for n in anchors))
print('Payload files:',len(rows),'bytes:',sum(x['bytes'] for x in rows))
print((R/'SHA256SUMS').read_text(),end='')
