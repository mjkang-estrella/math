import json,hashlib,gzip,shutil,time
from pathlib import Path
L=Path(__file__).resolve().parent;B=L.parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for x in iter(lambda:f.read(131072),b''):h.update(x)
 return h.hexdigest()
def save(n,v):(L/n).write_text(json.dumps(v,indent=2))
if not (L/'source-lock.json').exists():
 originals=[]
 for lane in ('sol-fresh-source-discovery-r74','sol-fresh-source-discovery-r79','sol-fresh-source-discovery-r84'):
  p=B/lane/'discovery.md';q=L/'sources'/(lane+'-discovery.md');q.write_bytes(p.read_bytes());originals.append({'original':str(p),'copy':str(q.relative_to(L)),'sha256':sha(q)})
 p=L.parents[2]/'2026-10-26/new-discoveries/novelty-rejections.md'
 # Campaigns is three levels above lane, resolve explicitly.
 p=L.parents[3]/'2026-10-26/new-discoveries/novelty-rejections.md'
 q=L/'sources/first-batch-rejections.md';q.write_bytes(p.read_bytes());originals.append({'original':str(p),'copy':str(q.relative_to(L)),'sha256':sha(q)})
 save('original-reads.json',originals)
 save('source-lock.json',[{'copy':str(p.relative_to(L)),'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted((L/'sources').iterdir()) if p.is_file()])
 h=json.loads((L/'sources/omega-current-head.json').read_text());d=json.loads((L/'sources/omega-current-delta.json').read_text())
 save('registry-correction.json',{'error_preserved':'registry-receipt.json used main, not default HEAD; not a valid current Omega observation','actual_HEAD':h['sha'],'committer_date':h['commit']['committer']['date'],'delta_total_commits':d.get('total_commits'),'delta_files':len(d.get('files',[])),'delta_status':d.get('status'),'comparison_merge_base':d.get('merge_base_commit',{}).get('sha'),'HOLD':'Historical 0d4-to-5e2 300-file cap remains. No complete current semantic clearance.'})
 # Preserve stream hashes and mappings without an uncompressed inventory packet.
 for name in ('pathmap.jsonl','audit.sqlite'):
  p=L/name
  if p.exists():
   oldsha=sha(p)
   with p.open('rb') as f,gzip.open(str(p)+'.gz','wb',compresslevel=6) as g:shutil.copyfileobj(f,g,131072)
   save(name+'.compression.json',{'uncompressed_sha256':oldsha,'compressed_sha256':sha(Path(str(p)+'.gz'))})
   p.unlink()
 mutable=[]
 for r in json.loads((L/'context-sources.json').read_text()):
  now=sha(Path(r['original']));mutable.append({**r,'current_original_sha256':now,'changed':now!=r['sha256']})
 save('context-drift.json',mutable)
 save('provenance.json',{'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'lane':str(L),'credit':0,'candidates':3,'source_receipts':'http.jsonl','source_lock':'source-lock.json','context':'context-sources.json','original_reads':'original-reads.json','registry':'registry-correction.json','scope':'negative selection only; no complete novelty clearance','limits':['original scan is lexical and size/extension bounded','full historical original rejection reading not complete','journal request returned HTTP200 Incapsula HTML, not PDF; stopped','wrong arXiv2005.10967 PDF preserved, never mathematical evidence','wrong main-branch registry observation preserved and corrected separately','historical capped registry interval not repaired; no positive clearance']})
 rows=[]
 for p in sorted(L.rglob('*')):
  if p.is_file() and p.name!='finalmanifest.json':rows.append({'path':str(p.relative_to(L)),'bytes':p.stat().st_size,'sha256':sha(p)})
 save('finalmanifest.json',rows);print('sealed',len(rows),'files')
