from pathlib import Path
import json,hashlib,shutil,zipfile,stat
B=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/nanostar-manuscript-r1');P=B.parent;D=P/'expanded-corpus-r162';R=P/'nanostar-review-r1'
def h(p): return hashlib.file_digest(open(p,'rb'),'sha256').hexdigest()
files=set()
for root in [D/'sources',D/'logs',D/'lean',R/'logs']:
 for f in root.rglob('*'):
  if f.is_file() and not f.is_symlink(): files.add(f)
for rel in ['NANOSTAR.md','SUMMARY.md','results.json','raw/349177.jsonl','extracted.json','outputs/totient-stage4-certificate.json','outputs/totient-independent.json','lean-status.json','proof-source.zip']: files.add(D/rel)
for rel in ['REVIEW.md','review.json','tmp/published-271.png','tmp/deutsch-639.png']: files.add(R/rel)
files.add(P/'nanostar-root-ruling-r1.json')
snapshot={str(f.relative_to(P)):{'sha256':h(f),'bytes':f.stat().st_size} for f in sorted(files)}
(B/'inputs-before.json').write_text(json.dumps(snapshot,indent=2)+'\n')
for f in sorted(files):
 dest=B/'frozen'/f.relative_to(P);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,dest)
(B/'proof-source.zip').write_bytes((D/'proof-source.zip').read_bytes());assert h(B/'proof-source.zip')=='5aa1150cb685221b2f9dbfbab4cd9eff9f503d917add10b62a491a1e19d81fac'
entry=json.loads((D/'results.json').read_text())['349177'];(B/'mathdb-entry.json').write_text(json.dumps(entry,indent=2)+'\n')
# Preflight all entries before extracting, with no archive-supplied execution.
out=B/'packet-extracted';out.mkdir(exist_ok=True);seen=set();entries=[];total=0
with zipfile.ZipFile(B/'proof-source.zip') as z:
 for i in z.infolist():
  p=Path(i.filename);mode=i.external_attr>>16
  assert not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename and i.filename not in seen
  assert not stat.S_ISLNK(mode) and (not stat.S_IFMT(mode) or stat.S_ISREG(mode) or stat.S_ISDIR(mode))
  assert i.file_size<32*1024**2
  total+=i.file_size;assert total<128*1024**2;seen.add(i.filename)
 for i in z.infolist():
  p=out/i.filename
  if i.is_dir(): p.mkdir(parents=True,exist_ok=True);continue
  p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(z.read(i));entries.append({'path':i.filename,'sha256':h(p),'bytes':i.file_size})
(B/'receipts/safe-extraction.json').write_text(json.dumps({'status':'PASS','packet_sha256':h(B/'proof-source.zip'),'entries':entries,'policy':'preflight absolute/traversal/backslash/duplicate/symlink/special-file/size; read every CRC; extract only below packet-extracted; no execution','lean_executed':False},indent=2)+'\n')
print('Frozen files:',len(files),'total bytes:',sum(x['bytes'] for x in snapshot.values()));print('Packet entries:',len(entries));print(json.dumps(entry,indent=2))
