import hashlib,json,sys,shutil,zipfile,stat
from pathlib import Path
R=Path(__file__).resolve().parent.parent; P=R.parent
paths=[]
for d in ['expanded-corpus-r240','hetyei-review-r1']:
 paths += [p for p in (P/d).rglob('*') if p.is_file()]
for name in ['source-only.zip','SUMMARY.md','PROOF.md','STATEMENT-CORRESPONDENCE.md','REPRODUCE.md','results.json','VALIDATION.txt','source-manifest.sha256']:
 paths.append(P/'hetyei-formal-r1'/name)
for d in ['src','provenance','receipts','logs']:
 paths += [p for p in (P/'hetyei-formal-r1'/d).rglob('*') if p.is_file()]
paths += [P/'hetyei-root-ruling-r1.json']
paths += [p for p in (P/'hetyei-parent-final-r1').rglob('*') if p.is_file() and 'replay/' not in str(p.relative_to(P/'hetyei-parent-final-r1'))]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
h={str(p.relative_to(P)):sha(p) for p in sorted(set(paths))}
mode=sys.argv[1]
(R/f'inputs-{mode}.json').write_text(json.dumps(h,indent=2)+'\n')
if mode=='after':
 assert h==json.loads((R/'inputs-before.json').read_text());print('Frozen inputs unchanged:',len(h));sys.exit()
# Preserve selected primary sources, discovery metadata, all reviewer evidence, formal texts, root receipts.
selected=[p for p in paths if ('hetyei-review-r1/' in str(p.relative_to(P))) or ('hetyei-formal-r1/' in str(p.relative_to(P))) or ('hetyei-parent-final-r1/' in str(p.relative_to(P))) or p.name=='hetyei-root-ruling-r1.json']
selected += [p for p in paths if str(p.relative_to(P)).startswith('expanded-corpus-r240/') and (p.name in ['CANDIDATE.md','SUMMARY.md','results.json','347230.jsonl','347231.jsonl','hetyei-certificates-v2.json'] or '/sources/' in str(p) or '/scripts/' in str(p))]
for p in sorted(set(selected)):
 dest=R/'evidence'/p.relative_to(P);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest)
packet=R/'evidence/hetyei-formal-r1/source-only.zip'
assert sha(packet)=='c96ee05e7799bca2aa7a35961e931185425ed44c8efd7160c73452d8a8d6054c'
shutil.copyfile(packet,R/'source-only.zip')
out=R/'packet-safe-extraction';out.mkdir(exist_ok=True)
with zipfile.ZipFile(packet) as z:
 for i in z.infolist():
  q=Path(i.filename)
  assert not q.is_absolute() and '..' not in q.parts and not stat.S_ISLNK(i.external_attr>>16)
  assert i.file_size<10000000
  dest=out/q
  if i.is_dir():dest.mkdir(parents=True,exist_ok=True)
  else:dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(z.read(i))
 members=[dict(name=i.filename,bytes=i.file_size,sha256=hashlib.sha256(z.read(i)).hexdigest()) for i in z.infolist() if not i.is_dir()]
(R/'receipts/safe-extraction.json').write_text(json.dumps(dict(packet_sha256=sha(packet),safe=True,executed=False,members=members),indent=2)+'\n')
print('Frozen files',len(h),'safe packet files',len(members))
