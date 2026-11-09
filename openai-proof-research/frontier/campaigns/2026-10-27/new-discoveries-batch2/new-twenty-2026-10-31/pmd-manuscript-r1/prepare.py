from pathlib import Path
import shutil,json,hashlib,tarfile
O=Path.cwd(); B=O.parent; D=B/'expanded-corpus-r143'; R=B/'pmd-review-r1'
for folder in ['evidence/discovery','evidence/review','evidence/root','certificates','raw','qa','scripts']:Path(folder).mkdir(parents=True,exist_ok=True)
def copy(p,q):
 q=Path(q);q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
for name in ['SUMMARY.md','PROOF.md','TorusPMD.lean','Audit.lean','AuditAll.lean']:copy(D/name,'evidence/discovery/'+name)
copy(D/'lean-packet.tar.gz','lean-packet.tar.gz')
copy(D/'raw/366974.jsonl','raw/366974.jsonl')
entry=json.loads((D/'results.json').read_text())['366974'];Path('evidence/discovery/results-366974.json').write_text(json.dumps(entry,indent=2)+'\n')
for name in ['pmd-certificate.json','pmd-signs.json','http.json','prior-http.json','extra-http.json']:copy(D/'outputs'/name,'evidence/discovery/outputs/'+name)
for name in ['2502.02826.pdf','2502.02826.txt','2502.02826-abs.html','2110.12168.pdf','2110.12168.txt']:copy(D/'sources'/name,'evidence/discovery/sources/'+name)
for name in ['REVIEW.md','review.json']:copy(R/name,'evidence/review/'+name)
for name in ['downloads','logs','scripts']:
 shutil.copytree(R/name,Path('evidence/review')/name,dirs_exist_ok=True)
for n in [5,6,7]:copy(R/f'logs/independent-search-3-{n}.json',f'certificates/3-{n}.json')
P=B/'pmd-parent-final-r1'
for name in ['replay-result.json','registry-refresh.json']:copy(P/name,'evidence/root/'+name)
for name in ['logs','registries','rootcheck']:shutil.copytree(P/name,Path('evidence/root')/name,dirs_exist_ok=True)
copy(B/'pmd-root-ruling-r1.json','evidence/root/ruling.json')
with tarfile.open('lean-packet.tar.gz','r:gz') as tar:
 members=tar.getmembers()
 for m in members:
  p=Path(m.name)
  assert not p.is_absolute() and '..' not in p.parts and (m.isfile() or m.isdir()),m.name
 target=Path('safe-extracted');target.mkdir()
 tar.extractall(target,filter='data')
lean=list(target.rglob('TorusPMD.lean'));assert len(lean)==1
assert lean[0].read_bytes()==(D/'TorusPMD.lean').read_bytes()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha('lean-packet.tar.gz')=='f8e94288a8ab8a1ec5a8c41c1da1795e9bade7a06c44080aef9b883ab210c2de'
Path('receipts/safe-extraction.json').write_text(json.dumps(dict(status='PASS',members=[m.name for m in members],policy='relative regular files/directories only; reject parent traversal and all links/devices; filter=data',lean_sha256=sha(lean[0]),packet_sha256=sha('lean-packet.tar.gz'),executed_lean=False),indent=2)+'\n')
Path('raw/366974.sha256').write_text(sha('raw/366974.jsonl')+'  366974.jsonl\n')
print('Copied evidence; safe extraction passed; no Lean invoked.')
