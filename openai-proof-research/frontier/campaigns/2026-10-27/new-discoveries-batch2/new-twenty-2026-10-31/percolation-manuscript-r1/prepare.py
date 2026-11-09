from pathlib import Path, PurePosixPath
import hashlib,json,zipfile,stat,shutil,sys
D=Path(sys.argv[1]).resolve(); P=D.parent
assert D.name=='percolation-manuscript-r1'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def save(n,j): (D/n).write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
files=[]
for k in range(1,9):
 b=P/f'percolation-formal-r{k}'
 files += [b/n for n in ['SUMMARY.md','PROOF.md','STATEMENT-CORRESPONDENCE.md','REPRODUCE.md','results.json'] if (b/n).exists()]
b=P/'expanded-corpus-r164'
files += [b/n for n in ['CANDIDATE.md','SUMMARY.md','results.json']]
files += [f for sub in ['sources','raw'] for f in (b/sub).rglob('*') if f.is_file()]
files += [b/'outputs'/n for n in ['percolation.json','percolation-three-round.json','registry-screen.json','percolation-prior-search.json','http.jsonl']]
b=P/'percolation-review-r1'
files += [f for f in b.rglob('*') if f.is_file() and (f.suffix in ['.md','.json','.py'] or f.parent.name=='logs') and '.lean' not in f.name]
files += [P/f'percolation-root-ruling-r{k}.json' for k in [1,2]]
files += [P/'percolation-formal-r8'/n for n in ['source-only.zip','module-order.txt','normalized.cnf','normalized-trimmed.json','module-times.json','axioms.txt','metadata-audit.txt','source-scan.json','final-verification.json']]
files += [P/'percolation-parent-final-r1'/n for n in ['replay-result.json','registry-refresh.json'] if (P/'percolation-parent-final-r1'/n).exists()]
files=sorted(set(files)); save('inputs-before.json',{str(f):{'sha256':sha(f),'bytes':f.stat().st_size} for f in files})
# Curated byte-identical copies: no proof-module archive copied.
for f in files:
 rel=f.relative_to(P)
 if f.name=='source-only.zip' or 'sources' in rel.parts and not ('333709' in f.name):continue
 if f.stat().st_size>40000000:continue
 out=D/'evidence'/rel;out.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,out)
zp=P/'percolation-formal-r8/source-only.zip'; digest=sha(zp)
assert digest=='b2e78af5a5191a37f364f39a89272af5898ca6a7ecc59058a7661649837ea9fb'
# Extract to temporary lane-local tree, verify every archived manifest entry, remove tree.
out=D/'packet-safe-test';out.mkdir(exist_ok=False)
with zipfile.ZipFile(zp) as z:
 infos=z.infolist(); assert len({i.filename for i in infos})==len(infos)
 for i in infos:
  p=PurePosixPath(i.filename); mode=i.external_attr>>16
  assert not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename and not stat.S_ISLNK(mode)
  assert i.file_size<150000000 and sum(v.file_size for v in infos)<500000000
  dest=out.joinpath(*p.parts);dest.parent.mkdir(parents=True,exist_ok=True)
  if not i.is_dir():
   with z.open(i) as a,dest.open('wb') as b:shutil.copyfileobj(a,b,1048576)
 entries=[]
 for line in (out/'source-manifest.sha256').read_text().splitlines():
  h,n=line.split(maxsplit=1); n=n.lstrip('*'); assert sha(out/n)==h;entries.append(n)
 order=(out/'module-order.txt').read_text().splitlines();assert len(order)==830
 docs=D/'packet-documentation';docs.mkdir(exist_ok=True)
 for f in out.iterdir():
  if f.is_file() and (f.suffix=='.md' or f.name=='module-order.txt'):shutil.copyfile(f,docs/f.name)
 save('packet-reuse-receipt.json',dict(path=str(zp),sha256=digest,compressed_bytes=zp.stat().st_size,uncompressed_bytes=sum(i.file_size for i in infos),members=len(infos),manifest_entries_verified=len(entries),modules=len(order),safe_extraction=True,lean_executed=False,archive_copied=False,documentation_copied_only=True))
shutil.rmtree(out)
raw=D/'evidence/expanded-corpus-r164/raw/333709.jsonl';assert sha(raw)=='d09e36b9c04f157daae95abf265ea46b7158bc88f42a2129031a5cc83f9c8d71'
save('raw-line-receipt.json',dict(path=str(raw.relative_to(D)),sha256=sha(raw),bytes=raw.stat().st_size,trailing_newline=raw.read_bytes().endswith(b'\n')))
print('Frozen',len(files),'inputs; packet safely extracted, manifest verified, test tree removed.')
