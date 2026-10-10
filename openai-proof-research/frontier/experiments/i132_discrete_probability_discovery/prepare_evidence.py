"""Acquisition/preparation only. Does not seal; offline verifier never invokes this."""
import json,re,hashlib,pathlib,subprocess
S=pathlib.Path('frontier/sources/i132_discrete_probability_discovery');X=pathlib.Path('frontier/experiments/i132_discrete_probability_discovery')
def sha(b):return hashlib.sha256(b).hexdigest()
def row(p):
 p=pathlib.Path(p);b=p.read_bytes();return dict(path=str(p),sha256=sha(b),bytes=len(b))
def save(name,x): (S/name).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
# Historical search results are superseded by this broader, fixed, frozen-ledger domain.
files=[]
for folder in ['frontier/iterations','frontier/reviews','frontier/findings','proposals','reviews']:
 for p in pathlib.Path(folder).glob('*.md'):
  iteration=re.search(r'(?:^|/)i(\d+)[-_]',str(p))
  if iteration and int(iteration.group(1))>=130:continue
  if str(p) in ['frontier/iterations/README.md']:p=S/'snapshots'/p
  files.append(str(p))
files=sorted(set(files));pat=r'Thorp|random.{0,8}(?:[k3]-?SAT|satisfiab)|symmetric.{0,35}(?:sign|Bernoulli|singular)|(?:rank|corank).{0,8}deficien|Carenini|hitting.time|partial.permutation'
save('overlap-query.json',dict(files=files,pattern=pat,flags='IGNORECASE',convention='UTF-8 splitlines; zero-based character offsets, every occurrence in file/line/start order'))
def occurrences(files,pattern):
 out=[]
 for p in files:
  for n,line in enumerate(pathlib.Path(p).read_text().splitlines(),1):
   for m in re.finditer(pattern,line,re.I):out.append(dict(path=p,line=n,start=m.start(),end=m.end(),text=m.group(),line_text=line))
 return out
save('overlap-results.json',occurrences(files,pat))
# Selected manuscript lexical search retains all local source representations, including inherited PDF text.
domain=json.load(open('frontier/sources/i114_quantum_information_discovery/search-domain.json'))
selected=json.load(open(S/'selected-inventory.json'));fs=sorted(set(r['local'] for r in selected))
pat2=r'corank|compressib|singular|proportional|two.rows|hitting.time|variance|central.limit|Gaussian|conditional|retained|multiplicity|computab|Carenini'
save('source-query.json',dict(files=fs,pattern=pat2,flags='IGNORECASE',convention='UTF-8 splitlines; every match including repetitions and PDF/TeX repeats'))
save('source-results.json',occurrences(fs,pat2))
# All reads and lexical dependencies are immutable references unless already own files.
manifest=json.load(open(S/'read-manifest.json'))
bylocal={r['local']:r for r in domain}
for r in manifest:
 if r['local'] in bylocal:
  r['domain_path']=bylocal[r['local']]['path'];r['url']='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+r['domain_path']
save('read-manifest.json',manifest)
paths=set(files+fs+[r['local'] for r in manifest])
paths={p for p in paths if not p.startswith(str(S)+'/') and not p.startswith(str(X)+'/')}
save('additional-references.json',[row(p) for p in sorted(paths)])
engine=json.load(open('frontier/sources/i129_disordered_fk_occupation/engine-dependencies.json'))
for p in ['frontier/experiments/i129_disordered_fk_occupation/verify.py','frontier/experiments/i129_disordered_fk_occupation/check.py','frontier/sources/i129_disordered_fk_occupation/seal.json']:
 engine.append(row(p))
save('engine-dependencies.json',sorted(engine,key=lambda x:x['path']))
# Fresh PDF extraction is separately bound; replay checks both immutable byte streams without subprocesses.
p=S/'external/carenini.pdf';v=S/'external/carenini-pdf.txt'
r=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True,check=True)
assert r.stdout==v.read_bytes()
save('pdf-bindings.json',[dict(pdf=row(p),text=row(v),command=['pdftotext','-layout',str(p),'-'],exit_code=r.returncode,stderr=r.stderr.decode(),version=subprocess.run(['pdftotext','-v'],capture_output=True).stderr.decode(),convention='Poppler -layout bytes; form feeds retained; splitlines counts page breaks separately; immutable replay does not extract')])
print(json.dumps(dict(overlap_files=len(files),overlap_occurrences=len(json.load(open(S/'overlap-results.json'))),source_files=len(fs),source_occurrences=len(json.load(open(S/'source-results.json'))),reads=len(manifest))))
