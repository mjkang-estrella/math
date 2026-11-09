from pathlib import Path
import subprocess,json,datetime,re
R=Path(__file__).resolve().parents[1]
exclude=['**/.git/**','**/fresh-arithmetic-discovery-r103/**','**/*arithmetic*r104*/**','**/*analytic*r134*/**','**/*[tT]009[pP]102*/**','**/*[tT]088[pP]133*/**','**/discovery-analytic-r133-parent/**','**/fresh-structural-discovery-r140/**','**/preprints-tree.json','**/tree.json','**/CONTENTS.md','**/sources/preprints/**','**/upstream/preprints/**','**/node_modules/**','**/.lake/**']
pat=r'Plancherel|tensor.product.Markov|tensor.chain|cycle.profile|Feray|Féray|Teyssier|Moore.Russell'
args=['rg','--hidden','--no-ignore','-l','-i',pat,'frontier']
for e in exclude:args+=['-g','!'+e]
a=subprocess.run(args,capture_output=True);files=a.stdout.decode().splitlines();(R/'packet/private/search/operation-paths.txt').write_bytes(a.stdout)
# Omit known copied search-result/index bodies only from displayed snippets, not the search.
nav=re.compile(r'(?i)(search|catalog|manifest|inventory|hash|receipt|bindings|\bbrief|task|contents|web-result|decoded)')
out=[]
for f in files:
 if nav.search(Path(f).name) or any(x in Path(f).parts for x in ['search','payload','inputs','snapshots']):continue
 for n,l in enumerate(Path(f).read_text(errors='replace').splitlines(),1):
  if re.search(pat,l,re.I):out.append(dict(path=f,line=n,text=l[:1200]))
(R/'packet/private/search/operation-hits.json').write_text(json.dumps(out,indent=2)+'\n');(R/'packet/private/search/operation-query.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),argv=args,returncode=a.returncode,files=len(files),snippets=len(out),snippet_filter=str(nav.pattern),limits='Text search, hidden/ignored/JSON/large included without size cutoff; excluded corpus indexes named in argv. Display filter does not certify absence and did not exclude private/work from search.'),indent=2)+'\n')
print('matched files',len(files),'focused excerpts',len(out))
for x in out[:22]:print(x['path'],x['line'],x['text'][:280])
