import pathlib,json,hashlib,urllib.request,datetime
R=pathlib.Path(__file__).resolve().parent;root=R.parents[3]; T=json.loads((root/'sources/preprints-tree.json').read_text())['tree'];pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
spec={'129':('An-exponential-two-way-deterministic-state-lower-bound',{'introduction.tex','machines.tex','rank.tex','separation.tex','references.bib'}),'129c':('An-exponential-state-lower-bound-for-two-way-nondeterministic-complementation',{'introduction.tex','machines.tex','main.tex','references.bib'}),'113c':('A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General',{'introduction.tex','main.tex','references.bib'})}
receipts=json.loads((R/'packet/private/upstream-receipts.json').read_text()); entries=json.loads((R/'packet/private/selected-tree.json').read_text())
for f,(key,names) in spec.items():
 for e in T:
  p=e['path']
  if key not in p or pathlib.PurePosixPath(p).name not in names:continue
  u=f'https://raw.githubusercontent.com/openai/math/{pin}/{p}';b=urllib.request.urlopen(u,timeout=45).read();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert blob==e['sha'];dest=R/'packet/private/upstream'/f/p.split('/build/')[1];dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
  receipts.append(dict(family=f,path=p,raw_url=u,git_blob=blob,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),local=str(dest.relative_to(R/'packet')),acquisition='fresh pinned HTTP',utc=datetime.datetime.now(datetime.timezone.utc).isoformat()));entries.append(e); print(f,p.split('/build/')[1],len(b))
(R/'packet/private/upstream-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n');(R/'packet/private/selected-tree.json').write_text(json.dumps(entries,indent=2)+'\n')
