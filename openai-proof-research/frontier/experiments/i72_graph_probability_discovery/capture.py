from pathlib import Path
import hashlib,json,subprocess,datetime,shutil,re
R=Path.cwd(); S=R/'frontier/sources/i72_graph_probability_discovery'; C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
def sha(b):return hashlib.sha256(b).hexdigest()
def write(n,x):(S/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
ledger=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
refs=['AGENTS.md','sources/upstream.json','sources/preprints-tree.json','sources/CONTENTS.md']+[f'frontier/iterations/{n}' for n in ['i13-fresh-discovery.md','i19-fresh-structural-discovery.md','i22-combinatorial-discovery.md','i26-probability-discovery-resumed.md','i39-quantum-spectral-discovery.md','i71-global-variation-algebra-rounding.md']]+[str(p.relative_to(R)) for p in (R/'frontier/findings').glob('R0*.md')]
records=[]
for n in ledger+refs:
 p=R/n
 if not p.exists():continue
 b=p.read_bytes(); row={'path':n,'sha256':sha(b),'bytes':len(b),'mutable':n in ledger}
 if n in ledger:
  dest=S/'ledgers'/n;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b);row['snapshot']=str(dest.relative_to(R))
 records.append(row)
write('inputs.json',{'captured_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'references':records})
tree=json.loads((R/'sources/preprints-tree.json').read_text()); blobs={e['path']:e for e in tree['tree'] if e['type']=='blob'}
files=sorted(subprocess.check_output(['rg','--files','--no-ignore',str(C)],text=True).splitlines()); domain=[]; selected=[]
prefixes=['GOE-bulk-universality','Fixed-energy-universality-for-weak','No-percolation-at-criticality','Nonuniqueness-of-percolation','Polynomial-Mixing-of-the-Switch','A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect']
for raw in files:
 p=Path(raw); rel=str(p.relative_to(C));b=p.read_bytes(); git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert git==blobs[rel]['sha']
 row={'path':rel,'sha256':sha(b),'git_blob':git,'bytes':len(b)};domain.append(row)
 if any(rel.split('/')[1].startswith(q) for q in prefixes):
  dest=S/'pinned'/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
  selected.append(dict(row,raw_url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+rel))
write('corpus-domain.json',{'root':str(C.relative_to(R)),'files':domain})
write('pinned-manifest.json',selected)
write('inventory.json',{'entries':len(tree['tree']),'manuscripts':len({e['path'].split('/')[1] for e in tree['tree']}),'blobs':len(blobs),'fixed_corpus':len(domain),'other_blobs':[e for p,e in sorted(blobs.items()) if p not in {r['path'] for r in domain}]})
patterns={'broad':r'(?i)(girth|short.cycles|inhomogeneous.percolation|weighted.switch|condition.{0,30}regular.graph)', 'spectral':r'(?i)(rare.event|condition.{0,25}girth|cycle.{0,25}universality|switch.{0,25}invarian)', 'mechanisms':r'(?i)(sprinkling|binary.{0,12}activit|weighted.{0,12}projection|relative.entropy)'}
search=[]
for label,pat in patterns.items():
 rx=re.compile(pat);hits=[]
 for row in domain:
  for i,line in enumerate((C/row['path']).read_text(errors='replace').splitlines(),1):
   if rx.search(line):hits.append([row['path'],i,line])
 search.append({'label':label,'pattern':pat,'engine':'Python re; each matching line retained once; list multiplicity retained','hits':hits})
write('searches.json',search)
write('capture.json',{'time':datetime.datetime.now(datetime.timezone.utc).isoformat(),'command':'python frontier/experiments/i72_graph_probability_discovery/capture.py','selected_files':len(selected),'corpus_files':len(domain),'search_counts':{s['label']:len(s['hits']) for s in search}})
print((S/'capture.json').read_text())
