from pathlib import Path
import json, re, hashlib
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'frontier/sources/i20_pde_kinetic_discovery'
inventory=json.loads((OUT/'inputs/sources/preprints-tree.json').read_text())
assert not inventory.get('truncated',False)
rows=inventory['tree']; blobs={r['path']:r['sha'] for r in rows if r['type']=='blob'}
man=json.loads((OUT/'pinned-manifest.json').read_text())
for r in man['files']:assert blobs[r['path']]==r['git_blob']
names=sorted({r['path'].split('/')[1] for r in rows if r['path'].startswith('preprints/') and len(r['path'].split('/'))>1})
matches=[n for n in names if any(w in n.lower() for w in ['boltz','schrodinger','navier-stokes','forced-viscous','fluid-computation','box-transport','critical-local-smoothing'])]
(OUT/'inventory-screen.json').write_text(json.dumps({'entries':len(rows),'blob_count':len(blobs),'manuscripts':len(names),'truncated':inventory.get('truncated',False),'title_query_terms':['boltz','schrodinger','navier-stokes','forced-viscous','fluid-computation','box-transport','critical-local-smoothing'],'matches':matches,'scope':'Full metadata scan; selected source copying is not a claim of reading every file.'},indent=2)+'\n')
contracts=[]
for r in man['files']:
 if not r['path'].endswith('.tex'):continue
 text=(OUT/'corpus'/r['path']).read_text()
 for m in re.finditer(r'\\begin\{(theorem|maintheorem|proposition|lemma|assumption|definition|corollary|maincorollary)\}[\s\S]*?\\end\{\1\}',text):
  labels=re.findall(r'\\label\{([^}]+)\}',m.group())
  if labels:contracts.append({'path':r['path'],'url':r['url'],'git_blob':r['git_blob'],'sha256':r['sha256'],'start_line':text[:m.start()].count('\n')+1,'end_line':text[:m.end()].count('\n')+1,'labels':labels,'text':m.group()})
(OUT/'statement-contracts.json').write_text(json.dumps({'note':'Exact statement extraction; reading locators identify the passages actually relied on. No source proof audit.', 'contracts':contracts},indent=2)+'\n')
want={
 'Hard-sphere-fluctuations':{'01-introduction.tex':['ass:kinetic','thm:main','eq:grand-canonical'],'02-initial-target.tex':['prop:initial','eq:initial-insertion','eq:initial-centering-shift'],'06-sharp-asymptotics.tex':['thm:sharp-cumulants','lem:sharp-merger-coordinates','lem:sharp-summability'],'08-transfer.tex':['lem:center-transfer']},
 'The-Boltzmann-Grad':{'00-introduction.tex':['thm:main','cor:empirical'],'01-preliminaries.tex':['pre:potential','pre:duration','pre:collision','pre:scattering'],'06-closure.tex':['close:summability','close:tails']},
 'Nonuniqueness-with-local-conservation':{'01-introduction.tex':['def:admissible','thm:main'],'02-framework.tex':['eq:weight','eq:cutoff'],'04-construction.tex':['con:scales','con:jet-datum','con:seed','con:datum','con:finite-evolution'],'06-early.tex':['early:exponents','early:cap-selection'],'09-dilation.tex':['prop:blowup-limit'],'12-separation.tex':['sep:dormant-vanishing','sep:diagonal']},
 'Nonuniqueness-for-the-periodic':{'01-introduction.tex':['thm:main']},
 'Stable-Self-Similar':{'main.tex':['thm:blowup','cor:gaussian']},
 'Endpoint-pointwise':{'introduction.tex':['m:main']},
 'Universal-Computation':{'main.tex':['thm:main']}}
loc=[]
for r in man['files']:
 for prefix,files in want.items():
  if not r['path'].split('/')[1].startswith(prefix):continue
  labels=files.get(Path(r['path']).name,[])
  if not labels:continue
  lines=(OUT/'corpus'/r['path']).read_text().splitlines()
  for label in labels:
   idx=[i for i,l in enumerate(lines) if '\\label{'+label+'}' in l]
   assert len(idx)==1,(r['path'],label,idx)
   i=idx[0];a=max(0,i-5);b=min(len(lines),i+31)
   loc.append({'path':r['path'],'url':r['url'],'git_blob':r['git_blob'],'label':label,'line':i+1,'excerpt_start':a+1,'excerpt_end':b,'excerpt':'\n'.join(lines[a:b])})
(OUT/'reading-locators.json').write_text(json.dumps(loc,indent=2)+'\n')
print('inventory',len(names),'manuscripts;',len(man['files']),'pinned files;',len(contracts),'exact statements;',len(loc),'reading locators')
