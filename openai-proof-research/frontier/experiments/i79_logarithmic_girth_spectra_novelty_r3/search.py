import pathlib,json,re,subprocess,collections,hashlib
R=pathlib.Path(__file__).resolve().parents[3];S=R/'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3';C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
patterns={'ensembles':r'(?i)locally[ -]tree[ -]like|permutation[ -]invariant|high[ -]girth|large[ -]girth|girth.{0,35}(condition|log)|condition.{0,35}girth', 'spectral':r'(?i)(universality|GOE|Gaussian.wave|Gaussian orthogonal).{0,80}(regular|graph|tree|ensemble)|(regular|graph|tree|ensemble).{0,80}(universality|GOE|Gaussian.wave)', 'conditioning':r'(?i)(entropy|resampl|involution|rejection|spectral).{0,50}(condition|absorb|rare)|(condition|absorb|rare).{0,50}(entropy|resampl|involution|rejection|spectral)'}
paths=sorted(subprocess.check_output(['rg','--files','--no-ignore',str(C)],text=True).splitlines())
rows=[json.loads(l) for l in (S/'outside-requests.jsonl').read_text().splitlines()]
assert len(paths)==9340 and len(rows)==1033
print('outside failures',[(x['path'],x.get('error')) for x in rows if 'error' in x]);print('blob mismatches',sum(not x.get('git_match',False) for x in rows))
dom=[]
for p in paths:dom.append((str(pathlib.Path(p).relative_to(C)),pathlib.Path(p),'corpus'))
for x in rows:
 if 'error' in x:continue
 p=R/x.get('extraction',{}).get('path',x['local']);dom.append((x['path'],p,'outside_pdf' if 'extraction' in x else 'outside_bytes'))
result=[]
for label,pattern in patterns.items():
 rx=re.compile(pattern);hits=[]
 for original,p,kind in dom:
  for i,line in enumerate(p.read_bytes().decode('utf-8',errors='replace').splitlines(),1):
   if rx.search(line):hits.append([original,i,line,kind])
 result.append(dict(label=label,pattern=pattern,hits=hits))
 print(label,len(hits));print(collections.Counter(h[0].split('/')[1] for h in hits).most_common(15))
(S/'searches.json').write_text(json.dumps(result,indent=2,ensure_ascii=False))
(S/'search-domain.json').write_text(json.dumps([{'path':a,'local':str(p.relative_to(R)),'kind':k,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for a,p,k in dom],indent=2))
