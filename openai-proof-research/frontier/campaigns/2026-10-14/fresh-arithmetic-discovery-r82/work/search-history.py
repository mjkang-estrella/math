from pathlib import Path
import subprocess,re,json
base=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r82')
files=subprocess.check_output(['rg','--files','frontier/campaigns','frontier/iterations','frontier/experiments'],text=True).splitlines()
patterns={
 'intersection':r'Serre.{0,30}(positivity|intersection)|source.?193|screen.?193|tangent.cone|Rees.algebra|intersection.multiplicity',
 'lech':r'Lech|source.?194|screen.?194|multiplicity.*flat|flat.*multiplicity',
 'weights':r'Alperin|source.?202|screen.?202|Galois.*weight|weight.*bijection',
 'donovan':r'Donovan|source.?203|screen.?203|Frobenius.Morita|Morita.Frobenius|bounded.defect',
 'virasoro':r'Virasoro|source.?065|screen.?065|relative.cap|master.space|blow.up.*constraint',
 'roots':r'half.weight|root.orbifold|source.?057|screen.?057|orbifold.*abelian|abelian.*orbifold|inertia.*special'
}
res={k:[] for k in patterns}
exclude={'private','inputs','snapshots','frozen','payload','dependencies','upstream','context','node_modules','.git'}
for f in files:
 p=Path(f)
 if str(base) in f or p.suffix not in {'.md','.txt','.tex'} or set(p.parts)&exclude:continue
 try:s=p.read_text()
 except (UnicodeError,OSError):continue
 for key,pat in patterns.items():
  hits=[{'line':i,'text':line[:1300]} for i,line in enumerate(s.splitlines(),1) if re.search(pat,line,re.I)]
  if hits:res[key].append({'file':f,'size':p.stat().st_size,'hits':hits})
(base/'packet/private/history-search.json').write_text(json.dumps(res,indent=2)+'\n')
for key,items in res.items():
 print('\nFAMILY',key,'files',len(items))
 for it in items:
  if re.search(r'(fresh-arithmetic-discovery-r\d+/(packet/public/)?(screen|research|checkpoint|candidate|report)|iterations/I|experiments/)',it['file'],re.I):print(it['file'],it['size'],[(h['line'],h['text'][:180]) for h in it['hits'][:2]])
