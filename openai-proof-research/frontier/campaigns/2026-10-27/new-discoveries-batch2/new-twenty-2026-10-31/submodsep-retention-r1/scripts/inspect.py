from pathlib import Path
B=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/submodsep-retention-r1')
for name,term in [('thesis','submodular'),('thesis','based on'),('matroid','[6]'),('advances','submodular'),('tu','CCSM'),('cnf','posed in [2]'),('eccc','Conjecture 3.33.')]:
 for i,p in enumerate((B/(name+'.txt')).read_text().split('\f'),1):
  if term in p:
   print('\nSOURCE',name,'PDF PAGE',i,'TERM',term,'FOOTER',repr(p[-100:]))
   lines=p.splitlines()
   for k,line in enumerate(lines):
    if term in line: print('\n'.join(lines[max(0,k-2):k+8]))
