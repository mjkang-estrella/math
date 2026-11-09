from pathlib import Path
import json
R=Path(__file__).resolve().parent
spec={'2053':[46],'2090':[24,25,63],'3385':[11,22],'3387':[66],'3400':[17],'3473':[22,26],'3475':[27,28],'4080':[66,67]}
out=[]
for n,pages in spec.items():
 t=(R/f'sources/{n}.txt').read_text().split('\f')
 for p in pages:
  o={'file':f'sources/{n}.txt','physical_page':p,'excerpt':t[p-1]};out.append(o);print('\n###',n,p,'\n'+t[p-1])
(R/'extra-excerpts.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
