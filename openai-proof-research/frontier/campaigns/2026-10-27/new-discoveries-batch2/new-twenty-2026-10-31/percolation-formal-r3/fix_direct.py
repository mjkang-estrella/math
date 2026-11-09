from pathlib import Path
import re
r=Path(__file__).resolve().parent
for p in (r/'packet/src').glob('Inputs*.lean'):
 lines=p.read_text().splitlines();out=[]
 for l in lines:
  if 'by simpa only' not in l:out.append(l);continue
  i=re.search(r'holds_decode v cl_(\d+)',l)[1]
  if 'input_omit' in l:
   a=re.search(r'input_omit (\d+) v h',l)[1];c=f'omitClause5 {a}';t=f'input_omit {a} v h'
  elif 'input_contain' in l:
   a,b=re.search(r'input_contain (\d+) (\d+)',l).groups();c=f'containClause5 {a} {b}';t=f'input_contain {a} {b} (by decide) v h'
  else:c='pts5.map (fun p => (SatVar.x p, true))';t='input_nonfull v h'
  out +=[f'  apply holds_decode v cl_{i}',f'  have he : decodeClause cl_{i} = {c} := by decide',f'  rw [he]',f'  exact {t}']
 p.write_text('\n'.join(out)+'\n')
(r/'retry-pilot-order.txt').write_text('\n'.join([f'Inputs{i:03d}' for i in range(43,48)]+['Pilot500','Pilot2000'])+'\n')
