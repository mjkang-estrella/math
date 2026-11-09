from pathlib import Path
import re,json
b=Path(__file__).resolve().parent;rows=json.loads((b/'independent-math.json').read_text())['trees'];checked=[]
for row in rows:
 tag=''.join(map(str,row['counts']));s=(b/f'fresh/formal/EvalR3_{tag}.lean').read_text()
 masks=set(map(int,re.search(r'theorem best_\d+.*?= \{([\d,]+)\}',s).group(1).split(',')))
 own={sum(1<<v for v in vs) for vs in row['maxima']}
 assert masks==own,(tag,masks,own)
 totals=[sum(sum(1 for v in vs if (0 if v<2 else 1 if v<6 else 2)==i) for vs in row['maxima']) for i in range(3)]
 decl=re.search(r'theorem totals_.*? := by',s,re.S).group(0)
 assert list(map(int,re.findall(r'⟩ [012] = (\d+)',decl)))==totals
 checked.append({'tag':tag,'mask_count':len(masks),'totals':totals})
(b/'certificate-crosscheck.json').write_text(json.dumps({'passed':True,'forms':checked},indent=2));print('All 81 Lean claimed mask sets and layer totals agree independently')
