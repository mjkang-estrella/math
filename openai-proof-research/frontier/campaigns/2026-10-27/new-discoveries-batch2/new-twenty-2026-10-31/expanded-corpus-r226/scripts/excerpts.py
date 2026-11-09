from pathlib import Path
import json,re
L=Path(__file__).resolve().parents[1];out=[]
for p in sorted((L/'receipts').glob('2026*.json')):
 r=json.loads(p.read_text());u=r['url'];tp=L/'inputs'/(Path(r['body']).stem+'.txt')
 if '/html/' not in u or r.get('status')!=200 or not tp.exists():continue
 t=tp.read_text(); excerpts=[]
 for m in re.finditer(r'Conjecture\s+\d|Theorem 1\.[1234]\s|Figure\s+\d|Example\s+\d|verified|computer|experimental',t,re.I):
  excerpts.append(t[max(0,m.start()-80):m.start()+1300])
 out.append({'url':u,'receipt':p.name,'excerpts':excerpts})
(L/'inputs/source-excerpts.json').write_text(json.dumps(out,indent=2)+'\n')
for r in out:
 if any(s in r['url'] for s in ['2405.04915v4','2406.13176v2','2406.10192v2','2404.15645v1']):
  print(r['url']);print('\n'.join(r['excerpts'][:6]))
