from pathlib import Path
import re,json
D=Path(__file__).resolve().parents[1];x=json.load(open(D/'extracted.json'));terms=['uber','ferrers','antimagic','general-position','terminal-set','parking','chomp','interlac','tough','cofactor','difference-set','matroid','divisible','hyperelliptic','schrod','schrö','strict-partition','shuffle','rainbow','geodetic']
r={}
for p in (D/'sources').glob('*.json'):
 if p.name not in ['omega-D5.json','omega-Problems.json','openai-preprints.json']:continue
 o=json.loads(p.read_text());assert not o.get('truncated');r[p.name]={'truncated':o.get('truncated'), 'hits':[e['path'] for e in o['tree'] if any(t in e['path'].lower() for t in terms)]}
(D/'outputs/registry-screen.json').write_text(json.dumps(r,indent=2)+'\n')
for p in (D/'sources').glob('*.txt'):
 lines=p.read_text().splitlines(); ix=set()
 for i,l in enumerate(lines):
  if re.search('conjecture|verified|checked|confirmed',l,re.I): ix.update(range(max(0,i-4),min(len(lines),i+16)))
 (D/'outputs'/('screen-'+p.name)).write_text('\n'.join(f'{i+1}: {lines[i]}' for i in sorted(ix))+'\n')
