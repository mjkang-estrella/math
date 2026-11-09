exec((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text().split('urls=json.loads')[0])
import re
patterns=r'319291|319346|319348|319360|339277|316980|317342|317350|317478|317479|317480|317512|317604|317646|317666|317722|317724|317864|317985|318040|Snevily|Raff|Thi.ry|whist|projection.cone|tight.neighbor|longest.increasing|circuit.relation|graph.invariant|Brualdi|Freiman'
matches=[]
for f in (l/'sources').glob('*'):
 if f.suffix=='.json' or f.name.endswith('-pdf') or f.name.endswith('-abs'):continue
 if f.name.endswith('-head') or f.name.endswith('-commit') or f.name=='pool-candidates':continue
 if not f.name.startswith(('openai-','omega-','aim-','pool-')):continue
 for n,line in enumerate(f.read_text(errors='replace').splitlines(),1):
  if re.search(patterns,line,re.I):matches.append({'file':str(f.relative_to(l)),'line':n,'text':line})
(l/'registry-matches.json').write_text(json.dumps(matches,indent=2));print(json.dumps(matches,indent=2)[:22000])
heads=json.loads((l/'registry-heads.json').read_text())
for name,o in heads.items():
 s=(l/'sources'/(name+'-commit')).read_text();o['observed_dates']=sorted(set(re.findall(r'\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d[^"< ]*',s)))[:8];o['readscope']='Current landing page and commit chronology, plus targeted term screen of immutable-at-head catalogue/root imports/projects. Routing only; no absence-based novelty clearance.'
(l/'registry-heads.json').write_text(json.dumps(heads,indent=2));print(heads)
