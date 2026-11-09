import re,hashlib
exec((p/'read_sources.py').read_text().split('for name')[0])
text=(p/'376322-v1-clean.txt').read_text()
for left,right in [('Theorem 2 .','4 Optimized'),('4.2 Optimization','4.3 Construction'),('5 Concluding','References')]:
 i=text.index(left);j=text.index(right,i+len(left));print('V1',text[i:j])
text=(p/'376322-clean.txt').read_text();i=text.index('4.2 Optimization');print('V2 compatible definition',text[i:i+1200])
for key in ['openai-head','leanpool-head']:
 print(key,re.findall(r'"currentOid":"([a-f0-9]+)"',(p/(key+'.html')).read_text()))
for key in ['main-abs','companion-abs']:
 s=(p/(key+'.html')).read_text();print(key,re.findall(r'\[Submitted[^<]+|\[v[0-9]+\][\s\S]{0,180}|name="citation_[^"]+" content="[^"]+"',s))
for name in ['376322','376322-v1']:
 html=(a/'sources'/(name+'.html')).read_text();fig=re.search(r'<figure[^>]*id="S3.F4"[\s\S]*?</figure>',html).group()
 (p/(name+'-figure4.svg-source.txt')).write_text(fig)
 print(name,'FIG4 geometric paths',re.findall(r'<path[^>]*d="([^"]+)"',fig));print('FIG4 lines',re.findall(r'<line[^>]+>',fig));print('labels',re.findall(r'alttext="([^"]+)"',fig))
j=json.loads((a/'source-inventory.json').read_text());v=j['per_id'];print('INVENTORY TARGET',v.get('376322') if isinstance(v,dict) else [r for r in v if '376322' in str(r)])
j=json.loads((a/'registry-screen.json').read_text());print('REGISTRY NONPATH',json.dumps({k:v for k,v in j.items() if k!='leanpool_project_paths'},indent=2)[:4500])
allow=json.loads((p/'historical-results-allowlist.json').read_text());print('HISTORY type',type(allow).__name__)
files=allow if isinstance(allow,list) else []
hits=[]
for path in files:
 if 'crown-vnumber-' in path:continue
 q=pathlib.Path(path)
 if not q.is_file() or q.stat().st_size>2500000:continue
 s=q.read_text()
 matches=list(re.finditer(r'376322|dual.cube|compound.graph',s,re.I))
 if matches:hits.append(dict(path=path,sha256=hashlib.sha256(q.read_bytes()).hexdigest(),excerpts=[s[max(0,m.start()-120):m.start()+400] for m in matches[:8]]))
(p/'history-target-screen.json').write_text(json.dumps(hits,indent=2));print('HISTORY relevant',json.dumps(hits,indent=2)[:7000])
