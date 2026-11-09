from research import *
import re
pat=re.compile(r'Airy|Tracy.Widom|Miller.Paris|hypergeometric.*zero|Kuijlaars|shadows? of polynomial|Rodrigues|chromatic.*sphere|cardinal function|Cantor.*sum|planar achievement|Karp.*root',re.I)
out=[];seen=set()
for line in (L/'bindings.jsonl').read_text().splitlines():
 r=json.loads(line);p=pathlib.Path(r['original'])
 if p.name not in ['SUMMARY.md','SCOUTING.md','discovery.md','discovery.json'] or str(p) in seen:continue
 seen.add(str(p));q=pathlib.Path(r['copy']);s=q.read_text(errors='replace');matches=[]
 for m in pat.finditer(s):matches.append(s[max(0,m.start()-180):m.end()+320])
 if matches:out.append({'path':str(p),'sha256':r['sha256'],'excerpts':matches[:8]})
save('additional-alias-hits.json',out);print(json.dumps(out,indent=2)[:27000])
