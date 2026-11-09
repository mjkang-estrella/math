exec(compile((__import__('pathlib').Path(__file__).resolve().parent/'research.py').read_text(),'research.py','exec'))
import re
if sys.argv[1]=='catalogue':
 sources=[L/'sources/current-openai-CONTENTS.md',L.parents[5]/'sources/CONTENTS.md']
 # actual local pinned path, no recursive history search
 sources[1]=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/CONTENTS.md')
 out={}
 for p in sources:
  if not p.exists():continue
  s=p.read_text();blocks=s.split('</td>');matches=[b.strip() for b in blocks if re.search(r'derangement|rainbow|Costas|Snevily|Nebbia|Thomass|packing property|list.avoiding|chromatic symmetric homology|planar graze',b,re.I)]
  out[str(p)]=matches
  for b in matches:print(p.name,b[:2200])
 js('registry-catalogue-matches.json',out)
 p=L/'sources/LeanPool-root.html'
 if p.exists():
  s=p.read_text();print('LEANPOOL HEAD',set(re.findall(r'currentOid[^a-f0-9]+([a-f0-9]{40})',s)));print('LEANPOOL PATHS',re.findall(r'"path":"([^"]+)"',s)[:60])
 receipt('catalogue')
elif sys.argv[1]=='convert':
 inv=[]
 for n in sys.argv[2:]:
  p=L/'sources'/n
  if not p.exists():continue
  q=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(q)],check=True,timeout=15)
  inv.append(dict(path=str(q),sha256=sha(q.read_bytes()),depth='converted only'))
 js('reads/converted-extra-'+sys.argv[2]+'.json',inv);receipt('convert-'+sys.argv[2],dict(children_reaped=True))
