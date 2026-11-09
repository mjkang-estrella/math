import urllib.request, urllib.error, json, hashlib, datetime, concurrent.futures
from pathlib import Path
r=Path(__file__).parent
urls={'registry-openai-0': 'https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/preprints/Conditional-information-under-deterministic-coordinate-sweeps-September-26-2026/build/sections/10-palettes.tex', 'registry-openai-1': 'https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/preprints/From-partial-permutation-information-to-Fourier-bounds-September-26-2026/build/sections/palettes.tex', 'registry-openai-2': 'https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-Euclidean-plane-is-not-five-colorable-September-23-2026/build/sections/palettes.tex', 'registry-openai-3': 'https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-Margulis-Platonov-conjecture-over-global-function-fields-October-5-2026/build/paper/06-palettes.tex', 'registry-openai-4': 'https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-Margulis-Platonov-conjecture-over-number-fields-September-23-2026/build/sections/palettes.tex', 'registry-omega-two-colours': 'https://raw.githubusercontent.com/the-omega-institute/trureturing/759ea620b15c60a4f0c74e6b55227446439a74cd/D5/S3/Combinatorics/Graph/EdgeColouring/TwoColours.lean'}
def get(pair):
 name,url=pair;d={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical-source-review/1.0'}),timeout=25) as q: b=q.read();d.update(status=q.status,final_url=q.url)
 except urllib.error.HTTPError as e:b=e.read();d.update(status=e.code,final_url=e.url)
 except Exception as e:b=b'';d.update(error=repr(e))
 (r/(name+'.body')).write_bytes(b);d.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(r/(name+'.receipt.json')).write_text(json.dumps(d,indent=2));return name,d
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 for name,d in pool.map(get,urls.items()):print(name,json.dumps(d))
