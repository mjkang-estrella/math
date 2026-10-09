"""Pinned corpus retrieval and complete-inventory screening; stdlib only."""
import concurrent.futures, datetime, hashlib, json, re, urllib.request
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / 'frontier/sources/i08_variable_capacity_novelty_r3'
OUT.mkdir(parents=True, exist_ok=True)
PIN = json.loads((ROOT/'sources/upstream.json').read_text())['commit']
inventory = json.loads((ROOT/'sources/preprints-tree.json').read_text())
assert inventory['truncated'] is False
entries = inventory['tree']
families = ['A-Capacity-Criterion-for-Four-State', 'The-Reconstruction-Threshold-for-the-Ferromagnetic-Four-State', 'The-exact-reconstruction-threshold-for-the-three-state', 'The-sharp-factor-of-IID-threshold-for-the-free-Ising']
inputs = ['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/TEN-FINDINGS.md','frontier/iterations/i08-variable-channel-capacity.md','frontier/reviews/i08-variable-capacity-r2.md']
def digest(b): return hashlib.sha256(b).hexdigest()
input_manifest=[]
for p in inputs:
    b=(ROOT/p).read_bytes()
    input_manifest.append(dict(path=p, bytes=len(b), sha256=digest(b)))
    if p.endswith('i08-variable-channel-capacity.md'): (OUT/'candidate-input.md').write_bytes(b)
    if p.endswith('i08-variable-capacity-r2.md'): (OUT/'proof-review-input.md').write_bytes(b)
roots=[x['path'] for x in entries if x['type']=='tree' and x['path'].count('/')==1]
rx=r'potts|ising|reconstruct|broadcast|capacit|tree|entropy|information|channel'
screen=dict(inventory_sha=inventory['sha'], truncated=False, total_entries=len(entries), manuscript_directories=len(roots), all_manuscript_directories=roots, screening_pattern=rx, matched_directories=[p for p in roots if re.search(rx,p,re.I)], selected_prefixes=families)
(OUT/'inventory-screen.json').write_text(json.dumps(screen,indent=2)+'\n')
selected=[x for x in entries if x['type']=='blob' and any(f in x['path'] for f in families) and '/verification/' not in x['path'] and x['path'].endswith(('.tex','.bib','.md'))]
def get(x):
    p=x['path']; url=f'https://raw.githubusercontent.com/openai/math/{PIN}/{p}'
    with urllib.request.urlopen(url,timeout=60) as r: b=r.read()
    blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    assert blob==x['sha'],p
    dest=OUT/'pinned'/p; dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
    return dict(path=p,url=url,local=str(dest.relative_to(ROOT)),bytes=len(b),sha256=digest(b),git_blob=blob,inventory_git_blob=x['sha'],matches=True)
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool: sources=list(pool.map(get,selected))
manifest=dict(retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),pin=PIN,inputs=input_manifest,sources=sources)
(OUT/'input-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(inputs=len(inputs),sources=len(sources),all_git_blobs_match=True,inventory_entries=len(entries),manuscript_directories=len(roots))))
