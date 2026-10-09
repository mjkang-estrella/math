"""Fresh immutable inputs; writes only within the assigned audit source directory."""
from pathlib import Path
import concurrent.futures, hashlib, json, urllib.request

ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / 'frontier/sources/i10_complex_modes_r2'
PIN = json.loads((ROOT / 'sources/upstream.json').read_text())['commit']
TREE = json.loads((ROOT / 'sources/preprints-tree.json').read_text())
assert PIN == 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb' and not TREE['truncated']
BLOBS = {e['path']: e['sha'] for e in TREE['tree'] if e['type'] == 'blob'}
OLD = json.loads((ROOT / 'frontier/sources/i10_complex_modes/retrieval-manifest.json').read_text())['files']
PATHS = [r['path'] for r in OLD]
D = 'preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/sections/'
PATHS += [D + n for n in ['04-memory.tex', '05-major-arcs.tex', '08-poisson-dirichlet.tex']]

def fetch(path):
    url = f'https://raw.githubusercontent.com/openai/math/{PIN}/{path}'
    data = urllib.request.urlopen(url, timeout=60).read()
    blob = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    assert blob == BLOBS[path], path
    target = OUT / 'pinned' / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
    return dict(path=path, url=url, local=str(target.relative_to(ROOT)), bytes=len(data),
                sha256=hashlib.sha256(data).hexdigest(), git_blob=blob, tree_match=True)

def main():
    with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool:
        records = list(pool.map(fetch, PATHS))
    (OUT/'retrieval-manifest.json').write_text(json.dumps(dict(pin=PIN, files=records), indent=2)+'\n')
    literature=[]
    for old in json.loads((ROOT/'frontier/sources/i10_complex_modes/literature-manifest.json').read_text()):
        src=ROOT/old['local']
        if src.suffix == '.pdf':
            data=urllib.request.urlopen(old['primary_url'], timeout=60).read()
            assert data.startswith(b'%PDF')
        else:
            data=src.read_bytes()
        target=OUT/'literature'/src.name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        literature.append(dict(local=str(target.relative_to(ROOT)), url=old['primary_url'],
            sha256=hashlib.sha256(data).hexdigest(), bytes=len(data),
            fresh_download=src.suffix=='.pdf', matches_author=hashlib.sha256(data).hexdigest()==old['sha256']))
    (OUT/'literature-manifest.json').write_text(json.dumps(literature,indent=2)+'\n')
    print(json.dumps(dict(pinned_files=len(records), all_blobs_match=True, literature=literature),indent=2))

if __name__ == '__main__':
    main()
