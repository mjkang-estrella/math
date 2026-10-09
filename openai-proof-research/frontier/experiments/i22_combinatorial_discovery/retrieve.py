"""Retrieve versioned primary evidence, without changing shared caches."""
from pathlib import Path
import concurrent.futures, datetime, hashlib, json, subprocess, urllib.request

ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / 'frontier/sources/i22_combinatorial_discovery/literature'
PAPERS = {
    'iff-sfm': 'math/0004089v1',
    'dvorak-yepremyan': '2307.15048v1',
    'kaniewski-lee-dewolf': '1411.7280v1',
    'strong-secretary': '2609.19118v1',
    'sample-ocrs': '2507.09507v1',
    'sample-prophet': '2406.12799v1',
}

def fetch(item):
    name, version = item
    rows = []
    for kind, ext in [('abs', 'html'), ('pdf', 'pdf')]:
        url = f'https://arxiv.org/{kind}/{version}'
        req = urllib.request.Request(url, headers={'User-Agent': 'Research evidence archive/1.0'})
        with urllib.request.urlopen(req, timeout=45) as response:
            data = response.read()
            final_url = response.url
        path = OUT / f'{name}.{ext}'
        path.write_bytes(data)
        rows.append({'name': name, 'version': version, 'url': url, 'final_url': final_url,
                     'path': str(path.relative_to(ROOT)), 'bytes': len(data),
                     'sha256': hashlib.sha256(data).hexdigest(),
                     'retrieved_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()})
    subprocess.run(['pdftotext', '-layout', str(OUT/f'{name}.pdf'), str(OUT/f'{name}.txt')], check=True)
    p = OUT/f'{name}.txt'
    rows.append({'name': name, 'derived_from': str((OUT/f'{name}.pdf').relative_to(ROOT)),
                 'path': str(p.relative_to(ROOT)), 'sha256': hashlib.sha256(p.read_bytes()).hexdigest(),
                 'bytes': p.stat().st_size})
    return rows

if __name__ == '__main__':
    OUT.mkdir(parents=True, exist_ok=True)
    rows = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        for result in pool.map(fetch, PAPERS.items()):
            rows.extend(result)
    (OUT/'manifest.json').write_text(json.dumps(rows, indent=2)+'\n')
    print(json.dumps({'papers': len(PAPERS), 'artifacts': len(rows)}))
