"""Write manifest.json: sha256 of every lane file, EXCLUDING manifest.json
itself and verification-receipt.json (explicitly), plus external bindings."""
import os, json, hashlib, datetime

lane = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXCL = {'manifest.json', 'verification-receipt.json'}
B = os.path.normpath(os.path.join(lane, '..', '..'))


def h(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


files = {}
for root, dirs, fs in os.walk(lane):
    dirs[:] = [d for d in dirs if d != '__pycache__']
    for f in fs:
        rel = os.path.relpath(os.path.join(root, f), lane)
        if rel in EXCL:
            continue
        files[rel] = h(os.path.join(root, f))
external = {}
for rel in ['lanes/sol-fresh-source-discovery-r213/sources/even.pdf',
            'lanes/sol-fresh-source-discovery-r213/frozen/even.pdf',
            'lanes/sol-fresh-source-discovery-r213/sources/even-abs.html',
            'lanes/sol-fresh-source-discovery-r213/frozen/even-abs.html',
            'lanes/sol-fresh-source-discovery-r213/SCOUTING.md',
            'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:
    external[rel] = h(os.path.join(B, rel))
m = {'generated_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
     'excluded_explicitly': sorted(EXCL), 'files': dict(sorted(files.items())),
     'external_originals': external}
json.dump(m, open(os.path.join(lane, 'manifest.json'), 'w'), indent=1)
print(len(files), 'files hashed; excluded', sorted(EXCL))
