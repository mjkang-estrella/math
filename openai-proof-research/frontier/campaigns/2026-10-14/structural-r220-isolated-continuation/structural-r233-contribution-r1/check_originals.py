"""Read-only exact admitted-original baseline recheck; no directory traversal."""
from pathlib import Path
import hashlib, json, stat, datetime
O = Path(__file__).resolve().parent
baseline_bytes = (O / 'original-baseline.json').read_bytes()
baseline = json.loads(baseline_bytes)
A = Path(baseline['root'])
assert len(baseline['entries']) == 53
for e in baseline['entries']:
    p = A / e['path']
    s = p.lstat()
    assert stat.S_ISREG(s.st_mode) and not p.is_symlink()
    assert format(stat.S_IMODE(s.st_mode), '04o') == e['mode'], e['path']
    b = p.read_bytes()
    assert len(b) == e['bytes'] and hashlib.sha256(b).hexdigest() == e['sha256'], e['path']
print(json.dumps({'admitted_original_files': 53, 'unchanged_bytes_and_modes': True, 'baseline_sha256': hashlib.sha256(baseline_bytes).hexdigest(), 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}, sort_keys=True))
