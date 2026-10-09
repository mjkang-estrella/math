"""Execute unchanged author verifier; capture its sole report write in memory.

No author file, seal or output is regenerated. The execution uses the original
__file__, original source bytes, and original check script. The interception is
necessary because this review may write only in its own directories.
"""
from pathlib import Path
import contextlib
import hashlib
import io
import json
import runpy
import sys

ROOT = Path(__file__).resolve().parents[3]
AUTHOR = ROOT / 'frontier/experiments/i36_harmonic_analysis_discovery'


def reproduce():
    before = {p: hashlib.sha256(p.read_bytes()).hexdigest()
              for d in (AUTHOR, ROOT / 'frontier/sources/i36_harmonic_analysis_discovery')
              for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
    report = ROOT / 'frontier/iterations/i36-harmonic-analysis-discovery.md'
    before[report] = hashlib.sha256(report.read_bytes()).hexdigest()
    original_write = Path.write_text
    captured = []
    def intercept(path, data, *args, **kwargs):
        assert path.resolve() == (AUTHOR / 'verification.json').resolve(), path
        captured.append(data)
        return len(data)
    output = io.StringIO()
    sys.dont_write_bytecode = True
    try:
        Path.write_text = intercept
        with contextlib.redirect_stdout(output):
            runpy.run_path(str(AUTHOR / 'verify.py'), run_name='__main__')
    finally:
        Path.write_text = original_write
    assert len(captured) == 1 and captured[0] == output.getvalue()
    assert all(hashlib.sha256(p.read_bytes()).hexdigest() == h for p, h in before.items())
    return {'status': 'PASS', 'author_bytes_unchanged': len(before),
            'method': 'Original verifier executed unchanged; only Path.write_text for its verification.json captured in memory.',
            'verifier_sha256': hashlib.sha256((AUTHOR / 'verify.py').read_bytes()).hexdigest(),
            'result': json.loads(output.getvalue())}


if __name__ == '__main__':
    print(json.dumps(reproduce(), sort_keys=True, indent=2))
