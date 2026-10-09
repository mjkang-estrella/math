#!/usr/bin/env python3
"""Run unchanged author diagnostics/verifier; intercept its only output write."""
import contextlib
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import sys
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[3]
E = Path(__file__).resolve().parent
S = ROOT / 'frontier/sources/i38_propeller_stability_r2'
AUTHOR_E = ROOT / 'frontier/experiments/i38_inequality_stability_discovery'

def run():
    baseline = json.loads((S / 'author-before.json').read_text())
    def check():
        for item in baseline:
            data = (ROOT/item['path']).read_bytes()
            assert hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
    check()
    sys.path.insert(0, str(AUTHOR_E))
    spec = importlib.util.spec_from_file_location('i38_author_verifier', AUTHOR_E/'verify.py')
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    captured = []
    def intercept(path, data, *args, **kwargs):
        assert path.resolve() == (AUTHOR_E/'verification.json').resolve(), str(path)
        captured.append(json.loads(data))
        return len(data)
    stdout = io.StringIO()
    with patch.object(Path, 'write_text', intercept), contextlib.redirect_stdout(stdout):
        result = mod.main()
    assert result == 0 and len(captured) == 1, stdout.getvalue()
    assert captured[0]['status'] == 'PASS'
    # The original CLI diagnostic prints and performs no writes; invoke it unchanged.
    import subprocess
    proc = subprocess.run([sys.executable, '-B', str(AUTHOR_E/'diagnostics.py')],
                          cwd=ROOT, capture_output=True, text=True, check=True)
    diagnostics = json.loads(proc.stdout)
    check()
    out = {'status':'PASS', 'unchanged_author_files':len(baseline),
           'intercepted_write':str(AUTHOR_E/'verification.json'),
           'author_verification':captured[0], 'diagnostics':diagnostics,
           'limitations':'Integrity and finite diagnostics only, not universal analytic proof.'}
    return out

if __name__ == '__main__':
    result = run()
    (E/'author-reproduction.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['diagnostics']},indent=2))
