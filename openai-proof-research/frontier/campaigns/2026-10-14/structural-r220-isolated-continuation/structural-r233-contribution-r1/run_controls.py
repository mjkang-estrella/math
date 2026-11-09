"""Preseal miniature copied-verifier controls, entirely inside this own root.
Do not rerun after sealing. These are artifact checks, not mathematical tests.
"""
from pathlib import Path
import hashlib, json, shutil, subprocess, sys
O = Path(__file__).resolve().parent
T = O / 'miniature-control-copy'
assert not T.exists()
T.mkdir()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
def run(anchors):
    r = subprocess.run([sys.executable, '-I', '-B', str(T/'verify_packet.py'), '--root', str(T), '--final-sha256', anchors['FINAL.md'], '--manifest-sha256', anchors['MANIFEST.json'], '--report-sha256', anchors['REPORT.md']], capture_output=True, text=True)
    return r.returncode
try:
    shutil.copyfile(O/'verify_packet.py', T/'verify_packet.py')
    (T/'sample.txt').write_text('Miniature artifact control only.\n')
    names = ['sample.txt', 'selection.json', 'verify_packet.py']
    (T/'selection.json').write_text(json.dumps({'files': names}, sort_keys=True)+'\n')
    entries = [{'path': n, 'bytes': (T/n).stat().st_size, 'sha256': sha(T/n), 'mode': '0444'} for n in names]
    (T/'MANIFEST.json').write_text(json.dumps({'entries': entries}, sort_keys=True)+'\n')
    (T/'FINAL.md').write_text('Manifest SHA256: '+sha(T/'MANIFEST.json')+'\nSelection SHA256: '+sha(T/'selection.json')+'\n')
    (T/'REPORT.md').write_text('Miniature copied control. No mathematical verdict.\n')
    anchors = {n: sha(T/n) for n in ['FINAL.md','MANIFEST.json','REPORT.md']}
    for p in T.iterdir():p.chmod(0o444)
    results = {'intact_copy_accepted': run(anchors) == 0}
    p = T/'sample.txt'; original = p.read_bytes();p.chmod(0o644);p.write_bytes(original+b'altered\n');p.chmod(0o444)
    results['changed_bytes_rejected'] = run(anchors) != 0
    p.chmod(0o644);p.write_bytes(original);p.chmod(0o644)
    results['changed_mode_rejected'] = run(anchors) != 0
    p.chmod(0o444)
    extra = T/'unlisted.txt';extra.write_text('extra');extra.chmod(0o444)
    results['unlisted_file_rejected'] = run(anchors) != 0
    extra.unlink()
    bad = dict(anchors);bad['REPORT.md']='0'*64
    results['wrong_detached_anchor_rejected'] = run(bad) != 0
    assert all(results.values()), results
    (O/'control-results.json').write_text(json.dumps({'miniature_copied_controls': results, 'mathematical_evidence': False}, indent=2, sort_keys=True)+'\n')
    print(json.dumps(results, sort_keys=True))
finally:
    shutil.rmtree(T)
