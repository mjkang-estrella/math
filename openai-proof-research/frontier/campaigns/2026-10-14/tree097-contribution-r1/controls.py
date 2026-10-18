#!/usr/bin/env python3
"""MIT. Verifier controls run ONLY on disposable copies under /var/tmp.

Usage: controls.py PACKET_ROOT AUTHOR_ROOT [RESULT_JSON]
The packet and author roots are only read. Every mutation acts on a fresh
copy. Expected outcome: the positive control passes and every mutation fails.
"""
import json, os, shutil, subprocess, sys, tempfile
from pathlib import Path

sys.dont_write_bytecode = True
PKT = Path(sys.argv[1]).absolute()
AUTH = Path(sys.argv[2]).absolute()
OUT = Path(sys.argv[3]).absolute() if len(sys.argv) > 3 else None
SKIP = {'MANIFEST.json', 'controls-result.json', '__pycache__'}
sys.path.insert(0, str(PKT))
import seal  # noqa: E402

BASE = Path(tempfile.mkdtemp(prefix='tree097-contrib-controls-', dir='/var/tmp'))


def fresh(tag):
    d = BASE / tag
    shutil.copytree(PKT, d, ignore=lambda _d, names: [n for n in names if n in SKIP])
    return d, seal.build(d)


def run(root, anchor, author=None):
    cmd = [sys.executable, '-B', str(PKT / 'verify.py'), '--root', str(root),
           '--expected-manifest-sha256', anchor]
    if author:
        cmd += ['--author-root', str(author)]
    p = subprocess.run(cmd, capture_output=True, text=True)
    return p.returncode, (p.stdout + p.stderr).strip()


results = []


def record(name, rc, msg, expect_pass):
    ok = (rc == 0) == expect_pass
    results.append({'control': name, 'expected': 'PASS' if expect_pass else 'REJECT',
                    'rc': rc, 'message': msg[:160], 'as_expected': ok})


d, a = fresh('positive')
record('positive', *run(d, a), True)
record('wrong_anchor', *run(d, '0' * 64), False)
record('malformed_anchor', *run(d, 'xyz'), False)

d, a = fresh('byte_edit')
p = d / 'report.md'
p.write_bytes(p.read_bytes().replace(b'TECHNICAL', b'SUBSTANTIAL', 1))
record('byte_edit_report', *run(d, a), False)

d, a = fresh('reseal_edit')
p = d / 'report.md'
p.write_bytes(p.read_bytes().replace(b'TECHNICAL', b'SUBSTANTIAL', 1))
new = seal.build(d)
record('resealed_edit_old_anchor', *run(d, a), False)
record('resealed_edit_self_anchor_is_new_hash', 0 if new != a else 1,
       'self-generated anchor differs from external anchor', True)

d, a = fresh('extra_file')
(d / 'extra.txt').write_text('x')
record('extra_file', *run(d, a), False)

d, a = fresh('extra_dir')
(d / 'emptydir').mkdir()
record('extra_empty_directory', *run(d, a), False)

d, a = fresh('deleted')
(d / 'reading-limits.md').unlink()
record('deleted_file', *run(d, a), False)

d, a = fresh('symlink_extra')
os.symlink(d / 'report.md', d / 'link.md')
record('extra_symlink', *run(d, a), False)

d, a = fresh('symlink_replace')
tgt = BASE / 'outside-report.md'
shutil.copyfile(d / 'report.md', tgt)
(d / 'report.md').unlink()
os.symlink(tgt, d / 'report.md')
record('payload_replaced_by_symlink', *run(d, a), False)

d, a = fresh('hardlink')
os.link(d / 'report.md', BASE / 'hardlink-outside.md')
record('hardlinked_payload', *run(d, a), False)

d, a = fresh('fifo')
os.mkfifo(d / 'pipe')
record('fifo_node', *run(d, a), False)

d, a = fresh('manifest_dir_edit')
m = json.loads((d / 'MANIFEST.json').read_text())
m['directories'].append('ghost')
raw = (json.dumps(m, indent=1, sort_keys=True) + '\n').encode()
(d / 'MANIFEST.json').write_bytes(raw)
import hashlib  # noqa: E402
record('manifest_edit_old_anchor', *run(d, a), False)
record('manifest_ghost_dir_with_its_own_hash', *run(d, hashlib.sha256(raw).hexdigest()), False)

d, a = fresh('author_ok')
record('author_anchor_positive', *run(d, a, AUTH), True)
ac = BASE / 'author-copy'
ac.mkdir()
for n in ('MANIFEST.json', 'candidate.md', 'original-scope.txt', 'prefix-law.md'):
    shutil.copyfile(AUTH / n, ac / n)
record('author_copy_positive', *run(d, a, ac), True)
s = ac / 'original-scope.txt'
s.write_bytes(s.read_bytes() + b' ')
record('author_scope_mutation', *run(d, a, ac), False)

summary = {'base': str(BASE), 'all_as_expected': all(r['as_expected'] for r in results),
           'count': len(results), 'results': results,
           'scope': 'Disposable-copy integrity controls; not mathematical evidence.'}
txt = json.dumps(summary, indent=1)
print(txt)
if OUT:
    OUT.write_text(txt + '\n')
sys.exit(0 if summary['all_as_expected'] else 1)
