#!/usr/bin/env python3
# Reason-checked replay of the author's verify.py on disposable copies only.
import hashlib, json, os, shutil, sys, tempfile, traceback
from pathlib import Path
sys.dont_write_bytecode = True
base = Path(sys.argv[1]).absolute()          # disposable authenticated copy
anchor = sys.argv[2]
sys.path.insert(0, str(base))
from verify import verify, inventory          # author's verifier (read before running)

work = Path(tempfile.mkdtemp(prefix='reason-', dir=base.parent))
def clone(name):
    d = work / name
    shutil.copytree(base, d, symlinks=True)
    shutil.rmtree(d / '__pycache__', ignore_errors=True)
    return d
def reanchor(d):
    inv = inventory(d)
    (d / 'manifest.json').write_text(json.dumps(inv, indent=2, sort_keys=True) + '\n')
    return hashlib.sha256((d / 'manifest.json').read_bytes()).hexdigest()

results = []
def expect(name, d, a, kind, text):
    try:
        verify(d, a)
    except Exception as e:
        ok = isinstance(e, kind) and (text in str(e))
        results.append({'case': name, 'rejected': True, 'type': type(e).__name__,
                        'message': str(e), 'reason_ok': ok})
        if not ok:
            raise SystemExit('WRONG REASON for ' + name + ': ' + repr(e))
    else:
        raise SystemExit('ACCEPTED mutation ' + name)

try:
    d = clone('positive'); n = verify(d, anchor)
    results.append({'case': 'positive', 'accepted': True, 'counts': list(n)})
    INV = 'exact directory/file inventory mismatch'
    d = clone('wrong-anchor'); expect('wrong-anchor', d, '0' * 64, ValueError, 'external anchor mismatch')
    d = clone('short-anchor'); expect('short-anchor', d, anchor[:-1], ValueError, 'external anchor mismatch')
    d = clone('changed-file'); p = d / 'diagnostic.py'; p.write_bytes(p.read_bytes() + b'\n#m\n')
    expect('changed-file', d, anchor, ValueError, INV)
    d = clone('changed-proof'); p = d / 'proof.md'; p.write_bytes(p.read_bytes().replace(b'|k|=1', b'|k|=2', 1))
    expect('changed-proof', d, anchor, ValueError, INV)
    d = clone('missing-file'); (d / 'diagnostic.py').unlink(); expect('missing-file', d, anchor, ValueError, INV)
    d = clone('extra-file'); (d / 'extra').write_text('m'); expect('extra-file', d, anchor, ValueError, INV)
    d = clone('extra-empty-directory'); (d / 'extra-empty').mkdir(); expect('extra-empty-directory', d, anchor, ValueError, INV)
    d = clone('payload-symlink'); p = d / 'diagnostic.py'; p.unlink(); p.symlink_to(base / 'diagnostic.py')
    expect('payload-symlink', d, anchor, ValueError, 'link/nonregular: diagnostic.py')
    d = clone('directory-symlink'); shutil.rmtree(d / 'private/source337')
    (d / 'private/source337').symlink_to(base / 'private/source337', target_is_directory=True)
    expect('directory-symlink', d, anchor, ValueError, 'link/nonregular: private/source337')
    d = clone('root-symlink'); link = work / 'root-link'; link.symlink_to(d, target_is_directory=True)
    expect('root-symlink', link, anchor, ValueError, 'root/ancestor link or non-directory')
    d = clone('ancestor-symlink'); link = work / 'anc-link'; link.symlink_to(work, target_is_directory=True)
    expect('ancestor-symlink', link / d.name, anchor, ValueError, 'root/ancestor link or non-directory')
    d = clone('hardlinked-payload'); os.link(d / 'diagnostic.py', work / 'hl-payload')
    expect('hardlinked-payload', d, anchor, ValueError, 'hardlink: diagnostic.py')
    d = clone('fifo-payload'); p = d / 'diagnostic.py'; p.unlink(); os.mkfifo(p)
    expect('fifo-payload', d, anchor, ValueError, 'link/nonregular: diagnostic.py')
    d = clone('hardlinked-manifest'); os.link(d / 'manifest.json', work / 'hl-manifest')
    expect('hardlinked-manifest', d, anchor, ValueError, 'manifest link/nonregular')
    d = clone('changed-manifest'); (d / 'manifest.json').write_text('{}\n')
    expect('changed-manifest', d, anchor, ValueError, 'external anchor mismatch')
    # Re-anchored counterfeits: inventory self-consistent, content checks must still reject.
    d = clone('reanchored-source-blob'); p = d / 'private/source337/build/sections/03-radial.tex'
    p.write_bytes(p.read_bytes() + b'%m\n'); a = reanchor(d)
    try:
        verify(d, a)
    except AssertionError as e:
        tb = traceback.extract_tb(e.__traceback__)[-1].line
        ok = 'git_blob' in tb
        results.append({'case': 'reanchored-source-blob', 'rejected': True, 'type': 'AssertionError',
                        'failing_check': tb, 'reason_ok': ok})
        if not ok: raise SystemExit('WRONG REASON reanchored-source-blob ' + tb)
    else:
        raise SystemExit('ACCEPTED reanchored-source-blob')
    d = clone('reanchored-primary-pdf'); p = d / 'private/stadler2212.pdf'
    p.write_bytes(p.read_bytes() + b'\n'); a = reanchor(d)
    try:
        verify(d, a)
    except AssertionError as e:
        tb = traceback.extract_tb(e.__traceback__)[-1].line
        ok = 'pdf_sha256' in tb
        results.append({'case': 'reanchored-primary-pdf', 'rejected': True, 'type': 'AssertionError',
                        'failing_check': tb, 'reason_ok': ok})
        if not ok: raise SystemExit('WRONG REASON reanchored-primary-pdf ' + tb)
    else:
        raise SystemExit('ACCEPTED reanchored-primary-pdf')
finally:
    shutil.rmtree(work)
print(json.dumps({'integrity_only': True, 'all_reasons_ok': True, 'results': results}, indent=1))
