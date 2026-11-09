#!/usr/bin/env python3
"""One-time own-root seal, using the verifier's identical core/binding logic."""
import hashlib,json,os,shutil,stat
from pathlib import Path

project=Path.cwd()
assert str(project)=='/home/mj-kang/Documents/Dev/math/openai-proof-research'
root=project/'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cr'
assert not (root/'MANIFEST.json').exists() and not (root/'REPORT.md').exists(),'already sealed'
ns={'__name__':'packet_verifier'}
exec(compile((root/'verify.py').read_text(),str(root/'verify.py'),'exec'),ns)
digest=ns['digest'];core=ns['core'];check=ns['check'];inventory=ns['inventory']
os.umask(0o077)
controls=root/'private/integrity-controls';controls.mkdir(mode=0o700)
seed=controls/'seed.txt';seed.write_text('r162cr tiny owned copy\n');seed.chmod(0o600)
mini=controls/'fixture';mini.mkdir(mode=0o700)
shutil.copy2(seed,mini/'FINAL.md');shutil.copy2(seed,mini/'data.txt')
(mini/'REPORT.md').write_text('Tiny copied integrity control only.\n');(mini/'REPORT.md').chmod(0o600)

def make_manifest(r):
    fs,ds=inventory(r)
    return {'schema':'r162cr-exact-packet-v1',
      'files':[{'path':s,'bytes':len(d:= (r/s).read_bytes()),'sha256':digest(d),'full_mode':fs[s].st_mode}
               for s in sorted(set(fs)-ns['DETACHED'])],
      'directories':[{'path':s,'full_mode':ds[s]} for s in sorted(ds)],
      'detached_full_modes':{s:stat.S_IFREG|0o600 for s in sorted(ns['DETACHED'])}}
m=make_manifest(mini);(mini/'MANIFEST.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n');(mini/'MANIFEST.json').chmod(0o600)
anchors={k:digest((mini/s).read_bytes()) for k,s in [('manifest','MANIFEST.json'),('final','FINAL.md'),('report','REPORT.md')]}
results=[{'control':'exact tiny copied fixture','result':check(mini,anchors,with_bindings=False)['status']}]

def rejects(label,fn):
    try:fn()
    except (AssertionError,ValueError,KeyError,OSError):results.append({'control':label,'result':'REJECT as expected'})
    else:raise AssertionError('negative control accepted: '+label)
for key in anchors:
    wrong=dict(anchors);wrong[key]='0'*64
    rejects('wrong '+key+' anchor',lambda w=wrong:check(mini,w,with_bindings=False))
copy=mini/'data.txt';before=copy.read_bytes();mode=copy.stat().st_mode
copy.write_bytes(before+b'!');rejects('changed copied payload',lambda:check(mini,anchors,with_bindings=False));copy.write_bytes(before)
copy.chmod(0o400);rejects('changed copied full mode',lambda:check(mini,anchors,with_bindings=False));copy.chmod(stat.S_IMODE(mode))
mb=(mini/'MANIFEST.json').read_bytes();bad=json.loads(mb);bad['files'].reverse();(mini/'MANIFEST.json').write_text(json.dumps(bad))
new=dict(anchors);new['manifest']=digest((mini/'MANIFEST.json').read_bytes())
rejects('unsorted membership with matching manifest anchor',lambda:check(mini,new,with_bindings=False))
(mini/'MANIFEST.json').write_bytes(mb)
assert check(mini,anchors,with_bindings=False)['status']=='MATCH'
assert copy.read_bytes()==seed.read_bytes() and copy.stat().st_mode==mode
results.append({'control':'restored exact tiny fixture','result':'MATCH'})
(controls/'results.json').write_text(json.dumps(results,indent=2)+'\n')

# Set own packet rights before membership preflight. Original exception files are never changed.
fs,ds=inventory(root)
for s in ds:
    path=root if s=='.' else root/s
    path.chmod(0o700 if s=='.' or s=='private' or s.startswith('private/') else 0o755)
for s in fs:
    (root/s).chmod(0o600 if s.startswith('private/') else 0o644)
bp=root/'private/completed-bindings.json';bindings=json.loads(bp.read_text())
for rec in bindings:
    rec['copy_full_mode']=(root/rec['copy']).stat().st_mode
    rec['copy_mode_stage']='Recorded at own preseal rights normalization; original full mode was recorded at initial copy.'
bp.write_text(json.dumps(bindings,indent=2)+'\n')

manifest=make_manifest(root)
preflight=core(root,manifest,require_detached=False)
bound=ns['bindings'](root,project)
# Same logic was used for this actual membership and for the tiny controls; no source-copy mutation.
report='''# R162CR detached sealing report

PREFREEZE/no nominee. No mathematical grade or campaign increment. This report is outside the payload manifest but inside the exclusive root. Its SHA256 is a required explicit detached anchor.

One-time preflight used verify.py's identical core inventory/hash/length/full-mode logic and its actual source-pin/completed-copy/primary bindings. Safe POSIX paths, sorted unique exact file and directory membership, full stat modes, all payload hashes/lengths, ten pinned Git blobs, nine complete-text lengths, five exact original/copy bindings and eight primary PDF/text bindings matched. Source truth was stipulated; these are artifact checks only.

Preflight: %d payload files, %d payload bytes, %d directories including root. Final whole-root file count is payload count plus two detached files. Protected material and its metadata are under private/ with restricted local rights; the entire exclusive root is mode0700. Original exception files were not modified; their initial full modes and bytes matched. Own-copy full modes were recorded at preseal rights normalization, not backdated to creation.

Tiny controls used a copied 23-byte owned text fixture. Exact fixture matched; three wrong detached anchors, one changed payload, one changed full mode and one unsorted manifest with a matching new anchor were rejected. Restoring the tiny fixture gave MATCH. No whole-packet clone or enlarged integrity suite was made. The fixture and control record are payload files.

The manifest was serialized once after that preflight. FINAL is included in its payload; MANIFEST and this REPORT are detached. All subsequent packet use is read-only. A read-only explicit-anchor check is printed by the sealing command and may be independently repeated using verify.py. There is no inherited manifest and no reduced selection represented as an inherited complete packet.

No optional original-history traversal, live workspace query, browser UI, git operation, nested agent, publication or downstream work. Reading limitations and the exact mathematical gap are in the private ledgers. These checks do not establish correctness, substantial contribution, acceptance, completeness of literature/history coverage or worldwide priority.
''' % preflight
assert len(seed.read_bytes())==23
for path,data in [(root/'REPORT.md',report.encode()),(root/'MANIFEST.json',(json.dumps(manifest,indent=2,sort_keys=True)+'\n').encode())]:
    with path.open('xb') as f:f.write(data)
    path.chmod(0o600)
anchors={k:digest((root/s).read_bytes()) for k,s in [('manifest','MANIFEST.json'),('final','FINAL.md'),('report','REPORT.md')]}
result=check(root,anchors,project)
print(json.dumps({'anchors':anchors,'verification':result,'whole_root_files':preflight[0]+2,'root':str(root)},indent=2))
