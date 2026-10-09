#!/usr/bin/env python3
"""Read-only input verification; writes only in the round-4 source directory."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import hashlib, json, urllib.request
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'frontier/sources/i03_operator_r4'
sha=lambda b: hashlib.sha256(b).hexdigest()
blob=lambda b: hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
manifest=json.loads((ROOT/'frontier/sources/i03_operator/upstream_manifest.json').read_text())
tree={e['path']:e['sha'] for e in json.loads((ROOT/'sources/preprints-tree.json').read_text())['tree']}
pin=json.loads((ROOT/'sources/upstream.json').read_text())['commit']
def verify(e):
    b=(ROOT/e['file']).read_bytes()
    r={'path':e['path'], 'url':e['url'], 'sha256':sha(b), 'git_blob_sha1':blob(b),
       'local_sha256_matches':sha(b)==e['sha256'], 'local_git_blob_matches':blob(b)==e['git_blob_sha1'],
       'pinned_tree_matches':blob(b)==tree[e['path']], 'url_is_pinned':f'/{pin}/' in e['url']}
    try:
        with urllib.request.urlopen(e['url'],timeout=35) as response: fresh=response.read()
        dest=OUT/Path(e['file']).name
        dest.write_bytes(fresh)
        r.update(fresh_file=str(dest.relative_to(ROOT)), fresh_sha256=sha(fresh), fresh_matches=fresh==b)
    except Exception as exc: r['fresh_error']=str(exc)
    return r
with ThreadPoolExecutor(max_workers=6) as pool: upstream=list(pool.map(verify,manifest))
inputs=[]
for e in json.loads((ROOT/'frontier/sources/i03_operator/input_manifest.json').read_text()):
    actual=sha((ROOT/e['file']).read_bytes())
    inputs.append(dict(e,actual_sha256=actual,matches=actual==e['sha256']))
literature=[]
for e in json.loads((ROOT/'frontier/sources/i03_operator/literature_manifest.json').read_text()):
    if 'sha256' not in e: continue
    p=ROOT/'frontier/sources/i03_operator'/ (e['name']+'.pdf')
    b=p.read_bytes()
    literature.append({'file':str(p.relative_to(ROOT)),'sha256':sha(b),'matches':sha(b)==e['sha256'],'bytes_match':len(b)==e['bytes']})
original=ROOT/'frontier/experiments/i03_operator'
reproduced=ROOT/'frontier/experiments/i03_operator_r4'
r={'pin':pin,'upstream':upstream,'prior_input_manifest':inputs,'literature':literature,
   'original_script_copy_identical':(original/'check_halfspace.py').read_bytes()==(reproduced/'reproduce_original.py').read_bytes(),
   'original_output_reproduced_byte_for_byte':(original/'output.json').read_bytes()==(reproduced/'output.json').read_bytes()}
(OUT/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
current_inputs=['AGENTS.md','sources/upstream.json','sources/preprints-tree.json','sources/CONTENTS.md','frontier/iterations/README.md','frontier/iterations/i02-operator-r2.md','frontier/reviews/i02-operator-r3.md','frontier/iterations/i03-operator-halfspace.md','frontier/sources/i03_operator/upstream_manifest.json','frontier/sources/i03_operator/input_manifest.json','frontier/sources/i03_operator/literature_manifest.json','frontier/experiments/i03_operator/check_halfspace.py','frontier/experiments/i03_operator/output.json']
(OUT/'input_manifest.json').write_text(json.dumps([{'file':p,'sha256':sha((ROOT/p).read_bytes())} for p in current_inputs],indent=2)+'\n')
print(json.dumps({'upstream_count':len(upstream),'local_all_pass':all(all(e[k] for k in ['local_sha256_matches','local_git_blob_matches','pinned_tree_matches','url_is_pinned']) for e in upstream),'fresh_matches':sum(e.get('fresh_matches',False) for e in upstream),'fresh_errors':[e for e in upstream if 'fresh_error' in e],'input_hash_matches':sum(e['matches'] for e in inputs),'input_hash_total':len(inputs),'literature_hash_matches':sum(e['matches'] for e in literature),'original_output_reproduced_byte_for_byte':r['original_output_reproduced_byte_for_byte']},indent=2))
