"""Read-only independent complete-corpus integrity/search audit."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i38_propeller_stability_r2'
CORPUS=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
MANIFEST=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json'
def run():
    manifest=json.loads(MANIFEST.read_text())
    tree=json.loads((S/'frozen/sources/preprints-tree.json').read_text())
    assert not tree['truncated'] and len(tree['tree'])==13223
    entries={r['path']:r for r in tree['tree']}
    manuscripts={p.split('/')[1] for p in entries if p.startswith('preprints/')}
    patterns={
      'propeller':r'propeller',
      'countable_gaussian_interface':r'(?:countabl|infinit)[^.!?]{0,100}(?:score|partition|Gaussian)',
      'propeller_stability_interface':r'(?:stabil|deficit)[^.!?]{0,150}propeller|propeller[^.!?]{0,150}(?:stabil|deficit)'}
    matches={k:[] for k in patterns};total=0
    for r in manifest['files']:
        data=(CORPUS/r['path']).read_bytes();total+=len(data)
        assert len(data)==r['bytes'] and hashlib.sha256(data).hexdigest()==r['sha256'],r['path']
        blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        assert blob==r['git_blob']==entries[r['path']]['sha'],r['path']
        content=' '.join(data.decode('utf-8',errors='replace').split())
        for name,pat in patterns.items():
            found=list(re.finditer(pat,content,re.I))
            if found:matches[name].append({'path':r['path'],'count':len(found),'contexts':[content[max(0,m.start()-100):m.end()+100] for m in found[:8]],'contexts_limited_to':8})
    assert (len(manifest['files']),total,len(manuscripts))==(9340,141349121,749)
    return {'files':9340,'bytes':total,'tree_entries':13223,'manuscripts':749,'manifest_sha256':hashlib.sha256(MANIFEST.read_bytes()).hexdigest(),'patterns':patterns,'matches':matches,'scope':'Every cached file read and hashed; bounded lexical contexts, not semantic review of every manuscript. Complete tree includes non-text blobs not in text corpus.'}
if __name__=='__main__':print(json.dumps(run(),indent=2))
