"""Shared read-only evidence functions; importing this module writes nothing."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[3]
S='frontier/sources/i95_finite_cat0_obstruction_r2';E='frontier/experiments/i95_finite_cat0_obstruction_r2'
REPORT='frontier/reviews/i95-finite-cat0-obstruction-r2.md'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
MUTABLE=sorted(['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'])
EX=[S+'/seal-v1.json',S+'/seal-v1.sha256']
def path(s):
    p=Path(s);assert not p.is_absolute() and '..' not in p.parts and p.as_posix()==s
    q=R
    for part in p.parts:
        q=q/part;assert not q.is_symlink(),s
    return q
def raw(s):return path(s).read_bytes()
def sha(b):return hashlib.sha256(b).hexdigest()
def load(s):return json.loads(raw(s))
def inventory():
    names=[REPORT]
    for d in [S,E]:
        for p in path(d).rglob('*'):
            n=p.relative_to(R).as_posix();path(n)
            if p.is_file():names.append(n)
            else:assert p.is_dir()
    return sorted(names)
def complete_domain(searches):
    tree=load('sources/preprints-tree.json');entries=tree['tree'];assert not tree['truncated'] and len(entries)==13223
    blobs={d['path']:d for d in entries if d['type']=='blob'}
    assert len(blobs)==10373 and len({p.split('/')[1] for p in blobs})==749
    domain=load('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json')
    assert len(domain)==10373 and {d['path'] for d in domain}==set(blobs)
    outside=[json.loads(l) for l in raw('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl').splitlines()]
    outside={d['path']:d for d in outside};assert len(outside)==1033
    regex=[re.compile(q['pattern'],re.I) for q in searches];hits=[[] for _ in searches]
    body_records=[];corpus=[];pdfs=0
    for d in sorted(domain,key=lambda x:x['path']):
        name=d['path'];b=raw(d['local']);assert sha(b)==d['sha256'],d['local']
        if d['kind']=='corpus':original=b;local=d['local'];corpus.append(local)
        else:
            o=outside[name];local=o['local'];original=raw(local)
            assert sha(original)==o['sha256'] and len(original)==o['bytes'] and o['git_match']
            if 'extraction' in o:
                pdfs+=1;assert o['extraction']['path']==d['local'] and o['extraction']['sha256']==sha(b)
        assert len(original)==blobs[name]['size']
        assert hashlib.sha1(b'blob '+str(len(original)).encode()+b'\0'+original).hexdigest()==blobs[name]['sha'],name
        body_records.append({'path':name,'original':local,'original_sha256':sha(original),'git_blob':blobs[name]['sha'],'representative':d['local'],'representative_sha256':sha(b)})
        for n,line in enumerate(b.decode(errors='replace').splitlines(),1):
            for q,h in zip(regex,hits):
                if q.search(line):h.append({'path':name,'local':d['local'],'line':n,'text':line})
    assert len(corpus)==9340 and pdfs==776
    rg=subprocess.check_output(['rg','--files','--no-ignore','frontier/sources/i14_spectral_width_novelty_r3/corpus'],cwd=R).decode().splitlines()
    assert sorted(rg)==sorted(corpus)
    return body_records,hits,sorted(corpus)
