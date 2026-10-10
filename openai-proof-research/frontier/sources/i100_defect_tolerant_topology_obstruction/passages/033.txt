#!/usr/bin/env python3
"""Offline READ-ONLY evidence verifier. No downloads, writes, repairs or seal creation.
Child commands: inherited read-only I94 verifier, pdftotext to stdout, diagnostics -B.
--preseal checks every available dependency without requiring the final seal.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,os,re,subprocess

ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i97_relative_involution_stabilization'
E='frontier/experiments/i97_relative_involution_stabilization'
OLD='frontier/sources/i94_topology_transformation_discovery'
REPORT='frontier/iterations/i97-relative-involution-stabilization.md'
SEAL=S+'/seal.json'
DRIFT={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'

def check(v,s):
    if not v: raise AssertionError(s)
def raw(p): return (ROOT/p).read_bytes()
def sha(b): return hashlib.sha256(b).hexdigest()
def doc(p): return json.loads(raw(p))
def command(args):
    r=subprocess.run(args,cwd=ROOT,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=False)
    check(r.returncode==0,'Child failed: '+str(args)+'\n'+r.stdout.decode(errors='replace')+'\n'+r.stderr.decode(errors='replace'))
    return r.stdout
def owned():
    out=[REPORT]
    for base in (S,E): out.extend(str(p.relative_to(ROOT)) for p in (ROOT/base).rglob('*') if p.is_file())
    return sorted(x for x in out if x!=SEAL)

def main():
    check(sys.argv[1:] in ([],['--preseal']),'only optional --preseal')
    pre=bool(sys.argv[1:]);files=owned()
    check(not any('__pycache__' in f or f.endswith('.pyc') for f in files),'bytecode artifact')
    if not pre:
        seal=doc(SEAL)
        check(seal['pin']==PIN and seal['excluded_owned_files']==[SEAL],'seal scope')
        check(seal['files']==[dict(path=p,sha256=sha(raw(p))) for p in files],'owned inventory/hash mismatch')
    inputs=doc(S+'/inputs.json');drift=[]
    check({x['original'] for x in inputs if x['may_drift']}==DRIFT,'drift policy')
    for x in inputs:
        check(sha(raw(x['snapshot']))==x['sha256'],'snapshot '+x['snapshot'])
        if sha(raw(x['original']))!=x['sha256']:
            check(x['may_drift'] and x['original'] in DRIFT,'immutable original '+x['original'])
            drift.append(x['original'])
    refs=doc(S+'/immutable-references.json')
    for x in refs:
        check(not x.get('may_drift',False),'reference drift forbidden')
        check(not re.search(r'i9[56][_-]',x['path']),'in-progress I95/I96 binding')
        check(sha(raw(x['path']))==x['sha256'],'reference '+x['path'])
    check(sha(raw(OLD+'/seal.json'))=='0e260b2444ad2a9eb1412180f5fe97477da037db8c60e55848720e355fd0d643','original I94 seal')
    old=json.loads(command([sys.executable,'-B','frontier/experiments/i94_topology_transformation_discovery/verify.py']))
    check(old['status']=='PASS' and old['original_blob_positions']==10373 and old['outside_PDF_hash_bindings']==776,'inherited replay')
    tree=doc(S+'/snapshots/sources/preprints-tree.json')
    check(not tree['truncated'] and len(tree['tree'])==13223,'complete tree')
    blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
    titles=sorted({x.split('/')[1] for x in blobs})
    check(len(blobs)==10373 and len(titles)==749,'domain counts')
    domain=doc(OLD+'/search-domain.json')
    check({x['path'] for x in domain}==set(blobs),'domain bijection')
    screen=doc(S+'/selection.json')
    check(screen['all_title_hits']==[t for t in titles if re.search(screen['title_pattern'],t,re.I)],'title replay')
    check(doc(S+'/selected-inventory.json')==[x for x in domain if x['path'].split('/')[1] in screen['selected_families']],'selected completeness')
    queries=doc(S+'/queries.json');patterns={k:re.compile(v,re.I) for k,v in queries.items()};hits={k:[] for k in queries}
    for x in domain:
        # I94 has just checked original SHA-256/Git blob identities and all representatives.
        for i,line in enumerate(raw(x['local']).decode(errors='replace').splitlines(),1):
            for k,pattern in patterns.items():
                if pattern.search(line):hits[k].append(dict(path=x['path'],line=i,text=line))
    for k,h in hits.items():
        check(h==[json.loads(l) for l in raw(S+'/search-'+k+'.jsonl').decode().splitlines()],'search '+k)
    reads=doc(S+'/read-manifest.json')
    for x in reads:
        b=raw(x['local']);ls=b.decode(errors='replace').splitlines();a,z=x['start'],x['end']
        check(sha(b)==x['sha256'],'read source '+x['local'])
        check(len(ls)==x['total_splitlines'] and b.count(b'\n')==x['total_LF_newlines'],'line convention '+x['label'])
        check(1<=a<=z<=len(ls),'range '+x['label'])
        passage=('\n'.join(ls[a-1:z])+'\n').encode()
        check(sha(passage)==x['passage_sha256'] and passage==raw(x['passage_file']),'passage '+x['label'])
    requests=doc(S+'/external/requests.json');pdfs=0
    for x in requests:
        check('error' not in x,'retained download failure '+x['url'])
        check(sha(raw(x['pdf']))==x['sha256'] and sha(raw(x['text']))==x['text_sha256'],'new primary bytes')
        check(sha(command(['pdftotext','-layout',x['pdf'],'-']))==x['text_sha256'],'new primary extraction')
        pdfs+=1
    diagnostic=json.loads(command([sys.executable,'-B',E+'/diagnostics.py']))
    check(diagnostic==doc(E+'/diagnostic-results.json'),'diagnostic output')
    print(json.dumps(dict(status='PASS',mode='preseal' if pre else 'final-seal',owned_files=len(files),immutable_references=len(refs),allowed_ledger_drift=drift,original_blob_positions=10373,manuscripts=749,inherited_pdf_hash_bindings=776,inherited_I94_replay=old,read_records=len(reads),selected_representations=len(doc(S+'/selected-inventory.json')),new_primary_PDF_replays=pdfs,search_counts={k:len(v) for k,v in hits.items()},diagnostics=diagnostic,limits='Evidence replay only; no geometric construction, full-domain semantic audit, all-PDF re-extraction, human review, or formal certification.'),indent=2,sort_keys=True))

if __name__=='__main__':main()
