#!/usr/bin/env python3
"""Offline READ-ONLY I94 evidence verifier. No downloads, writes, repairs or resealing.
Run python -B. The only child processes are rg, pdftotext/pdftoppm to stdout,
and the owned diagnostics with -B. --preseal verifies dependencies before sealing.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess

ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i94_topology_transformation_discovery'
E='frontier/experiments/i94_topology_transformation_discovery'
REPORT='frontier/iterations/i94-topology-transformation-discovery.md'
SEAL=S+'/seal.json'
DRIFT={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}

def check(v,msg):
    if not v: raise AssertionError(msg)
def raw(p): return (ROOT/p).read_bytes()
def sha(b): return hashlib.sha256(b).hexdigest()
def doc(p): return json.loads(raw(p))
def command(args):
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
    r=subprocess.run(args,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=False)
    check(r.returncode==0,'child command failed: '+str(args)+' '+r.stderr.decode(errors='replace'))
    return r.stdout

def owned():
    names=[REPORT]
    for base in [S,E]:
        names.extend(str(p.relative_to(ROOT)) for p in (ROOT/base).rglob('*') if p.is_file())
    return sorted(p for p in names if p!=SEAL)

def main():
    check(sys.argv[1:] in [[],['--preseal']],'only optional --preseal is accepted')
    preseal=bool(sys.argv[1:])
    files=owned()
    if not preseal:
        seal=doc(SEAL)
        check(seal['excluded_owned_files']==[SEAL],'seal exclusion')
        check(seal['files']==[{'path':p,'sha256':sha(raw(p))} for p in files],'owned inventory or bytes changed')
    inputs=doc(S+'/inputs.json');drift=[]
    check({x['original'] for x in inputs if x['may_drift']}==DRIFT,'drift allowlist changed')
    for x in inputs:
        check(sha(raw(x['snapshot']))==x['sha256'],'snapshot changed '+x['snapshot'])
        if sha(raw(x['original']))!=x['sha256']:
            check(x['may_drift'] and x['original'] in DRIFT,'immutable original changed '+x['original'])
            drift.append(x['original'])
    refs=doc(S+'/immutable-references.json')
    for x in refs:
        check(not x['may_drift'],'extra drift permission')
        check('i91_' not in x['path'] and 'i91-' not in x['path'],'I91 reference prohibited')
        check(sha(raw(x['path']))==x['sha256'],'reference changed '+x['path'])
    up=doc(S+'/snapshots/sources/upstream.json')
    check(up['commit']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','pin changed')
    tree=doc(S+'/snapshots/sources/preprints-tree.json')
    check(tree['truncated'] is False,'tree truncated')
    entries=tree['tree'];blobs={x['path']:x['sha'] for x in entries if x['type']=='blob'}
    titles=sorted({x['path'].split('/')[1] for x in entries if len(x['path'].split('/'))>2})
    check(len(entries)==13223 and len(blobs)==10373 and len(titles)==749,'tree counts')
    check(titles==doc(S+'/all-titles.json'),'title inventory')
    domain=doc(S+'/search-domain.json')
    check(len(domain)==len(blobs) and {x['path'] for x in domain}==set(blobs),'domain completeness')
    bodies={}
    for x in domain:
        original=raw(x['original_local']);body=raw(x['local'])
        check(sha(original)==x['original_sha256'],'original hash '+x['path'])
        git=hashlib.sha1(b'blob '+str(len(original)).encode()+b'\0'+original).hexdigest()
        check(git==blobs[x['path']]==x['git_sha'],'Git blob identity '+x['path'])
        check(sha(body)==x['sha256'],'representative hash '+x['path'])
        bodies[x['path']]=body.decode(errors='replace').splitlines()
    inventory=doc(S+'/i14-files.json')
    found=sorted(command(inventory['command']).decode().splitlines())
    check(found==inventory['files'],'I14 rg inventory')
    check(set(found)=={x['original_local'] for x in domain if x['kind']=='corpus'},'I14 domain positions')
    selected=doc(S+'/selected-inventory.json');screen=doc(S+'/title-screen.json')
    families=screen['selected_families']
    check(len(families)==10 and len(selected)==129,'selection counts')
    expected=[x for x in domain if x['path'].split('/')[1] in families]
    check(sorted(selected,key=lambda x:x['path'])==sorted(expected,key=lambda x:x['path']),'selected family completeness')
    check(screen['title_hits']==[n for n in titles if re.search(screen['title_pattern'],n,re.I)],'title lexical replay')
    queries=doc(S+'/queries.json');compiled={name:re.compile(p,re.I) for name,p in queries.items()}
    hits={name:[] for name in queries}
    for x in domain:
        for i,line in enumerate(bodies[x['path']],1):
            for name,pattern in compiled.items():
                if pattern.search(line):hits[name].append({'path':x['path'],'line':i,'text':line})
    for name,got in hits.items():
        wanted=[json.loads(line) for line in raw(S+'/search-'+name+'.jsonl').decode().splitlines()]
        check(got==wanted,'search replay '+name)
    for x in doc(S+'/read-manifest.json'):
        b=raw(x['local']);lines=b.decode(errors='replace').splitlines();a,z=x['start'],x['end']
        check(sha(b)==x['sha256'],'read body '+x['local'])
        check(len(lines)==x['total_splitlines'] and b.count(b'\n')==x['total_LF_newlines'],'line conventions')
        check(1<=a<=z<=len(lines),'read range')
        check(sha(('\n'.join(lines[a-1:z])+'\n').encode())==x['passage_sha256'],'passage '+x['label'])
    pdfs=0
    for x in selected:
        if x['kind']=='outside_pdf':
            output=command(['pdftotext','-layout',x['original_local'],'-'])
            check(sha(output)==x['sha256'],'selected PDF replay '+x['path']);pdfs+=1
    requests=doc(S+'/external/requests.json')
    for x in requests:
        check('error' not in x,'primary download error')
        check(sha(raw(x['pdf']))==x['sha256'],'primary PDF '+x['name'])
        check(sha(raw(x['text']))==x['text_sha256'],'primary text '+x['name'])
        check(sha(command(['pdftotext','-layout',x['pdf'],'-']))==x['text_sha256'],'primary extraction '+x['name'])
    rendered=command(['pdftoppm','-f','254','-l','254','-scale-to','1500','-png','-singlefile',S+'/external/ranicki-topman.pdf'])
    check(rendered==raw(S+'/external/ranicki-page254.png'),'render replay')
    result=json.loads(command([sys.executable,'-B',E+'/diagnostics.py']))
    check(result==doc(E+'/diagnostic-results.json'),'diagnostic replay')
    check(not any('__pycache__' in p or p.endswith('.pyc') for p in files),'bytecode artifact')
    print(json.dumps({'status':'PASS','mode':'preseal' if preseal else 'final-seal',
                      'owned_files':len(files),'allowed_ledger_drift':drift,
                      'immutable_extra_references':len(refs),'original_blob_positions':len(domain),
                      'I14_originals':len(found),'outside_PDF_hash_bindings':776,
                      'selected_representations':len(selected),'selected_PDF_replays':pdfs,
                      'primary_PDF_replays':len(requests),'render_replays':1,
                      'read_records':len(doc(S+'/read-manifest.json')),
                      'search_counts':{name:len(h) for name,h in hits.items()},
                      'diagnostics':'PASS; finite only',
                      'limits':'No full-corpus semantic audit; 776 inherited PDFs hash-bound, only selected PDFs re-extracted; no independent proof/novelty certification.'},indent=2,sort_keys=True))

if __name__=='__main__': main()
