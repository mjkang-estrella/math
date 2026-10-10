#!/usr/bin/env python3
"""Offline READ-ONLY evidence replay. Never downloads, writes, repairs or reseals.

Use python -B. --preseal validates evidence before the one final seal exists;
normal mode requires that seal and exact owned inventory. Neither mode writes.
"""
import sys
sys.dont_write_bytecode = True
import os
import json
import re
import hashlib
import subprocess
import runpy
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
BASE = Path('frontier/sources/i105_chromatic_homotopy_discovery')
EXP = Path('frontier/experiments/i105_chromatic_homotopy_discovery')
REPORT = Path('frontier/iterations/i105-chromatic-homotopy-discovery.md')
SEAL = BASE/'seal.json'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
DRIFT = {'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
PDF_ARGS = ['pdftotext','-layout',str(ROOT/BASE/'external/bssw-v2.pdf'),'-']


def audit(event,args):
    if event == 'open':
        _,mode,flags = args
        if (mode and any(c in mode for c in 'wax+')) or (flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
            raise RuntimeError('Read-only verifier rejected file-write open')
    if event in {'os.remove','os.unlink','os.rename','os.rmdir','os.mkdir','os.chmod','os.chown','os.truncate','os.symlink','os.link','os.utime','os.system'}:
        raise RuntimeError('Read-only verifier rejected mutation: '+event)
    if event.startswith('socket.'):
        raise RuntimeError('Offline verifier rejected network operation')
    if event == 'subprocess.Popen' and list(args[1]) != PDF_ARGS:
        raise RuntimeError('Verifier permits only the one PDF-to-stdout extraction')
sys.addaudithook(audit)


def read(p):return (ROOT/p).read_bytes()
def sha(data):return hashlib.sha256(data).hexdigest()
def js(p):return json.loads(read(p))
def require(condition,message):
    if not condition:raise AssertionError(message)
def owned():
    out={str(REPORT)}
    for root in (BASE,EXP):
        for p in (ROOT/root).rglob('*'):
            require(not p.is_symlink(),'Owned symlink: '+str(p))
            if p.is_file():out.add(str(p.relative_to(ROOT)))
    return out


def main():
    require(sys.argv[1:] in ([],['--preseal']),'Only optional flag is --preseal')
    preseal=bool(sys.argv[1:])
    if preseal:
        require(not (ROOT/SEAL).exists(),'Preseal mode requires absent seal')
    else:
        seal=js(SEAL)
        require(seal['pin']==PIN,'Seal pin')
        require(owned()==set(seal['owned'])|{str(SEAL)},'Exact owned inventory')
        for p,h in seal['owned'].items():require(sha(read(p))==h,'Owned hash '+p)
        require(set(seal['driftable_live'])==DRIFT,'Drift allowlist')
    drift=[]
    for p in sorted((ROOT/BASE/'snapshots').rglob('*')):
        if not p.is_file():continue
        rel=str(p.relative_to(ROOT/BASE/'snapshots'))
        same=read(Path(rel))==p.read_bytes()
        if rel in DRIFT:
            if not same:drift.append(rel)
        else:require(same,'Immutable live reference changed: '+rel)
    require(js(BASE/'snapshots/sources/upstream.json')['commit']==PIN,'Upstream pin')
    tree=js(BASE/'snapshots/sources/preprints-tree.json')
    require(not tree['truncated'] and len(tree['tree'])==13223,'Complete tree')
    blobs={x['path']:x for x in tree['tree'] if x['type']=='blob'}
    domain=js(BASE/'search-domain.json')
    require(len(domain)==10373 and len({x['path'] for x in domain})==10373,'Unique domain')
    require(set(blobs)=={x['path'] for x in domain},'Full blob-position coverage')
    counts={k:sum(x['kind']==k for x in domain) for k in ('corpus','outside_pdf','outside_bytes')}
    require(counts=={'corpus':9340,'outside_pdf':776,'outside_bytes':257},'Domain kinds')
    queries=js(BASE/'queries.json')
    rx={k:re.compile(v,re.I) for k,v in queries.items()}
    hits={k:[] for k in rx}
    bypath={}
    for x in domain:
        require('i103_' not in x['local'] and 'i104_' not in x['local'],'Active reference')
        data=read(Path(x['original_local']))
        require(sha(data)==x['original_sha256'],'Original SHA256 '+x['path'])
        git=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        require(git==x['git_sha']==blobs[x['path']]['sha'],'Git blob '+x['path'])
        require(len(data)==blobs[x['path']]['size'],'Blob size '+x['path'])
        representation=read(Path(x['local']))
        require(sha(representation)==x['sha256'],'Representation SHA256 '+x['path'])
        for n,line in enumerate(representation.decode('utf-8',errors='replace').splitlines(),1):
            for name,pattern in rx.items():
                matches=[m.group(0) for m in pattern.finditer(line)]
                if matches:hits[name].append({'path':x['path'],'local':x['local'],'splitline':n,'text':line,'matches':matches})
        bypath[x['path']]=x
    for name,rows in hits.items():
        saved=[json.loads(line) for line in read(BASE/('search-'+name+'.jsonl')).decode().splitlines()]
        require(rows==saved,'Exact lexical occurrence sequence/multiset '+name)
    selected=js(BASE/'selected-inventory.json')
    for x in selected:
        require({k:v for k,v in x.items() if k!='url'}==bypath[x['path']],'Selected inventory')
        require(x['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+x['path'],'Pinned URL')
    screen=js(BASE/'title-screen.json')
    titles=sorted({x['path'].split('/')[1] for x in tree['tree']})
    require(len(titles)==749 and titles==screen['all_titles'],'Exact title inventory')
    require(screen['selected_titles']==[t for t in titles if any(t.startswith(p) for p in screen['selected_prefixes'])],'Title screen')
    for x in js(BASE/'passages.json'):
        data=read(Path(x['local']));s=data.decode('utf-8');lines=s.split('\n')
        require(sha(data)==x['source_sha256'],'Passage source hash')
        require(len(lines)==x['LF_fields'] and len(s.splitlines())==x['splitlines_count'],'Line convention counts')
        start,end=x['LF_start'],x['LF_end']
        part='\n'.join(lines[start-1:end])
        require(part==x['text'] and sha(part.encode())==x['text_sha256'],'Exact passage')
        beg=sum(len(l)+1 for l in lines[:start-1]);fin=beg+len(part);offset=0;covered=[]
        for i,line in enumerate(s.splitlines(keepends=True),1):
            if offset<fin and offset+len(line)>beg:covered.append(i)
            offset+=len(line)
        require([min(covered),max(covered)]==x['splitlines_containing_range'],'LF versus splitlines map')
        require(re.findall(r'\\label\{([^}]+)\}',part)==x['labels'],'Exact source labels')
    for p in (ROOT/BASE/'external').glob('*.response.json'):
        r=json.loads(p.read_bytes())
        if r.get('status')==200:
            require(sha(read(Path(r['local'])))==r['sha256'],'External response hash')
        else:
            require('error' in r and not (ROOT/r['local']).exists(),'Retain failed retrieval without invented artifact')
    result=subprocess.run(PDF_ARGS,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
    require(result.stdout==read(BASE/'external/bssw-v2.txt'),'One selective PDF extraction')
    diag=runpy.run_path(str(ROOT/EXP/'diagnostics.py'))['run']()
    print(json.dumps({'status':'PRESEAL PASS' if preseal else 'PASS','original_positions':len(domain),'kinds':counts,
                      'lexical_matching_lines':{k:len(v) for k,v in hits.items()},'selected_files':len(selected),
                      'read_passages':len(js(BASE/'passages.json')),'drifted_live_ledgers':drift,'diagnostics':diag,
                      'scope':'Evidence identity and finite diagnostics only; no universal proof or contribution certification.'},sort_keys=True))

if __name__=='__main__':main()
