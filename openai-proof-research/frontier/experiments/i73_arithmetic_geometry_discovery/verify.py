#!/usr/bin/env python3
"""Offline, read-only I73 evidence replay. Does not certify open mathematics."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import hashlib, json, subprocess, re, runpy
from collections import Counter

ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i73_arithmetic_geometry_discovery'
E=ROOT/'frontier/experiments/i73_arithmetic_geometry_discovery'
C=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
MUTABLE={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
sha=lambda b:hashlib.sha256(b).hexdigest()
blob=lambda b:hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def read(p):return json.loads(p.read_text())
def need(value,message):
    if not value:raise AssertionError(message)
def run(preflight=False):
    out={'mathematics':'C73-M, C73-D, S73 and H73 remain unproved; no substantial finding nominated','mutable_ledger_drift':[]}
    if not preflight:
        seal=read(S/'seal-v1.json')
        for r in seal['files']:
            p=ROOT/r['path'];need(p.is_file(),'missing sealed file '+r['path']);b=p.read_bytes()
            need(len(b)==r['bytes'] and sha(b)==r['sha256'],'seal mismatch '+r['path'])
        out['sealed_files']=len(seal['files'])
    inputs=read(S/'inputs.json')
    need({r['path'] for r in inputs if r['mutable']}==MUTABLE,'mutable ledger set')
    for r in inputs:
        need(sha((S/'inputs'/r['path']).read_bytes())==r['sha256'],'frozen input '+r['path'])
        same=sha((ROOT/r['path']).read_bytes())==r['sha256']
        if r['mutable']:
            if not same:out['mutable_ledger_drift'].append(r['path'])
        else:need(same,'immutable input drift '+r['path'])
    out['frozen_inputs']=len(inputs)
    refs=read(S/'prior-references.json')
    for r in refs:need(sha((ROOT/r['path']).read_bytes())==r['sha256'],'old immutable reference drift '+r['path'])
    out['prior_references']=len(refs)
    T=read(S/'inputs/sources/preprints-tree.json')['tree'];tb={r['path']:r for r in T if r['type']=='blob'}
    need((len(T),sum(r['type']=='tree' and r['path'].count('/')==1 for r in T),len(tb))==(13223,749,10373),'full tree counts')
    inventory=read(S/'corpus.json');actual=subprocess.check_output(['rg','--files','--no-ignore',str(C)],text=True)
    paths=[str(Path(x).relative_to(C)) for x in actual.splitlines()]
    need(Counter(paths)==Counter(r['path'] for r in inventory),'fixed corpus domain')
    for r in inventory:
        b=(C/r['path']).read_bytes();need(sha(b)==r['sha256'],'corpus hash '+r['path'])
        need(blob(b)==tb[r['path']]['sha'],'corpus Git blob '+r['path'])
    other=read(S/'other-tree-blobs.json');expected=[r for r in T if r['type']=='blob' and r['path'] not in set(paths)]
    need(other==expected and len(other)==1033,'separate other blobs')
    out['tree_entries']=len(T);out['corpus_files']=len(paths);out['other_tree_blobs']=len(other)
    pins=read(S/'pinned.json')
    for r in pins:
        b=(S/'pinned'/r['path']).read_bytes();need(sha(b)==r['sha256'] and blob(b)==r['blob']==tb[r['path']]['sha'],'pinned blob '+r['path'])
        need(r['raw_url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+r['path'],'pinned raw URL')
    out['pinned_text_files']=len(pins)
    for q in read(S/'searches.json'):
        proc=subprocess.run(['rg','--no-ignore','--line-number','--no-heading','--color','never','-i',q['pattern'],str(C)],capture_output=True,text=True)
        need(proc.returncode in [0,1],proc.stderr)
        lines=proc.stdout.replace(str(C)+'/', '').splitlines()
        need(Counter(lines)==Counter(read(S/q['file'])),'search line multiset '+q['key'])
    out['fixed_domain_searches']=len(read(S/'searches.json'))
    passages=read(S/'passages.json')
    for r in passages:
        lines=(S/r['path']).read_text().splitlines(keepends=True)
        b=''.join(lines[r['start']-1:r['end']]).encode()
        need(sha(b)==r['sha256'],'exact passage '+r['path'])
    out['passages']=len(passages)
    versions=read(S/'version-comparisons.json')
    for r in versions:need(((S/r['old']).read_bytes()==(S/r['new']).read_bytes())==r['identical'],'old/new TeX comparison')
    need(sum(r['identical'] for r in versions)==44 and len(versions)==48,'version counts')
    out['old_new_TeX_pairs']=len(versions)
    request_log=read(S/'primary/requests.json');pdfs=0;raws=0
    for r in request_log:
        if 'failure' in r:continue
        p=S/r['file'];b=p.read_bytes();need(sha(b)==r['sha256'],'response hash '+r['key'])
        need(r['status']==200,'unexpected response '+r['key'])
        if p.suffix=='.pdf':
            z=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True)
            need(z.returncode==r['extraction_returncode']==0,'PDF extraction '+r['key'])
            need(z.stdout==p.with_suffix('.txt').read_bytes(),'PDF text replay '+r['key']);pdfs+=1
        if r['key'].startswith('pin-'):
            f=r['url'].split('fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/')[1]
            need(b==(S/'pinned'/f).read_bytes(),'fresh raw pin '+r['key']);raws+=1
    out['successful_requests']=sum('failure' not in r for r in request_log);out['preserved_request_failures']=sum('failure' in r for r in request_log)
    out['PDF_text_replays']=pdfs;out['fresh_raw_pin_comparisons']=raws
    for r in read(S/'primary/versions.json'):
        s=(S/r['abs_file']).read_text();og=re.search(r'<meta property="og:url" content="([^"]+)',s)
        need(og and og.group(1)==r['captured_current_url'],'captured version URL')
        need(re.findall(r'<strong>(?:<a[^>]*>)?\[v(\d+)\]',s)==r['history_versions'],'captured version history')
    actual=runpy.run_path(str(E/'diagnostics.py'))['run']()
    need(actual==read(E/'diagnostics.json'),'finite diagnostic replay')
    out['finite_diagnostics']=actual['status'];out['status']='PREFLIGHT_PASS' if preflight else 'PASS_PROVENANCE_AND_FINITE_INTERFACES'
    return out
if __name__=='__main__':
    try:print(json.dumps(run('--preflight' in sys.argv),indent=2,sort_keys=True))
    except Exception as error:
        print(json.dumps({'status':'FAIL','error':str(error)},indent=2));sys.exit(1)
