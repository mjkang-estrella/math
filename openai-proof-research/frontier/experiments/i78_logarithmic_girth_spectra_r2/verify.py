#!/usr/bin/env python3
"""Offline, read-only evidence/finite verifier. Analytic verdict is in the review."""
import sys
sys.dont_write_bytecode = True
import hashlib
import json
import os
import re
import subprocess
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
S = ROOT/'frontier/sources/i78_logarithmic_girth_spectra_r2'
E = ROOT/'frontier/experiments/i78_logarithmic_girth_spectra_r2'
REPORT = 'frontier/reviews/i78-logarithmic-girth-spectra-r2.md'
LEDGERS = {'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
EXCLUSIONS = {'frontier/sources/i78_logarithmic_girth_spectra_r2/seal-v1.json',
              'frontier/experiments/i78_logarithmic_girth_spectra_r2/verification.json'}

def sha(b): return hashlib.sha256(b).hexdigest()
def read(p): return json.loads(p.read_text())
def check(ok,msg):
    if not ok: raise AssertionError(msg)
def run(args):
    env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    return subprocess.run(args,cwd=ROOT,env=env,capture_output=True)
def without_drift(x):
    if isinstance(x,dict): return {k:without_drift(v) for k,v in x.items() if k!='mutable_ledger_drift'}
    if isinstance(x,list): return [without_drift(v) for v in x]
    return x


def audit(sealed=True):
    count=None
    if sealed:
        seal=read(S/'seal-v1.json')
        check(set(seal['mutable_ledgers'])==LEDGERS,'exact mutable ledger allowlist')
        check(set(seal['exclusions'])==EXCLUSIONS,'exact exclusions')
        domain={REPORT}|{str(p.relative_to(ROOT)) for base in (S,E) for p in base.rglob('*') if p.is_file()}
        check(domain-EXCLUSIONS=={x['path'] for x in seal['artifacts']},'owned artifact domain')
        for x in seal['artifacts']:
            b=(ROOT/x['path']).read_bytes()
            check(len(b)==x['bytes'] and sha(b)==x['sha256'],'sealed artifact '+x['path'])
        count=len(seal['artifacts'])
    refs=read(S/'references.json')
    drift=[]
    check({x['path'] for x in refs if x['mutable']}==LEDGERS,'reference mutable allowlist')
    for x in refs:
        check(x['mutable']==(x['path'] in LEDGERS),'mutability '+x['path'])
        b=(ROOT/x['path']).read_bytes()
        good=(len(b)==x['bytes'] and sha(b)==x['sha256'])
        if x['mutable']:
            if not good: drift.append(x['path'])
        else: check(good,'immutable reference '+x['path'])
    brief=(S/'full-brief.txt').read_text()
    prov=read(S/'brief-provenance.json')
    check(len(brief.encode('utf-16-le'))//2==prov['utf16Length']+int(prov['fileFinalNewlineAdded']),'full brief UTF16 length')
    for name in ['i72-graph-probability-discovery','i76-logarithmic-girth-spectra']:
        check((ROOT/f'frontier/iterations/{name}.md').read_text().rstrip('\n') in brief,'original report embedded '+name)
    passages=read(S/'audit-passages.json')
    for x in passages:
        b=b''.join((ROOT/x['path']).read_bytes().splitlines(keepends=True)[x['first_line']-1:x['last_line']])
        check(sha(b)==x['slice_sha256'],'exact passage '+x['id'])
    searches={}
    for name in ['interface-search.json','clean-spectral-search.json']:
        x=read(S/name); rx=re.compile(x['pattern']);hits=[]
        check(x['exit_code']==0 and not x['stderr'],'original search succeeded '+name)
        for p in x['domain']:
            for i,line in enumerate((ROOT/p).read_text().splitlines(),1):
                if rx.search(line): hits.append((p,i,line))
        check(Counter(hits)==Counter(map(tuple,x['hits'])),'fixed-domain line multiset '+name)
        searches[name]=len(hits)
    requests=read(S/'fresh-requests.json')
    for x in requests:
        check(x['status']==200,'original request status '+x['name'])
        b=(ROOT/x['body']).read_bytes()
        check(len(b)==x['bytes'] and sha(b)==x['sha256'],'request body '+x['name'])
        check(sha((ROOT/x['headers']).read_bytes())==x['headers_sha256'],'request headers '+x['name'])
    html=(S/'responses/hy-current.html').read_text()
    history=html[html.index('Submission history'):html.index('<!--end leftcolumn-->')]
    check(re.findall(r'\[v(\d+)\]',history)==['1','2','3'],'captured latest HY version')
    check('Sun, 2 Feb 2025 22:37:48 UTC' in history and '<strong>[v3]</strong>' in history,'HY current revision binding')
    primary=ROOT/'frontier/sources/i72_graph_probability_discovery/primary'
    for new,old in [('hy-official-v3.pdf','hy-v3'),('mww-author.pdf','mww')]:
        pdf=S/'responses'/new
        check(pdf.read_bytes()==(primary/(old+'.pdf')).read_bytes(),'fresh PDF byte identity '+new)
        result=run(['pdftotext','-layout',str(pdf),'-'])
        check(result.returncode==0 and result.stdout==(primary/(old+'.txt')).read_bytes(),'PDF extraction replay '+new)
    old=run([sys.executable,'-B','frontier/experiments/i76_logarithmic_girth_spectra/verify.py'])
    check(old.returncode==0,'existing verifier failed: '+old.stdout.decode()+old.stderr.decode())
    oldresult=json.loads(old.stdout)
    check(without_drift(oldresult)==without_drift(read(E/'i76-replay.stdout.json')),'old replay differs beyond mutable ledger drift')
    check(not (E/'i76-replay.stderr.txt').read_bytes(),'retained successful replay stderr')
    parent=read(ROOT/'frontier/experiments/i76-parent-verification.json')
    check(parent['exit_code']==0 and parent['result']['status']==oldresult['status'],'finalized I76 parent verification')
    diagnostic=run([sys.executable,'-B',str(E/'diagnostics.py')])
    check(diagnostic.returncode==0,'independent diagnostics failed: '+diagnostic.stderr.decode())
    check(json.loads(diagnostic.stdout)==read(E/'diagnostics-v1.stdout.json'),'exact finite JSON replay')
    check((E/'diagnostics.py').read_bytes()==(E/'diagnostics-v1.py').read_bytes(),'first diagnostic version unchanged')
    check(not (E/'diagnostics-v1.stderr.txt').read_bytes(),'first diagnostic stderr empty')
    return dict(status='PASS_EVIDENCE_AND_FINITE_DIAGNOSTICS' if sealed else 'PASS_UNSEALED_PREFLIGHT_ONLY',
        read_only=True,sealed_artifacts=count,reference_files=len(refs),passages=len(passages),
        search_line_multisets=searches,fresh_requests=len(requests),pdf_replays=2,
        current_HY_capture_version='v3',mutable_ledger_drift=drift,
        prior_replay=oldresult,independent_finite_diagnostics='exact first-version JSON reproduced',
        analytic_status='See I78 review: original A, B, and used I72 lemmas PASS under stipulated premises; this program is not an analytic proof certificate.',
        contribution_status='Not assessed; no acceptance or count change.')

if __name__=='__main__':
    try:
        print(json.dumps(audit(),indent=2,sort_keys=True))
    except Exception as e:
        print(json.dumps({'status':'FAIL','error':str(e)},indent=2))
        sys.exit(1)
