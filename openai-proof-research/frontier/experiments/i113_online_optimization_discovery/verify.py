"""I113 final verifier: offline and READ-ONLY, including imports.
No network, writes, bytecode, extraction, repair, manifest generation or sealing.
Only the four named live ledgers may drift. Their frozen snapshots may not.
Source identity and finite diagnostics do not certify universal proofs or novelty.
"""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import hashlib
import json
import re
import runpy
from collections import Counter

ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i113_online_optimization_discovery'
E='frontier/experiments/i113_online_optimization_discovery'
REPORT='frontier/iterations/i113-online-optimization-discovery.md'
SEAL=S+'/seal.json'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
DRIFT={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}

def require(condition, message):
    if not condition:raise ValueError(message)

def read(rel):
    p=Path(rel)
    require(not p.is_absolute() and '..' not in p.parts,'unsafe path: '+rel)
    p=ROOT/p
    require(p.is_file() and not p.is_symlink(),'missing/nonregular file: '+rel)
    return p.read_bytes()

def sha(b):return hashlib.sha256(b).hexdigest()
def obj(rel):return json.loads(read(rel))
def checked(rel,digest):
    b=read(rel)
    require(sha(b)==digest,'SHA-256 mismatch: '+rel)
    return b

def owned_paths():
    result={REPORT}
    for base in [S,E]:
        for p in (ROOT/base).rglob('*'):
            require(not p.is_symlink(),'owned symlink: '+str(p))
            if p.is_file():result.add(str(p.relative_to(ROOT)))
    return result

def validate_inventory(seal, allow_unsealed=False):
    require(seal['schema']=='i113-exact-owned-v1','seal schema')
    require(seal['pin']==PIN,'seal pin')
    require(seal['roots']==[REPORT,S+'/',E+'/'],'seal roots')
    items=seal['files']
    paths=[d['path'] for d in items]
    require(paths==sorted(set(paths)),'noncanonical inventory')
    expected=set(paths) if allow_unsealed else set(paths)|{SEAL}
    require(owned_paths()==expected,'owned inventory differs: '+str(sorted(owned_paths()^expected)))
    require(SEAL not in paths,'seal cannot hash itself')
    for d in items:
        b=checked(d['path'],d['sha256'])
        require(len(b)==d['bytes'],'owned byte count: '+d['path'])
    return {'owned_files_excluding_seal':len(paths),'seal_is_inventory_envelope':True}

def validate_core():
    results={}
    inputs=obj(S+'/inputs.json')
    require(len(inputs)==11,'input count')
    require({x['original'] for x in inputs if x['may_drift']}==DRIFT,'drift allowlist')
    changed=[]
    for d in inputs:
        checked(d['snapshot'],d['sha256'])
        if d['may_drift']:
            if sha(read(d['original']))!=d['sha256']:changed.append(d['original'])
        else:checked(d['original'],d['sha256'])
    require(obj('sources/upstream.json')['commit']==PIN,'upstream pin')
    results['snapshots']=len(inputs)
    results['allowed_live_ledger_drift']=sorted(changed)
    refs=obj(S+'/immutable-references.json')
    require(len(refs)==16,'immutable reference count')
    for d in refs:
        b=checked(d['path'],d['sha256'])
        require(len(b)==d['bytes'],'reference bytes: '+d['path'])
    results['immutable_reference_records']=len(refs)

    domain=obj(S+'/search-domain.json')
    require(domain==obj('frontier/sources/i88_nonlinear_banach_discovery/search-domain.json'),'I88 mapping identity')
    old=obj('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json')
    require([{k:d[k] for k in ('path','local','kind','sha256')} for d in domain]==old,'I79 representation map')
    tree=obj('sources/preprints-tree.json')
    require(not tree.get('truncated',False),'truncated tree')
    require(len(tree['tree'])==13223,'tree entry count')
    require(len({d['path'].split('/')[1] for d in tree['tree']})==749,'manuscript count')
    blobs={d['path']:d['sha'] for d in tree['tree'] if d['type']=='blob'}
    require(len(blobs)==10373,'blob count')
    require(len(domain)==10373 and {d['path'] for d in domain}==set(blobs),'full original position coverage')
    require(Counter(d['kind'] for d in domain)=={'corpus':9340,'outside_pdf':776,'outside_bytes':257},'representation counts')
    originals=set()
    for d in domain:
        b=checked(d['original_local'],d['original_sha256'])
        git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        require(git==d['git_sha']==blobs[d['path']],'Git blob identity: '+d['path'])
        if d['local']==d['original_local']:
            require(sha(b)==d['sha256'],'same-file representation identity')
        else:checked(d['local'],d['sha256'])
        originals.add(d['original_local'])
    require(len(originals)==10373,'one original path per position')
    corpus=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
    corpus_paths={str(p.relative_to(ROOT)) for p in corpus.rglob('*') if p.is_file()}
    require(corpus_paths=={d['original_local'] for d in domain if d['kind']=='corpus'},'ignored I14 inventory')
    results['corpus']={'tree_entries':13223,'manuscripts':749,'original_positions':10373,
                       'i14_originals':9340,'additional_originals':1033,'inherited_pdf_texts':776}
    selected=obj(S+'/selected-inventory.json')
    require(len(selected)==94,'selected count')
    mapped={d['path']:d for d in domain}
    for d in selected:
        require({k:v for k,v in d.items() if k!='url'}==mapped[d['path']],'selected mapping')
        require(d['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+d['path'],'pinned raw URL')
    require(len({d['path'] for d in selected})==94,'selected duplicates')
    results['selected_representations']=len(selected)

    queries=obj(S+'/queries.json')
    expected_queries={'scope':'prophet|k[ -]server|mean[ -]payoff|Blackwell|stochastic game',
        'robust':'misspecif|likelihood.ratio|inaccurate prior|contaminat|non.?identical sample|biased sample|robust prophet|distribution.shift'}
    require(queries['queries']==expected_queries,'exact lexical expressions')
    regex={k:re.compile(v,re.I) for k,v in expected_queries.items()}
    matches={k:[] for k in regex}
    for d in domain:
        lines=read(d['local']).decode('utf-8',errors='replace').splitlines()
        for i,line in enumerate(lines,1):
            for k,pattern in regex.items():
                if pattern.search(line):matches[k].append({'path':d['path'],'local':d['local'],'line':i,'text':line})
    for k,found in matches.items():
        saved=[json.loads(line) for line in read(S+'/search-'+k+'.jsonl').splitlines()]
        require(found==saved,'ordered matching-line multiset: '+k)
    require({k:len(v) for k,v in matches.items()}=={'scope':399,'robust':199},'lexical counts')
    results['lexical_matching_line_multisets']={k:len(v) for k,v in matches.items()}

    external=obj(S+'/external-manifest.json')
    responses=sorted((ROOT/S/'external').glob('*.response.json'))
    require(external==[json.loads(p.read_bytes()) for p in responses],'external response manifest')
    require(len(external)==8,'external original count')
    texts=0
    for d in external:
        require(d['status']==200,'external retrieval status')
        b=checked(d['path'],d['sha256'])
        require(len(b)==d['bytes'],'external original size')
        if 'text' in d:
            checked(d['text'],d['text_sha256']);texts+=1
    require(texts==3,'selective extraction count')
    results['new_external_originals']=len(external)
    results['new_pdf_texts']=texts
    reads=obj(S+'/read-manifest.json')['passages']
    require(len(reads)==32,'reading passage count')
    for d in reads:
        text=checked(d['path'],d['sha256']).decode('utf-8',errors='replace')
        require(d['line_convention'] in ('LF','splitlines'),'unknown line convention')
        lines=text.splitlines() if d['line_convention']=='splitlines' else text.split('\n')
        require(len(lines)==d['total_lines'],'reading line count')
        require(1<=d['start']<=d['end']<=len(lines),'reading range')
        require(sha('\n'.join(lines[d['start']-1:d['end']]).encode())==d['passage_sha256'],'reading passage hash')
    results['reading_passages']=len(reads)
    diagnostics=runpy.run_path(str(ROOT/E/'diagnostics.py'),run_name='i113_readonly_diagnostics')['run']()
    require(diagnostics==obj(E+'/diagnostics.json'),'deterministic diagnostics replay')
    results['diagnostics']=diagnostics
    return results

def main():
    # Verify executable/source inventory before running any owned diagnostic code.
    inventory=validate_inventory(obj(SEAL))
    core=validate_core()
    print(json.dumps({'status':'PASS','offline':True,'read_only':True,
        'certifies':'exact source/artifact identities and listed finite diagnostics only',
        'inventory':inventory,'validation':core},indent=2,sort_keys=True))

if __name__=='__main__':
    try:main()
    except Exception as e:
        print(json.dumps({'status':'FAIL','error':type(e).__name__+': '+str(e)},sort_keys=True))
        sys.exit(1)
