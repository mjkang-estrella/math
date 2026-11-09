import pathlib,json,hashlib,sys
D=pathlib.Path(sys.argv[1]); out={'sources':{},'raw':{},'extracted_consistency':{}}
for r in sorted((D/'sources').glob('*.receipt.json')):
    rec=json.loads(r.read_text()); f=D/'sources'/r.name[:-len('.receipt.json')]
    if 'sha256' in rec:
        ok=f.exists() and hashlib.sha256(f.read_bytes()).hexdigest()==rec['sha256']
        out['sources'][f.name]={'receipt_sha256':rec['sha256'],'match':ok,'status':rec.get('status')}
    else: out['sources'][f.name]={'error':rec.get('error'),'exists':f.exists()}
ex=json.loads((D/'extracted.json').read_text())
B=D.parents[1]
for i,o in ex.items():
    raw=(D/'raw'/f'{i}.jsonl').read_bytes(); pv=o['provenance']
    ch=pathlib.Path(pv['chunk']); data=ch.read_bytes()
    line=data.splitlines(keepends=True)[pv['line_one_based']-1]
    out['raw'][i]={'raw_hash_ok':hashlib.sha256(raw).hexdigest()==pv['raw_sha256'],'chunk_hash_ok':hashlib.sha256(data).hexdigest()==pv['chunk_sha256'],'line_equal':line==raw,
      'statement_ok':hashlib.sha256(json.loads(raw)['statement'].encode()).hexdigest()==pv['statement_sha256']}
# non-receipt source files
out['unreceipted']=[p.name for p in (D/'sources').iterdir() if not p.name.endswith('.receipt.json') and not (D/'sources'/(p.name+'.receipt.json')).exists()]
bad=[k for k,v in out['sources'].items() if v.get('match') is False]+[k for k,v in out['raw'].items() if not all(v.values())]
out['bad']=bad
print(json.dumps(out,indent=1))
