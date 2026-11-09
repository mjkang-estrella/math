"""Recover direct checker verdicts from their immutable completed stdout logs.
Run only after validators finish. Useful when independent validator batches wrote
the same checkpoint file from their own initial snapshots.
"""
import sys
sys.dont_write_bytecode=True
import os,json,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
fn=HERE/'checker_results.json';res=json.load(open(fn)) if fn.exists() else {}
for cert in (HERE/'certs').rglob('*.jsonl'):
    key=str(cert.relative_to(HERE));sha=hashlib.sha256(cert.read_bytes()).hexdigest()
    for checker in ['checkhd.py','v14_checknd_hd.py']:
        stem=Path(checker).stem;name=key.replace('/','__')+'.'+stem+'.log';log=HERE/'logs/checks'/name
        if not log.exists() or not log.read_text().rstrip().endswith('RESULT: PASS'):continue
        if res.get(key,{}).get(checker,{}).get('status')=='PASS' and res[key][checker]['sha256']==sha:continue
        source=HERE/checker if checker=='checkhd.py' else ROOT/'verification'/checker
        res.setdefault(key,{})[checker]={'status':'PASS','returncode':0,'sha256':sha,'log':str(log.relative_to(HERE)),
            'checker_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'recovered_from_direct_log':True}
tmp=fn.with_suffix('.tmp');tmp.write_text(json.dumps(res,indent=1)+'\n');os.replace(tmp,fn)
print('CHECKER VERDICTS',sum(len(x) for x in res.values()))
