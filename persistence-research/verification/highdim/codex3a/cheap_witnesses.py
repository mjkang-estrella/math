"""Add small aligned ordinary-prime alternatives, preserving every original witness.
This changes no domain, partition, node, leaf, or checker acceptance rule.
Both full checkers must then replay the resulting certificate from scratch.
"""
import sys
sys.dont_write_bytecode=True
import os,json,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent
WITNESSES=[(757,27),(1009,252),(10837,63),(1933,21)]
def main():
    summaryfn=HERE/'cheap_witnesses_summary.json'
    summary=json.load(open(summaryfn)) if summaryfn.exists() else []
    for path in (HERE/'certs').rglob('*.jsonl'):
        if len(sys.argv)>1 and sys.argv[1] not in str(path):continue
        with path.open() as f:first=json.loads(next(f))
        if first.get('small_aligned_prime_alternatives')==[list(x) for x in WITNESSES]:continue
        before=hashlib.sha256(path.read_bytes()).hexdigest();changed=0;tmp=path.with_suffix('.tmp')
        with path.open() as fi,tmp.open('w') as fo:
            meta=json.loads(next(fi));meta['small_aligned_prime_alternatives']=WITNESSES
            fo.write(json.dumps(meta)+'\n')
            for line in fi:
                n=json.loads(line)
                if n['k']=='i':
                    pref=[p for p,d in WITNESSES if n['m2']%d==0 and n['m']%d!=0]
                    if pref:
                        old=n['rest'] or []
                        if isinstance(old,int):old=[old]
                        n['rest']=pref+[p for p in old if p not in pref];changed+=1
                        assert set(old)<=set(n['rest'])
                fo.write(json.dumps(n,separators=(',',':'))+'\n')
        os.replace(tmp,path)
        summary.append({'file':str(path.relative_to(HERE)),'before':before,'after':hashlib.sha256(path.read_bytes()).hexdigest(),
                        'nodes_with_added_alternatives':changed})
    summaryfn.write_text(json.dumps(summary,indent=2)+'\n')
    print(summary)
if __name__=='__main__':main()
