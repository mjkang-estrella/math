import sys
sys.dont_write_bytecode=True
import json,hashlib,collections
from pathlib import Path
HERE=Path(__file__).resolve().parent
new={x[0] for x in json.load(open(HERE/'supply_scan.json'))['new_primes']}
stats={}
for p in sorted((HERE/'certs').rglob('*.jsonl')):
    h=hashlib.sha256();count=collections.Counter();primes=set();lifts=0;maxM=1
    with p.open('rb') as f:
        first=next(f);h.update(first);meta=json.loads(first)
        for line in f:
            h.update(line);n=json.loads(line);count[n['k']]+=1;maxM=max(maxM,n['m'])
            if n['k']=='i':
                lifts+=(n['m2']//n['m'])**meta['dim'];maxM=max(maxM,n['m2'])
                rp=n['rest'] or []
                if isinstance(rp,int):rp=[rp]
                primes.update(rp)
            else:
                assert set(n['x'])<= {'prime','sz','sol'}
                if 'prime' in n['x']:primes.add(n['x']['prime']);count['prime_leaves']+=1
                if 'sz' in n['x']:count['size_leaves']+=1;count['listed_solution_points']+=len(n['x']['sol'])
    stats[str(p.relative_to(HERE))]={'nodes':count['i']+count['l'],'certificate_lifts':lifts,'counts':dict(count),
        'maximum_modulus':maxM,'domain':meta['domain'],'qmin':meta['qmin'],'dim':meta['dim'],
        'sha256':h.hexdigest(),'listed_prime_witnesses':sorted(primes),'new_scan_primes_listed':sorted(primes&new)}
out={'certificates':stats,'total_nodes':sum(s['nodes'] for s in stats.values()),
     'total_certificate_lifts':sum(s['certificate_lifts'] for s in stats.values()),
     'new_scan_primes_listed':sorted({p for s in stats.values() for p in s['new_scan_primes_listed']})}
(HERE/'cert_stats.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='certificates'},indent=2))
