import sys
sys.dont_write_bytecode=True
import os,json,hashlib,collections,itertools,math
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
sys.path.insert(0,str(HERE))
from inventory import enum_module
from breadth import atomic_json
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    final='--final' in sys.argv
    checks=json.load(open(HERE/'checker_results.json')) if (HERE/'checker_results.json').exists() else {}
    assignment=json.load(open(HERE/'assignment.json'));totals={};out={};problems=[];maxfloor=0
    # Recover independently checkpointed completions even if simultaneous batches wrote snapshots.
    recovered={32:{},14112:{}}
    for line in open(HERE/'history.jsonl'):
        h=json.loads(line);t=h['target'];k=h['key'];r=h['result']
        if r['status']=='CLOSED' or recovered[t].get(k,{}).get('status')!='CLOSED':recovered[t][k]=r
    files=sorted((HERE/'certs').rglob('*.jsonl'));meta={p:json.loads(p.open().readline()) for p in files}
    verified={p:all(checks.get(str(p.relative_to(HERE)),{}).get(c,{}).get('status')=='PASS'
        and checks[str(p.relative_to(HERE))][c]['sha256']==digest(p)
        for c in ('checkhd.py','v14_checknd_hd.py')) for p in files}
    if final:
        problems += ['unchecked '+str(p.relative_to(HERE)) for p in files if not verified[p]]
    for t in (32,14112):
        incoming=json.load(open(HERE/f'incoming_t{t}.json'));res=recovered[t]
        atomic_json(str(HERE/f'results_t{t}.json'),res)
        if final and set(res)!=set(incoming):problems.append(f'{t}: missing {set(incoming)-set(res)}')
        E=enum_module(t==32);records=[]
        for key,orig in incoming.items():
            r=res.get(key,{});status=r.get('status','NOT_ATTEMPTED');S=orig['S_low'];far=orig['far'];K0=9*S-1
            rec={'key':key,'status':status,'both_checkers':False,'slice_cover_ok':False,
                'stop_reason':r.get('stop_reason'),'budget':r.get('budget')}
            if status=='CLOSED':
                def fixed(K):
                    delta=K-K0
                    if delta<0 or delta%9:return None
                    ds=str(delta//9)[::-1]
                    f={p:9*int(d) for p,d in enumerate(ds) if d!='0'}
                    return None if any(p<3 or c==81 for p,c in f.items()) else f
                groups=collections.defaultdict(list)
                for p,m in meta.items():
                    if p.parent.name!=f't{t}':continue
                    cf=fixed(m['K'])
                    if cf is None or collections.Counter(cf.values())+collections.Counter(m['coefs'])!=collections.Counter(far):continue
                    groups[(m['K'],tuple(sorted(m['coefs'])))].append((p,m))
                covers=[]
                for (K,cs),vals in groups.items():
                    un=[(p,m) for p,m in vals if m.get('domain','ordered')=='unordered']
                    if un:
                        p,m=min(un,key=lambda x:x[1]['qmin']);covers.append((fixed(K),m['qmin'],{p}))
                    orders=[]
                    for od in set(itertools.permutations(cs)):
                        matches=[(p,m) for p,m in vals if m.get('domain','ordered')=='ordered' and tuple(m['coefs'])==od]
                        if not matches:break
                        orders.append(min(matches,key=lambda x:x[1]['qmin']))
                    else:covers.append((fixed(K),max(m['qmin'] for p,m in orders),{p for p,m in orders}))
                need=E.slices(K0,far);used=set();holes=[]
                for K,free,floor,_ in need:
                    maxfloor=max(maxfloor,floor);ef=fixed(K);assert ef is not None
                    for cf,fl,ps in covers:
                        if any(ef.get(p)!=c for p,c in cf.items()):continue
                        if any(p<fl for p in ef if p not in cf):continue
                        if free and floor<fl:continue
                        if not free and max(floor,max(ef,default=-1)+1)<fl:continue
                        used|=ps;break
                    else:holes.append([K,free,floor])
                rec.update(slice_cover_ok=not holes,both_checkers=all(verified[p] for p in used),holes=holes,
                    files=sorted(str(p.relative_to(HERE)) for p in used),independent_slice_count=len(need))
                rec['no_short_length_gap']=any(meta[p]['K']==K0 and sorted(meta[p]['coefs'])==far
                    and meta[p]['qmin']<=3 and meta[p].get('domain')=='unordered' for p in used)
                genuine=set()
                for p in used:
                    m=meta[p]
                    for line in p.open():
                        if '"sz"' not in line:continue
                        nd=json.loads(line)
                        for pt in nd.get('x',{}).get('sol',[]):
                            X=10**pt[0]+m['K']+sum(c*10**q for c,q in zip(m['coefs'],pt[1:]))
                            if X%9:continue
                            n=X//9;ds=str(n)[::-1]
                            if len(ds)!=pt[0] or math.prod(int(d) for d in ds)!=t:continue
                            s0=sum((int(d)-1)*10**i for i,d in enumerate(ds[:3]))
                            f0=sorted(9*(int(d)-1) for d in ds[3:] if d!='1')
                            if s0==S and f0==far:genuine.add(n)
                rec['certificate_members']=sorted(genuine)
                if holes:problems.append(f'{t} {key}: slice holes')
                if final and not rec['both_checkers']:problems.append(f'{t} {key}: unchecked closure')
            records.append(rec)
        totals[str(t)]={'assigned':len(incoming),'attempted':len(res),'closed':sum(r['status']=='CLOSED' for r in records),
            'checked_closed':sum(r['status']=='CLOSED' and r['both_checkers'] and r['slice_cover_ok'] for r in records),
            'still_open':sum(r['status']!='CLOSED' for r in records),'status_counts':dict(collections.Counter(r['status'] for r in records))}
        totals[str(t)]['certificate_members']=sorted({n for r in records for n in r.get('certificate_members',[])})
        out[str(t)]=records
    assert maxfloor<=600
    summary={'final':final,'coverage':totals,'configurations':out,'max_floor':maxfloor,
        'certificates':len(files),'both_checker_pass':sum(verified.values()),'problems':problems,
        'finite_region_sources':{n:digest(ROOT/'verification'/n) for n in ['indep2/e_brute_600.json','indep3/i3_brute_600.json']}}
    atomic_json(str(HERE/'coverage_summary.json'),summary)
    print(json.dumps({k:v for k,v in summary.items() if k!='configurations'},indent=2))
    if final and problems:sys.exit(1)
if __name__=='__main__':main()
