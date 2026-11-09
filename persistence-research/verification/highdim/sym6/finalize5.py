"""Hash-bound certificate inventory and independent low-position cover replay."""
import sys
sys.dont_write_bytecode=True
import collections
import hashlib
import json
import math
import pathlib
import time

H=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(H))
from audit_coverage import cover,finite_scan
from coverage_distinct import distinct_cover,position_cover

def load(p): return json.loads(pathlib.Path(p).read_text())
def sha(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def save(p,o):
    tmp=p.with_suffix(p.suffix+'.tmp');tmp.write_text(json.dumps(o,indent=1)+'\n');tmp.replace(p)

def main():
    assignment=load(H/'assignment.json')['configurations']
    checks=load(H/'checks5.json')
    original_F=H.parents[1]/'indep4/check_sym_F.py'
    assert original_F.exists()
    for file,digest in load(H/'source_hashes.json').items():
        assert sha(file)==digest,('modified original',file)
    pools={w:collections.defaultdict(list) for w in ('all','k3','independent')}
    evidence={};failed=[];pending=[];depths=collections.Counter()
    def register(path,meta,record,pool):
        cs=tuple(c for c,n in meta['groups'] for _ in range(n))
        pools[pool][(meta['K'],cs)].append((meta['qmin'],path))
        evidence[path]=(meta,record)
    def valid(path,record):
        if record.get('result')!='PASS': return False
        assert record['sha256']==sha(path),('changed cert',path)
        assert record['checker_sha256']==sha(record['command'][4]),('changed checker',path)
        return True
    for path,records in checks['files'].items():
        meta=json.loads(pathlib.Path(path).open().readline())
        if not valid(path,records.get('M',{})):
            failed.append(path);continue
        assert meta['format']=='nd-sym'
        if meta['scope']!='full': continue
        assert meta['root']['m']==1 and meta['root']['r']==[0]+[[0]*n for c,n in meta['groups']]
        assert meta.get('pin_digits',0)<=meta['qmin']
        depth=meta.get('pin_digits',0);depths[depth]+=1
        if depth>3 and checks.get('F5_available'):
            assert valid(path,records.get('F5',{})),('F5 failed',path)
            listed=records['F5']['check'].get('claimed',records['F5']['check'].get('solutions'))
            assert listed is not None and sorted(listed)==sorted(records['M']['check']['solutions'])

        if depth<=3:
            assert valid(path,records['F']),('original F failed',path)
            assert sorted(records['M']['check']['solutions'])==sorted(records['F']['check']['claimed'])
            register(path,meta,records['M']['check'],'all')
            register(path,meta,records['M']['check'],'k3')
            register(path,meta,records['M']['check'],'independent')
        else:
            ab=records.get('downgrade',{})
            if 'file' in ab and valid(ab['file'],ab['M']) and valid(ab['file'],ab['F']):
                legacy=ab['file'];m3=json.loads(pathlib.Path(legacy).open().readline())
                assert sorted(ab['M']['check']['solutions'])==sorted(ab['F']['check']['claimed'])==sorted(records['M']['check']['solutions'])
                assert sorted(ab['M']['check']['solutions'])==sorted(ab['F']['check']['claimed'])
                for pool in pools: register(legacy,m3,ab['M']['check'],pool)
            else:
                register(path,meta,records['M']['check'],'all')
                if 'F5' in records and valid(path,records['F5']):
                    # F5 may name its declarations 'claimed' or 'solutions'.
                    independent=records['F5']['check']
                    listed=independent.get('claimed',independent.get('solutions'))
                    if listed is not None: assert sorted(listed)==sorted(records['M']['check']['solutions'])
                    register(path,meta,records['M']['check'],'independent')
                else: pending.append(path)
    def coverage(initial,coefs,pool):
        errors=[]
        for method in (cover,distinct_cover,position_cover):
            try:
                out=method(initial,coefs,pools[pool])
                out.setdefault('coverage_method','original_enlarged_cover')
                return out
            except AssertionError as e: errors.append(str(e))
        return {'coverage_failures':errors}
    results={};selected=collections.defaultdict(dict);bound=2
    for name,rec in sorted(assignment.items()):
        initial=9*rec['S_low']-1
        c=coverage(initial,rec['far'],'all')
        k3=coverage(initial,rec['far'],'k3')
        ind=coverage(initial,rec['far'],'independent')
        closed='domains' in c
        c.update(status='CLOSED' if closed else 'OPEN',target=rec['target'],key=rec['key'],dim=len(rec['far'])+1,
                 legacy_only_cover='domains' in k3,independently_checked_cover='domains' in ind)
        if closed:
            # Prefer a wholly original-F-checked proof whenever one exists.
            if 'domains' in k3:
                c.update(k3);c['requires_deep_pin_in_retained_proof']=False
            else: c['requires_deep_pin_in_retained_proof']=True
            c['deep_domains']=[p for p in c['domains'] if evidence[p][0].get('pin_digits',0)>3]
            c['independent_pending_domains']=[p for p in c['deep_domains'] if p in pending]
            bound=max(bound,c['finite_Lmax']);selected[rec['target']][rec['key']]=rec
        results[name]=c
    finite=finite_scan(bound,selected)
    for name,row in results.items():
        if row['status']!='CLOSED': continue
        actual={v['member'] for v in finite['members'] if v['target']==row['target'] and v['key']==row['key']}
        for path in row['domains']:
            meta,check=evidence[path]
            cs=tuple(c for c,n in meta['groups'] for _ in range(n))
            for point in check['solutions']:
                X=10**point[0]+meta['K']+sum(c*10**q for c,q in zip(cs,point[1:]))
                assert X%9==0
                n=X//9;digits=str(n)
                low=sum((int(d)-1)*10**i for i,d in enumerate(digits[::-1][:3]))
                far=sorted(9*(int(d)-1) for d in digits[::-1][3:] if d!='1')
                if math.prod(map(int,digits))==row['target'] and str(low)+'|'+','.join(map(str,far))==row['key']:
                    actual.add(n)
        row['members']=sorted(actual)
        row['claim_label']='PROVED (generator-independent checker and complete cover)'
    counts={}
    for target in (111132,):
        counts[str(target)]={}
        for d in sorted({v['dim'] for v in results.values() if v['target']==target}):
            rows=[v for v in results.values() if v['target']==target and v['dim']==d]
            counts[str(target)][str(d)]={'assigned':len(rows),'closed':sum(v['status']=='CLOSED' for v in rows),
                                       'open':sum(v['status']=='OPEN' for v in rows),
                                       'deep_pin_closures':sum(v.get('requires_deep_pin_in_retained_proof',False) for v in rows),
                                       'independently_checked':sum(v['independently_checked_cover'] for v in rows)}
    stages={}
    attempted=set()
    for p in sorted(H.glob('search_*.json')):
        rows=load(p);attempted.update(rows)
        stages[p.name]={'attempts':len(rows),'statuses':dict(collections.Counter(r['status'] for r in rows.values())),
                        'worker_seconds':round(sum(r['seconds'] for r in rows.values()),3),
                        'reasons':dict(collections.Counter(r.get('reason',r['status']) for r in rows.values()))}
    assert attempted==set(assignment)
    expected=set(assignment)
    for stage in tuple(p.stem.removeprefix('search_') for p in sorted(H.glob('search_*.json'), key=lambda p: p.stat().st_mtime)):
        rows=load(H/('search_'+stage+'.json'))
        assert set(rows)==expected,('missing escalation',stage)
        assert all(results[k]['status']=='CLOSED' for k,r in rows.items() if r['status']=='COMPLETE_PENDING_CHECKS'),('complete candidate lost',stage)
        expected={k for k,r in rows.items() if r['status']!='COMPLETE_PENDING_CHECKS'}
    used=sorted({p for row in results.values() if row['status']=='CLOSED' for p in row['domains']})
    used_deep=[p for p in used if evidence[p][0].get('pin_digits',0)>3]
    (H/'closure_certs.txt').write_text(''.join(p+'\n' for p in used))
    (H/'closure_deep_pin_certs.txt').write_text(''.join(p+'\n' for p in used_deep))
    combined_F=collections.Counter(v['F']['result'] for v in checks['files'].values() if 'F' in v)
    combined_F.update(v['downgrade']['F']['result'] for v in checks['files'].values()
                      if 'F' in v.get('downgrade',{}))
    inherited_counts={w:sum('reused_from' in v.get(w,{}) for v in checks['files'].values()) for w in ('M','F')}
    out={'counts_by_target_dimension':counts,'closed':sorted(k for k,v in results.items() if v['status']=='CLOSED'),
         'open':sorted(k for k,v in results.items() if v['status']=='OPEN'),'configurations':results,
         'finite_exception_scan':finite,'checker_counts':checks['counts'],'original_F_including_downgrades':dict(combined_F),
         'downgrades':checks['downgrades'],
         'inherited_checker_passes':inherited_counts,
         'stages':stages,'failed_certificates':failed,'independent_pending_deep_certificates':pending,
         'depth_counts':dict(depths),'closure_certificates':len(used),'closure_deep_certificates':len(used_deep),
         'deep_pin_closures':sum(v.get('requires_deep_pin_in_retained_proof',False) for v in results.values()),
         'all_60_attempted':True,'all_unfinished_escalated':True,'F5_available':checks['F5_available'],
         'test_results':load(H/'test_results.json') if (H/'test_results.json').exists() else {},'source_hashes_verified':True,
         'certificate_sha256':{p:sha(p) for p in used}}
    from audit_orderings import main as orderings_main
    orderings_main()
    ordering=load(H/'ordering_audit.json')
    import continue_sym2 as driver
    driver.ORDERS={p:d for source in H.parent.glob('supply_*.json') for p,d,a,w in load(source)}
    driver.ORDERS.update({p:d for p,d,a,w in load(H/'supply.json')})
    kills={}
    for path,records in checks['files'].items():
        stat=driver.usage(path)
        stat['sha256']=sha(path)
        stat['checker_stats']={w:records[w]['check'].get('stats',{}) for w in ('M','F','F5') if records.get(w,{}).get('result')=='PASS'}
        stat['checker_kinds']={w:{k:records[w]['check'].get(k,{}) for k in ('kinds','ukinds')} for w in ('F','F5') if records.get(w,{}).get('result')=='PASS'}
        kills[path]=stat
        ab=records.get('downgrade',{})
        if 'file' in ab and ab.get('M',{}).get('result')=='PASS' and ab.get('F',{}).get('result')=='PASS':
            legacy=ab['file'];item=driver.usage(legacy);item['sha256']=sha(legacy)
            item['checker_stats']={w:ab[w]['check'].get('stats',{}) for w in ('M','F')}
            item['checker_kinds']={'F':{k:ab['F']['check'].get(k,{}) for k in ('kinds','ukinds')}}
            item['downgraded_from']=path
            kills[legacy]=item
    save(H/'kill_usage.json',kills)
    for name,row in results.items():
        row['k']=len(assignment[name]['far'])
        row['distinct_coefficient_orderings']=ordering['configurations'][name]['distinct_orderings']
        if row['status']=='CLOSED':
            row['kill_dependencies']=sorted({d for path in row['domains'] for d in driver.usage(path)['dependencies']})
    save(H/'coverage_audit.json',{'configurations':results,'complete':len(out['closed']),'incomplete':len(out['open']),
         'finite_exception_scan':finite,'ordering_result':ordering['result'],'total_distinct_orderings':ordering['total_distinct_orderings']})
    # Inventory all canonical v2 branches, even for configurations remaining open.
    from audit_coverage import v2_inventory
    inventories={}
    for name,rec in assignment.items():
        terminals,states=v2_inventory(9*rec['S_low']-1,rec['far'])
        inventories[name]={'states':states,'terminal_count':len(terminals),
          'terminals':[{'K':K,'coefs':list(cs),'qmin':q,'v2_K':(K & -K).bit_length()-1} for K,cs,q in terminals]}
    save(H/'v2_inventory.json',inventories)
    out['counts_by_k']={str(int(d)-1):row for d,row in counts['111132'].items()}
    out['ordering_result']=ordering['result']
    out['total_distinct_orderings']=ordering['total_distinct_orderings']
    out['kill_dependency_counts']=dict(collections.Counter(d for v in kills.values() for d in v['dependencies']))
    out['kill_reference_counts']=dict(sum((collections.Counter(v['reference_counts']) for v in kills.values()),collections.Counter()))
    save(H/'summary.json',out)
    print(json.dumps({k:out[k] for k in ('counts_by_target_dimension','checker_counts','downgrades','deep_pin_closures',
                                       'closure_certificates','closure_deep_certificates','finite_exception_scan','F5_available')}))

if __name__=='__main__':main()
