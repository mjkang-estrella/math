#!/usr/bin/env python3
"""Independently audit configuration -> nd-sym domain coverage and finite exceptions.
No imports from generator, checker, projection, or batch driver.
"""
import collections
import hashlib
import json
import math
import pathlib
import sys
sys.dont_write_bytecode=True
HERE=pathlib.Path(__file__).resolve().parent
HD=HERE.parent


def load(p): return json.loads(pathlib.Path(p).read_text())


def v2(n):
    return (n & -n).bit_length()-1


def cover(K,cs,available):
    # Split an offending coordinate into exact low positions and a high tail.
    # The whole unordered domain is included: labelling is arbitrary and includes
    # collisions during slicing. Free/fixed distinctness is intentionally relaxed.
    todo=[(K,tuple(cs),(3,)*len(cs))]
    visited=set(); used=set(); bound=2
    while todo:
        a,c,f=todo.pop()
        st=(a,c,f)
        if st in visited: continue
        visited.add(st)
        options=available.get((a,tuple(sorted(c))),[])
        if not options:
            # Every valid domain in this format requires q > v2(K).
            floor=max(3,v2(a)+1)
        else: floor=min(q for q,file in options)
        bound=max(bound,floor-1)
        if all(x>=floor for x in f):
            assert options,('missing domain',a,c,f)
            used.add(next(file for q,file in options if q==floor))
            continue
        # Follow the canonical coefficient order used to name the legacy slices.
        # Choosing a different elimination order yields a different valid cover,
        # whose constants need not occur among the legacy certificate domains.
        i=min(i for i,x in enumerate(f) if x<floor)
        high=list(f);high[i]=floor
        todo.append((a,c,tuple(high)))
        for q in range(f[i],floor):
            todo.append((a+c[i]*10**q,c[:i]+c[i+1:],f[:i]+f[i+1:]))
        assert len(visited)<3000000,'coverage state cap'
    return {'domain_count':len(used),'domains':sorted(used),'finite_Lmax':bound,'states':len(visited)}


def finite_scan(B,configs):
    found=[];count=0
    upper=10**B
    x=1
    while x<upper:
        y=x
        while y<upper:
            z=y
            while z<upper:
                count+=1
                digits=str(z)
                product=math.prod(map(int,digits))
                if product in configs:
                    S=sum((int(d)-1)*10**i for i,d in enumerate(digits[::-1][:3]))
                    far=tuple(sorted(9*(int(d)-1) for d in digits[::-1][3:] if d!='1'))
                    key=str(S)+'|'+','.join(map(str,far))
                    if key in configs[product]: found.append({'target':product,'member':z,'key':key})
                z*=7
            y*=3
        x*=2
    return {'label':'COMPUTED','Lmax':B,'smooth_points':count,'members':sorted(found,key=lambda x:x['member'])}


def main():
    cross=load(HERE/'cross_all.json')
    source_map=load(HERE/'crosscheck_sources.json')
    available=collections.defaultdict(list)
    evidence={}
    def register(file,check,sha=None):
        p=pathlib.Path(file)
        if not p.is_absolute(): p=HERE/p
        if sha is not None: assert hashlib.sha256(p.read_bytes()).hexdigest()==sha
        with p.open() as stream: meta=json.loads(next(stream))
        assert meta['format']=='nd-sym' and meta['scope']=='full' and check['scope']=='full'
        assert meta['K']==check['K'] and meta['groups']==check['groups']
        cs=tuple(c for c,n in meta['groups'] for _ in range(n))
        relative=str(p.relative_to(HERE))
        available[(meta['K'],cs)].append((meta['qmin'],relative))
        evidence[relative]=(meta,check)
        return meta
    for item in source_map['domains']:
        source=item['sources'][0]
        result=cross.get(source)
        if not result or result['status']!='CLOSED': continue
        meta=register(result['certificate'],result['check'],result['sha256'])
        assert meta['K']==item['K'] and meta['qmin']==item['qmin']
        assert tuple(c for c,n in meta['groups'] for _ in range(n))==tuple(item['coefs'])
    allconfigs={};bytarget={};B=2
    paths=[HD/'codex'/f'results_t{t}.json' for t in (16,24,32,14112)]+[HD/'results_t112.json']
    for path in paths:
        target=int(path.stem.split('t')[-1]);data=load(path)
        selected={k:v for k,v in data.items() if v['status']=='CLOSED'}
        bytarget[target]=selected
        for key,rec in selected.items():
            try:
                result=cover(9*rec['S_low']-1,rec['far'],available)
                result.update(label='PROVED',result='COVERED',target=target,key=key)
                B=max(B,result['finite_Lmax'])
            except AssertionError as e:
                result={'label':'COMPUTED','result':'MISSING','target':target,'key':key,'error':str(e)}
            allconfigs[f'{target}:{key}']=result
    # Add any newly completed attack covers as well; each certificate was fresh-checked.
    attacks={}
    for path in sorted(HERE.glob('attack_*.json')):
        for key,rec in load(path).items():
            if rec['status']=='SLICE_COVER_CHECKED': attacks[key]=rec
    standalone=HERE/'standalone_checks.json'
    if not standalone.exists():
        # Interim reporting only. Final counts use hash-bound standalone results.
        for key,rec in attacks.items():
            for job in rec['jobs']: register(job['file'],job['check'],job.get('sha256'))
    # Standalone replays can also recover a complete file written immediately
    # before its configuration's checker timer expired. Never promote a partial tree.
    if standalone.exists():
        for file,rec in load(standalone)['files'].items():
            if rec['result']!='PASS' or rec['check']['scope']!='full': continue
            register(file,rec['check'],rec['sha256'])
    original=load(HD/'codex/results_t14112.json')
    for key,rec in original.items():
        if rec['status']!='BUDGET' or not 6<=len(rec['far'])+1<=8: continue
        try:
            result=cover(9*rec['S_low']-1,rec['far'],available)
            result.update(label='PROVED',result='COVERED',target=14112,key=key)
            bytarget[14112][key]=rec
            B=max(B,result['finite_Lmax'])
        except AssertionError as e:
            result={'label':'COMPUTED','result':'BUDGET','target':14112,'key':key,'error':str(e)}
        allconfigs['new:14112:'+key]=result
    finite=finite_scan(B,bytarget)
    members=set()
    for record in finite['members']:
        members.add((record['target'],record['key'],record['member']))
    # Filter any solutions of the enlarged slice domains back to the original
    # decimal configuration. No size-leaf member is silently discarded.
    for rec in allconfigs.values():
        if rec['result']!='COVERED': continue
        actual=set()
        for file in rec['domains']:
            meta,check=evidence[file]
            cs=tuple(c for c,n in meta['groups'] for _ in range(n))
            for pt in check['solutions']:
                X=10**pt[0]+meta['K']+sum(c*10**q for c,q in zip(cs,pt[1:]))
                assert X%9==0
                n=X//9
                ds=str(n)
                if math.prod(map(int,ds))!=rec['target']: continue
                S=sum((int(d)-1)*10**i for i,d in enumerate(ds[::-1][:3]))
                far=sorted(9*(int(d)-1) for d in ds[::-1][3:] if d!='1')
                if str(S)+'|'+','.join(map(str,far))==rec['key']:
                    actual.add(n);members.add((rec['target'],rec['key'],n))
        actual.update(x['member'] for x in finite['members'] if x['target']==rec['target'] and x['key']==rec['key'])
        rec['members']=sorted(actual)
    output={'label':'COMPUTED','audit_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
            'legacy_source_count':source_map['source_count'],
            'legacy_unique_domains':source_map['unique_domains'],
            'legacy_domains_checked':sum(v['status']=='CLOSED' for v in cross.values()),
            'configurations':allconfigs,'coverage_counts':dict(collections.Counter(v['result'] for v in allconfigs.values())),
            'finite':finite,'members':[{'target':t,'key':k,'member':n} for t,k,n in sorted(members)]}
    (HERE/'coverage_audit.json').write_text(json.dumps(output,indent=1)+'\n')
    print(json.dumps({'label':'COMPUTED','coverage_counts':output['coverage_counts'],
                      'finite_Lmax':B,'finite_members':finite['members']}))

if __name__=='__main__':main()
