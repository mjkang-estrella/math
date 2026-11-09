"""Direct CLI replays, checkpointed; original F for all k<=3 certificates.

Optionally try the SAME tree at k=3. Successful downgrades get their own original
F replay and can replace deep certificates in coverage. A failed downgrade is
only evidence that this tree needs a deeper pin, not mathematical necessity.
"""
import sys
sys.dont_write_bytecode=True
import argparse
import collections
import concurrent.futures
import hashlib
import json
import pathlib
import subprocess
import time

H=pathlib.Path(__file__).resolve().parent
R=H.parents[2]
M=H.parent/'sym5/check_sym5.py'
F=R/'verification/indep4/check_sym_F.py'
F5=R/'verification/indep5/check_sym_F5.py'
BASELINE={}

def f5_ready():
    note=F5.parent/'NOTE_F5.md'
    if not F5.exists() or not note.exists(): return False
    text=note.read_text().lower()
    return 'test' in text and any(word in text for word in ('pass','passed','passing'))


def sha(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def load(p): return json.loads(pathlib.Path(p).read_text())
def save(p,v):
    t=p.with_suffix(p.suffix+'.tmp');t.write_text(json.dumps(v,indent=1)+'\n');t.replace(p)

def one(path,checker,brute,seconds):
    start=time.monotonic();before=sha(path);code=sha(checker)
    cmd=['bash','-c','ulimit -v 8000000; python3 -I -B "$@"','sym6-replay',str(checker),str(path),str(brute)]
    if checker in (F,F5): cmd.append('--json')
    try:
        p=subprocess.run(cmd,text=True,capture_output=True,timeout=seconds)
        out=json.loads(p.stdout.strip().splitlines()[-1])
        assert p.returncode==0 and out['result']=='PASS',(p.returncode,out,p.stderr[-500:])
        assert before==sha(path) and code==sha(checker),'input changed'
        result={'result':'PASS','check':out}
    except Exception as e: result={'result':'FAIL','error':repr(e)}
    result.update(sha256=before,checker_sha256=code,seconds=round(time.monotonic()-start,3),command=cmd)
    return result

def reusable(record,path,checker,brute):
    return (record.get('result')=='PASS' and record.get('sha256')==sha(path)
            and record.get('checker_sha256')==sha(checker)
            and int(record['command'][6])==brute)

def work(path,args,old):
    meta=json.loads(path.open().readline())
    inherited=BASELINE.get(str(path),{}).get('M',{})
    if (meta.get('pin_digits',0)<=3 and inherited.get('result')=='PASS'
        and inherited.get('sha256')==sha(path) and inherited.get('brute_Lmax',int(inherited['command'][6]))==args.brute
        and inherited.get('checker_sha256')==sha(inherited['command'][4])):
        rec={'M':dict(inherited,reused_from=str(H.parent/'sym4/dual_checks.json'))}
    elif reusable(old.get('M',{}),path,M,args.brute): rec={'M':old['M']}
    else: rec={'M':one(path,M,args.brute,args.seconds)}
    if meta.get('pin_digits',0)<=3:
        previous=BASELINE.get(str(path),{}).get('F',{})
        if (previous.get('result')=='PASS' and previous.get('sha256')==sha(path)
            and previous.get('checker_sha256')==sha(F) and previous.get('brute_Lmax',int(previous['command'][6]))==args.brute):
            # SYM5: an unchanged inherited certificate already passed this exact
            # unmodified CLI at the same brute bound. Preserve its full evidence.
            rec['F']=dict(previous,reused_from=str(H.parent/'sym4/dual_checks.json'))
        elif reusable(old.get('F',{}),path,F,args.brute): rec['F']=old['F']
        else: rec['F']=one(path,F,args.brute,args.seconds)
    elif f5_ready():
        rec['F5']=old['F5'] if reusable(old.get('F5',{}),path,F5,args.brute) else one(path,F5,args.brute,args.seconds)
    ab=old.get('downgrade',{})
    if ab.get('result')=='FAIL' and ab.get('M',{}).get('checker_sha256')==sha(M):
        rec['downgrade']=ab
    elif 'file' in ab and pathlib.Path(ab['file']).exists() and reusable(ab.get('M',{}),ab['file'],M,args.brute) and reusable(ab.get('F',{}),ab['file'],F,args.brute):
        rec['downgrade']=ab
    if args.downgrade and 'downgrade' not in rec and meta.get('pin_digits',0)>3 and rec['M']['result']=='PASS':
        text=path.read_text();header,tail=text.split('\n',1)
        meta['pin_digits']=3
        dest=H/'k3_certs'/(sha(path)+'.jsonl')
        dest.parent.mkdir(exist_ok=True)
        dest.write_text(json.dumps(meta,separators=(',',':'))+'\n'+tail)
        ab=one(dest,M,args.brute,args.seconds)
        if ab['result']=='PASS':
            rec['downgrade']={'file':str(dest),'M':ab,'F':one(dest,F,args.brute,args.seconds)}
        else:
            rec['downgrade']={'result':'FAIL','M':ab}
            dest.unlink()
    return rec

def main():
    global BASELINE
    ap=argparse.ArgumentParser()
    ap.add_argument('--workers',type=int,default=8)
    ap.add_argument('--seconds',type=int,default=180)
    ap.add_argument('--brute',type=int,default=10)
    ap.add_argument('--downgrade',action='store_true')
    args=ap.parse_args();assert 1<=args.workers<=10 and 0<args.seconds<1700
    BASELINE={}
    paths=set((H/'certs').rglob('*.jsonl'))
    for ledger in H.glob('search_*.json'):
        for row in load(ledger).values():
            paths.update(pathlib.Path(j['file']) for j in row['jobs'])
    deep=sorted(str(p) for p in paths if json.loads(p.open().readline()).get('pin_digits',0)>3)
    deep_set=set(deep)
    (H/'deep_pin_certs.txt').write_text(''.join(p+'\n' for p in deep))
    resultpath=H/'checks5.json'
    results=load(resultpath) if resultpath.exists() else {'files':{}}
    journal=H/'checks5_journal.jsonl'
    if journal.exists():
        data=journal.read_bytes()
        if data and not data.endswith(b'\n'):
            data=data[:data.rfind(b'\n')+1]
            journal.write_bytes(data)
        for line in data.splitlines():
            row=json.loads(line);results['files'][row['file']]=row['record']
    todo=[]
    for p in sorted(paths):
        old=results['files'].get(str(p),{})
        needed={'M':M}
        if str(p) not in deep_set:
            needed['F']=F
            inherited=BASELINE.get(str(p),{}).get('M',{})
            if (inherited.get('result')=='PASS' and inherited.get('sha256')==sha(p)
                and inherited.get('brute_Lmax',int(inherited['command'][6]))==args.brute
                and inherited.get('checker_sha256')==sha(inherited['command'][4])):
                needed['M']=pathlib.Path(inherited['command'][4])
        elif f5_ready(): needed['F5']=F5
        ab=old.get('downgrade',{})
        need_ablation=args.downgrade and str(p) in deep_set and (
            not ab or ('file' in ab and (not pathlib.Path(ab['file']).exists()
                or not reusable(ab.get('M',{}),ab['file'],M,args.brute)
                or not reusable(ab.get('F',{}),ab['file'],F,args.brute))))
        if any(old.get(w,{}).get('result')!='PASS' or old[w].get('sha256')!=sha(p)
               or old[w].get('checker_sha256')!=sha(c) or int(old[w]['command'][6])!=args.brute
               for w,c in needed.items()) or need_ablation:
            todo.append(p)
    print('paths',len(paths),'deep',len(deep),'pending',len(todo),'F5 exists',f5_ready(),flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool,journal.open('a') as log:
        fs={pool.submit(work,p,args,results['files'].get(str(p),{})):p for p in todo}
        for i,f in enumerate(concurrent.futures.as_completed(fs),1):
            p=fs[f];rec={**results['files'].get(str(p),{}),**f.result()};results['files'][str(p)]=rec
            log.write(json.dumps({'file':str(p),'record':rec},separators=(',',':'))+'\n');log.flush()
            if i%100==0: save(resultpath,results)
            if i%100==0 or any(v.get('result')=='FAIL' for w,v in rec.items() if w!='downgrade'):
                print(i,p.name,{w:v.get('result') for w,v in rec.items()},flush=True)
    results['counts']={w:dict(collections.Counter(v[w]['result'] for v in results['files'].values() if w in v)) for w in ('M','F','F5')}
    results['downgrades']=dict(collections.Counter(v['downgrade'].get('result','PASS') for v in results['files'].values() if 'downgrade' in v))
    results['F5_available']=f5_ready()
    note=F5.parent/'NOTE_F5.md'
    results['F5_readiness_note']={'path':str(note),'exists':note.exists(),
        'sha256':sha(note) if note.exists() else None,'text':note.read_text() if note.exists() else None}

    save(resultpath,results);print(json.dumps({k:v for k,v in results.items() if k!='files'}),flush=True)

if __name__=='__main__': main()
