"""Run CaDiCaL on Ramsey cells. args: label tlimit_per_call spec... where spec=mode,H1,H2,n
Writes outputs/ramsey/<label>.jsonl ; keeps SAT witnesses (models) in outputs/ramsey/witness-*.txt"""
import sys,subprocess,json,os,time,pathlib
D=pathlib.Path(__file__).resolve().parents[1];C='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/cadical'
label,tl=sys.argv[1],int(sys.argv[2]);(D/'outputs/ramsey').mkdir(parents=True,exist_ok=True)
out=open(D/f'outputs/ramsey/{label}.jsonl','a')
for spec in sys.argv[3:]:
    mode,h1,h2,n=spec.split(',')
    cnf=D/f'tmp/{mode}_{h1}_{h2}_{n}.cnf'.replace(':','')
    g=subprocess.run([sys.executable,'-I',str(D/'scripts/ramsey_sat.py'),mode,h1,h2,n,str(cnf)],capture_output=True,text=True).stdout.strip()
    t=time.time();p=subprocess.run([C,'-t',str(tl),str(cnf)],capture_output=True,text=True);dt=time.time()-t
    st=[l for l in p.stdout.splitlines() if l.startswith('s ')]
    st=st[0] if st else 's UNKNOWN'
    rec=dict(spec=spec,result=st,seconds=round(dt,2),gen=g)
    if 'SATISFIABLE'==st[2:]:
        lits=[int(x) for l in p.stdout.splitlines() if l.startswith('v ') for x in l[2:].split()]
        w=D/f'outputs/ramsey/witness-{mode}-{h1}-{h2}-{n}.txt'.replace(':','')
        w.write_text(' '.join(str(x) for x in lits if x!=0)+'\n');rec['witness']=str(w.name)
    os.remove(cnf)
    print(json.dumps(rec),flush=True);out.write(json.dumps(rec)+'\n');out.flush()
