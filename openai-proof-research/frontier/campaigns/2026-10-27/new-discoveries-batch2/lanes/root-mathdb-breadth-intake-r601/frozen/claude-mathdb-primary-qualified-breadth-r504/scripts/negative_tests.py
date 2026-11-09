# Bounded negatives on TEMP COPIES of this lane only (originals untouched). Prints JSON.
import json,os,shutil,subprocess,sys,tempfile,hashlib
L=os.path.realpath(sys.argv[1]); B=os.path.realpath(os.path.join(L,'../..'))
def run(d): 
    p=subprocess.run([sys.executable,'-B','-I',os.path.join(d,'verify.py'),d,B],capture_output=True,text=True)
    try: errs=json.loads(p.stdout)['errors']
    except Exception: errs=['unparsable']
    return p.returncode,errs
def case(name,mut):
    t=tempfile.mkdtemp(prefix='r504neg-'); d=os.path.join(t,'lane'); shutil.copytree(L,d)
    mut(d); rc,e=run(d); shutil.rmtree(t)
    return {'case':name,'exit':rc,'rejected':rc!=0,'first_errors':e[:2]}
def flip(d):
    p=os.path.join(d,'dispositions.json'); b=bytearray(open(p,'rb').read()); i=b.index(b'RETIRE'); b[i]=ord('X'); open(p,'wb').write(bytes(b))
def grow(d): open(os.path.join(d,'SUMMARY.md'),'ab').write(b'\n')
def extra(d): open(os.path.join(d,'runs','extra.txt'),'w').write('x')
def missing(d): os.remove(os.path.join(d,'coverage.json'))
def stmt(d):
    p=os.path.join(d,'dispositions.json'); x=json.load(open(p,encoding='utf-8')); x[0]['statement']+=' '
    s=json.dumps(x,ensure_ascii=False,indent=1,sort_keys=True)+'\n'; open(p,'w',encoding='utf-8').write(s)
    m=json.load(open(os.path.join(d,'manifest.json'))); b=s.encode('utf-8')
    for e in m['files']:
        if e['path']=='dispositions.json': e['sha256']=hashlib.sha256(b).hexdigest(); e['size']=len(b)
    json.dump(m,open(os.path.join(d,'manifest.json'),'w'),indent=1)
res=[case('positive_control_unmodified',lambda d:None),case('hash_same_size_byte_flip',flip),case('size_append',grow),
     case('extra_file',extra),case('missing_payload',missing),case('statement_tamper_with_consistent_manifest',stmt)]
ok=res[0]['exit']==0 and all(r['rejected'] for r in res[1:])
print(json.dumps({'negative_tests':res,'all_expected':ok},indent=1)); sys.exit(0 if ok else 1)
