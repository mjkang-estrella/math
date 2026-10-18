import hashlib, json, os, pathlib, shutil, subprocess, sys
SRC=pathlib.Path(sys.argv[1]); ANCHOR=sys.argv[2]; WORK=pathlib.Path(sys.argv[3])
def tree_digest(root):
    h=hashlib.sha256()
    for dp,dn,fn in sorted(os.walk(root)):
        dn.sort()
        rel=os.path.relpath(dp,root); h.update(b'D'+rel.encode()+b'\0')
        for f in sorted(fn):
            p=os.path.join(dp,f); st=os.lstat(p)
            h.update(b'F'+os.path.relpath(p,root).encode()+b'\0'+str(st.st_mode).encode()+b'\0'+hashlib.sha256(open(p,'rb').read()).digest())
    return h.hexdigest()
before=tree_digest(SRC)
if WORK.exists(): shutil.rmtree(WORK)
WORK.mkdir(parents=True)
def fresh(name):
    d=WORK/name/'pkt'; shutil.copytree(SRC,d,symlinks=True); return d
def run(root,anchor,verifier=None):
    v=verifier or (root/'verify.py')
    r=subprocess.run([sys.executable,str(v),'--root',str(root),'--anchor',anchor],capture_output=True,text=True)
    return r.returncode,(r.stdout+r.stderr).strip()
res=[]
def case(name,expect,root,anchor=ANCHOR,verifier=None):
    rc,out=run(root,anchor,verifier)
    ok=(rc==0)==(expect=='PASS') and (expect=='PASS' or out.startswith('REJECT'))
    res.append({'case':name,'expected':expect,'exit_code':rc,'matched':ok,'output':out[:300]})
d=fresh('positive'); case('positive','PASS',d)
d=fresh('wrong_anchor'); case('wrong_anchor','REJECT',d,anchor='0'*64)
d=fresh('malformed_anchor'); case('malformed_anchor','REJECT',d,anchor='xyz')
d=fresh('changed'); p=d/'public/article.tex'; p.write_bytes(p.read_bytes()+b'%')
case('changed_file','REJECT',d)
d=fresh('missing'); (d/'validation/toolchain.json').unlink(); case('missing_file','REJECT',d)
d=fresh('extra'); (d/'public/extra.txt').write_text('x'); case('extra_file','REJECT',d)
d=fresh('extra_dir'); (d/'public/newdir').mkdir(); case('extra_empty_dir','REJECT',d)
d=fresh('missing_dir'); shutil.rmtree(d/'development/build-01'); case('missing_dir_with_files','REJECT',d)
d=fresh('symlink_file'); p=d/'public/README.md'; data=p.read_bytes(); p.unlink(); (d/'rd').write_bytes(data); os.symlink(d/'rd',p)
case('symlink_file','REJECT',d)
d=fresh('symlink_root'); link=WORK/'symlink_root'/'link'; os.symlink(d,link); case('symlink_root','REJECT',link,verifier=d/'verify.py')
d=fresh('symlink_ancestor'); anc=WORK/'symlink_ancestor'/'anc'; os.symlink(WORK/'symlink_ancestor',anc); case('symlink_ancestor','REJECT',anc/'pkt',verifier=d/'verify.py')
d=fresh('hardlink'); os.link(d/'README.md',d/'public'/'hl.md'); 
# replace an existing file by a hardlink to keep inventory equal
(d/'public'/'hl.md').unlink(); tgt=d/'validation/article.txt'; os.link(tgt, WORK/'hardlink'/'outside-link'); case('hardlink_existing_file','REJECT',d)
d=fresh('fifo'); p=d/'validation/toolchain.json'; p.unlink(); os.mkfifo(p); case('fifo_replacing_file','REJECT',d)
d=fresh('fifo_extra'); os.mkfifo(d/'public/fifo'); case('fifo_extra','REJECT',d)
d=fresh('remanifest'); p=d/'public/article.tex'; p.write_bytes(p.read_bytes()+b'%')
m=json.loads((d/'MANIFEST.json').read_text())
def fix(o):
    if isinstance(o,dict):
        if o.get('path')=='public/article.tex':
            b=p.read_bytes(); 
            for k in list(o):
                if 'sha' in k: o[k]=hashlib.sha256(b).hexdigest()
                if k in ('bytes','size'): o[k]=len(b)
        for v in o.values(): fix(v)
    elif isinstance(o,list):
        for v in o: fix(v)
fix(m)
if isinstance(m.get('files'),dict) and 'public/article.tex' in m['files']:
    b=p.read_bytes(); m['files']['public/article.tex']={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
(d/'MANIFEST.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
case('recomputed_manifest_old_anchor','REJECT',d)
newa=hashlib.sha256((d/'MANIFEST.json').read_bytes()).hexdigest()
case('recomputed_manifest_new_anchor_positive_control','PASS',d,anchor=newa)
after=tree_digest(SRC)
print(json.dumps({'source':str(SRC),'anchor':ANCHOR,'source_tree_digest_before':before,'source_tree_digest_after':after,'source_unchanged':before==after,'all_matched':all(r['matched'] for r in res),'results':res},indent=1))
