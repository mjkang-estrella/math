# Bounded negative tests: copy the lane (excluding scratch) to LANE/.negtest-scratch/lane, tamper, expect verify.py nonzero; then delete scratch.
import json,os,shutil,subprocess,sys
B=os.path.realpath(sys.argv[1]); ME=os.path.join(B,'lanes','claude-mathdb-primary-qualified-breadth-r602')
SC=os.path.join(ME,'.negtest-scratch'); C=os.path.join(SC,'lane')
def fresh():
    if os.path.exists(SC): shutil.rmtree(SC)
    shutil.copytree(ME,C,ignore=shutil.ignore_patterns('.negtest-scratch'))
def run():
    p=subprocess.run([sys.executable,'-B',os.path.join(C,'verify.py'),B,C],capture_output=True,text=True,timeout=200)
    try: errs=json.loads(p.stdout)['errors']
    except Exception: errs=['unparsable']
    return p.returncode,errs[:3]
res=[]
fresh(); res.append(('control_unmodified_copy',)+run())
fresh(); p=os.path.join(C,'dispositions.json'); b=bytearray(open(p,'rb').read()); b[100]^=1; open(p,'wb').write(b); res.append(('hash_flip_one_byte',)+run())
fresh(); p=os.path.join(C,'SUMMARY.md'); open(p,'ab').write(b'x'); res.append(('size_append_byte',)+run())
fresh(); open(os.path.join(C,'extra.txt'),'w').write('x'); res.append(('extra_file',)+run())
fresh(); os.remove(os.path.join(C,'proposals.json')); res.append(('missing_file',)+run())
shutil.rmtree(SC)
ok=res[0][1]==0 and all(r[1]!=0 for r in res[1:])
print(json.dumps({'tests':[{'name':n,'exit':c,'errors':e} for n,c,e in res],'negative_rejection':ok,'scratch_removed':not os.path.exists(SC)}))
sys.exit(0 if ok else 1)
