import json,os,shutil,subprocess,sys,tempfile
from pathlib import Path
R=Path(sys.argv[1]);A=Path(sys.argv[2]);anchor=sys.argv[3]
def fresh():
    t=Path(tempfile.mkdtemp(dir='/var/tmp/t133e-proof-r1'))
    shutil.copytree(R,t/'review',symlinks=True);shutil.copytree(A,t/'author',symlinks=True);return t
def run(t,anc=anchor):
    p=subprocess.run([sys.executable,str(t/'review/verify.py'),'--anchor',anc,'--root',str(t/'review'),'--author-root',str(t/'author')],capture_output=True,text=True)
    return p.returncode,p.stdout.strip(),p.stderr.strip()
cases=[]
def case(nm,mut,expect,anc=anchor):
    t=fresh();mut(t);rc,o,e=run(t,anc);shutil.rmtree(t)
    ok=(rc==0 and o.startswith('{') and json.loads(o)['result']=='PASS_INTEGRITY_ONLY') if expect is None else (rc==1 and o in ['INTEGRITY_REJECT: '+x for x in expect.split('|')])
    cases.append({'case':nm,'exit':rc,'stdout':o,'stderr':e,'expected':expect or 'PASS','reason_checked':ok})
    if not ok: print('CONTROL MISMATCH',nm,rc,o,e);sys.exit(1)
def app(p,b): open(p,'ab').write(b)
case('positive',lambda t:None,None)
case('wrong_anchor',lambda t:None,'external anchor mismatch','0'*64)
case('changed_review',lambda t:app(t/'review/review.md',b'x'),'payload hash: review.md')
case('extra_file',lambda t:(t/'review/extra.txt').write_text('x'),'file membership')
case('missing_file',lambda t:(t/'review/diagnostics.py').unlink(),'file membership')
case('extra_empty_directory',lambda t:(t/'review/emptydir').mkdir(),'directory membership')
case('symlink',lambda t:os.symlink('review.md',t/'review/link'),'symlink: link')
case('hardlink',lambda t:os.link(t/'review/review.md',t/'review/hl'),'hardlink: review.md|hardlink: hl')
case('fifo',lambda t:os.mkfifo(t/'review/pipe'),'nonregular: pipe')
case('author_candidate_changed',lambda t:app(t/'author/candidate.md',b'x'),'author payload: candidate.md')
case('author_extra_file',lambda t:(t/'author/extra.md').write_text('x'),'author file membership')
case('author_manifest_changed',lambda t:app(t/'author/MANIFEST.json',b' '),'author manifest anchor')
case('restored_positive',lambda t:None,None)
print(json.dumps({'note':'Controls run on fresh /var/tmp copies of the review directory and the full author packet; originals never mutated. Each negative is reason-checked against its exact rejection message.','anchor_tested':anchor,'controls':cases},indent=1,sort_keys=True))
