#!/usr/bin/env python3
"""Read-only r234 artifact replay; copied corruption controls are temporary."""
from pathlib import Path
import datetime,hashlib,json,os,runpy,stat,subprocess,sys,tempfile
from fractions import Fraction
P=Path(__file__).resolve().parent;A=P.parent/'fresh-structural-discovery-r234';S=A/'packet';C=P.parents[1];PROJECT=C.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'FINAL.json':'e3390b68a4c433a98155e1e39660624a8e97cf53245684a8436cf7cd766b03fa','MANIFEST.json':'65d164a5bd5d93c0f64d10b9b0c49dd079c222645eecb8788addd6c7a5921085','REPORT.md':'b838bd49e2dfb0e83e23bc67a08446d2dcf264595fdff5f5bc38169defad0d7c'}
def inventory(root):
 out={'files':{},'directories':{},'root_mode':stat.S_IMODE(root.stat().st_mode)}
 for base,ds,fs in os.walk(root,followlinks=False):
  for n in ds+fs:
   p=Path(base)/n;rel=p.relative_to(root).as_posix();st=p.lstat();assert not stat.S_ISLNK(st.st_mode)
   if stat.S_ISDIR(st.st_mode):out['directories'][rel]=stat.S_IMODE(st.st_mode)
   else:
    assert stat.S_ISREG(st.st_mode);b=p.read_bytes();out['files'][rel]={'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(st.st_mode)}
 return out
before=inventory(A);selected=inventory(S);m=read(A/'MANIFEST.json')
assert set(selected['files'])=={x['path']for x in m['files']}
for n,h in anchors.items():assert sha((A/n).read_bytes())==h
def invoke(expected):
 args=[sys.executable,'-I','-B',str(S/'verify_packet.py'),'--packet',str(S)]
 for arg,n in [('manifest','MANIFEST.json'),('final','FINAL.json'),('report','REPORT.md')]:args+=['--'+arg,str(A/n),'--'+arg+'-sha256',expected[n]]
 r=subprocess.run(args,capture_output=True,text=True);return r.returncode,json.loads(r.stdout)if r.returncode==0 else r.stderr.strip()
code,verified=invoke(anchors);assert code==0
treebytes=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(treebytes)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(treebytes)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree}
records=read(S/'private/canonical-authentication.json');assert len(records)==12
for x in records:
 b=(S/x['local']).read_bytes();e=by[x['path']];assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha'];assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'in x['url']
prefix='preprints/A-Three-Manifold-Without-Conjugate-Points-and-Without-a-Nonpositively-Curved-Metric-September-24-2026';assert read(S/'private/selected-tree.json')==[x for x in tree if x['path']==prefix or x['path'].startswith(prefix+'/')]
reads=[json.loads(x)for x in(S/'private/semantic-reads.jsonl').read_bytes().splitlines()];source_count=primary_count=omission_count=0
for x in reads:
 b=(S/x['file']).read_bytes();lo,hi=x['start'],x['end'];assert 0<=lo<hi<=len(b)
 if x['file'].startswith('private/canonical/'):
  assert lo==0 and hi==len(b) and sha(b)==x['sha256'];source_count+=1
 else:
  assert sha(b)==x['sha256'];ls=b.splitlines(keepends=True);i,j=x['line_start'],x['line_end_exclusive'];assert [sum(map(len,ls[:i-1])),sum(map(len,ls[:j-1]))]==[lo,hi]
  ends=set();offset=lo
  for line in ls[i-1:j-1]:ends.add((offset,offset+len(line)));offset+=len(line)
  for o in x['omissions']:assert(o['start'],o['end'])in ends
  primary_count+=1;omission_count+=len(x['omissions'])
assert(source_count,primary_count)==(8,6)
pdfs=[]
for x in read(S/'private/primary/access.json'):
 if 'failure'in x:continue
 p=S/'private/primary'/(x['name']+'.pdf');b=p.read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'];assert len(p.with_suffix('.txt').read_bytes())==x['text_bytes'];pdfs.append(x['name'])
g=read(S/'guards.json');assert len(g['wildcards'])==391 and len(g['substrings'])==162
h=read(S/'private/history-navigation.json');assert h['guards_sha256']==sha((S/'guards.json').read_bytes())and not h['hits']
assert not(A/'private/history-holonomy-navigation.json').exists();assert "OWN/'private/history-navigation.json'"in(S/'navigate_holonomy.py').read_text()
assert 'sorry'in(S/'private/ConjugatePoints.lean').read_text()
check=runpy.run_path(str(S/'verify_packet.py'))['check_tree'];controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='copied-controls-')as td:
 r=Path(td);f=r/'selected';b=b'independent copied control\n';f.write_bytes(b);f.chmod(0o444);entry={'path':'selected','bytes':len(b),'sha256':sha(b),'mode':'0444'}
 def case(label,reject=False):
  try:check(r,[entry],{},'0700');failed=False
  except AssertionError:failed=True
  assert failed==reject;controls.append({'case':label,'observed':'rejected'if reject else'accepted'})
 case('valid tiny selection');f.chmod(0o644);f.write_bytes(bytes([b[0]^1])+b[1:]);f.chmod(0o444);case('same-size byte mutation',True);f.chmod(0o644);f.write_bytes(b);case('file mode mutation',True);f.chmod(0o444)
 extra=r/'extra';extra.write_bytes(b'x');case('extra file',True);extra.unlink();extra.mkdir();case('extra directory',True);extra.rmdir();r.chmod(0o755);case('root mode mutation',True);r.chmod(0o700);case('restored selection')
code,_=invoke(dict(anchors,**{'MANIFEST.json':'0'*64}));assert code!=0
def determinant(rows):
 a=[list(map(Fraction,row))for row in rows];d=Fraction(1)
 for i in range(len(a)):
  k=next(k for k in range(i,len(a))if a[k][i]);
  if k!=i:a[i],a[k]=a[k],a[i];d=-d
  pivot=a[i][i];d*=pivot
  for j in range(i+1,len(a)):
   q=a[j][i]/pivot
   for k in range(i,len(a)):a[j][k]-=q*a[i][k]
 return str(d)
algebra=read(S/'algebra.json');assert determinant([[0,1,1],[1,1,1],[1,1,2]])==algebra['triangle_determinant'];dets={}
for row in algebra['wheels']:
 n=row['odd_wheel_n'];a=[[0]*(n+1)for _ in range(n+1)]
 for i in range(n):a[0][i+1]=a[i+1][0]=1;a[i+1][i+1]=2;a[i+1][(i+1)%n+1]=1;a[i+1][(i-1)%n+1]=1
 d=determinant(a);assert d==row['determinant']and row['first_betti_from_proof']==3*n+2;dets[n]=d
assert inventory(A)==before;(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_files':len(m['files']),'selected_subdirectories':len(m['directories']),'entire_author_files':len(before['files']),'entire_author_subdirectories':len(before['directories']),'verifier':verified,'verifier_sha256':sha((S/'verify_packet.py').read_bytes()),'canonical_blobs_authenticated':len(records),'complete_operative_source_intervals_bound':source_count,'primary_read_intervals_bound':primary_count,'primary_omitted_line_ranges_bound':omission_count,'primary_pdfs_authenticated':pdfs,'formal_support':'none; sorry present','history_limitation':'The second holonomy navigation script overwrites private/history-navigation.json. Its record is sealed with zero hits; the separately named history-holonomy-navigation.json in READ_LIMITS is absent, so no independent first-pass record or exhaustive clearance is verified.','independent_copied_controls':controls,'wrong_detached_anchor_rejected':True,'independent_exact_wheel_determinants':dets,'author_originals_unchanged':True,'semantic_scope':'Complete authored derivations, comparison/reading limits and handoffs read. Range authentication does not inherit semantic source/primary or visual reading. Elementary determinant replay is supplementary, not a full mathematical grade. No frozen theorem, grades or count.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
