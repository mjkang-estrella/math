#!/usr/bin/env python3
"""Read-only contribution-review replay. Mutations and arithmetic run only on tiny copies."""
from pathlib import Path
import datetime,hashlib,json,os,shutil,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;W=P.parent;C=P.parents[1];PROJECT=C.parents[2];R=W/'structural-r232-contribution-r1';S=R/'selected';A=W/'fresh-structural-discovery-r232'
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'FINAL.md':'01b56512b8ef20fc37de64310bc9fdc4990a8802b9c7990b0b6d2989cf8dde9f','MANIFEST.json':'7034c8cc471881500ed520e991d385af5ebf310b2d86e55c8e093afef791c2f7','REPORT.md':'f61fdb253309946283ebe2d76169bb63f22db3d3b09e55e8fa932d479add8227'}
def inventory(root):
 out={'files':{},'directories':{},'root_mode':stat.S_IMODE(root.stat().st_mode)}
 for base,ds,fs in os.walk(root,followlinks=False):
  for n in ds+fs:
   p=Path(base)/n;rel=p.relative_to(root).as_posix();st=p.lstat();assert not stat.S_ISLNK(st.st_mode)
   if stat.S_ISDIR(st.st_mode):out['directories'][rel]=stat.S_IMODE(st.st_mode)
   else:
    assert stat.S_ISREG(st.st_mode);b=p.read_bytes();out['files'][rel]={'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(st.st_mode)}
 return out
review_before=inventory(R);author_before=inventory(A);selected=inventory(S)
assert author_before==read(W/'discovery-structural-r232-parent/observed-root.json')
detached=read(R/'DETACHED-ANCHORS.json')
for key,n in [('FINAL','FINAL.md'),('MANIFEST','MANIFEST.json'),('REPORT','REPORT.md')]:
 assert detached[key]['sha256']==anchors[n] and sha((PROJECT/detached[key]['path']).read_bytes())==anchors[n]
assert sha((S/'REVIEW.md').read_bytes())=='6897ad3a6c1ae29aaea271bc0f3718adbcc764f7ea8f348748ab980183b590b3'
assert sha((S/'READING-ACCESS-LIMITS.md').read_bytes())=='1ba92de9be31105916ea51ce62811179677facef8a4fea07f8463c0f49dc0eba'
assert detached['sealed_once'] is True
m=read(S/'MANIFEST.json');expected={e['path']:e for e in m['files']}
assert set(selected['files'])==set(expected)|{'FINAL.md','MANIFEST.json'}
for n,e in expected.items():assert selected['files'][n]==dict(bytes=e['bytes'],sha256=e['sha256'],mode=int(e['mode'],8))
assert {'.':selected['root_mode'],**selected['directories']}=={n:int(v,8) for n,v in m['directories'].items()}
def invoke(root,report,exp):
 r=subprocess.run([sys.executable,'-I','-B',str(S/'code/verify_packet.py'),'--root',str(root),'--final-sha256',exp['FINAL.md'],'--manifest-sha256',exp['MANIFEST.json'],'--report',str(report),'--report-sha256',exp['REPORT.md']],capture_output=True,text=True)
 return r.returncode,json.loads(r.stdout)
code,verified=invoke(S,R/'REPORT.md',anchors);assert code==0
baseline=read(S/'private/original-baseline.json');baseline['files']={e['path']:{k:v for k,v in e.items() if k!='path'} for e in baseline['files']}
am=read(A/'selected/MANIFEST.json')
admitted={'selected/'+e['path'] for e in am['files']}|{'selected/FINAL.md','selected/MANIFEST.json','REPORT.md','DETACHED-ANCHORS.json','SEAL-VERIFICATION.json'}
assert set(baseline['files'])==admitted and len(admitted)==82
for n,e in baseline['files'].items():assert author_before['files'][n]==dict(bytes=e['bytes'],sha256=e['sha256'],mode=int(e['mode'],8))
for n,e in baseline['directories'].items():assert stat.S_IMODE((A/n).stat().st_mode)==int(e,8)
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree={e['path']:e for e in json.loads(tb)['tree']};assert len(tree)==13223
canon=read(S/'private/canonical-verification.json')['blobs'];assert len(canon)==22
source_records={e['path']:e for e in read(A/'selected/private/evidence/authentication-private.json')};assert set(canon)==set(source_records)
for name in canon:
 x=source_records[name];b=(A/'selected/private'/name).read_bytes();e=tree[name]
 assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha']
logs=[json.loads(x) for x in (S/'private/semantic-reads.jsonl').read_bytes().splitlines()]
for x in logs:
 assert 'selected/'+x['path'] in admitted
 b=(A/'selected'/x['path']).read_bytes();ls=b.splitlines(keepends=True);lo,hi=x['lines_inclusive'];start,end=x['bytes_half_open']
 assert 1<=lo<=hi<=len(ls) and [sum(map(len,ls[:lo-1])),sum(map(len,ls[:hi]))]==[start,end]
 assert sha(b)==x['file_sha256']
 for l,h in x['masks']:assert 1<=l<=h<=len(ls)
g=read(S/'private/guards.json');ag=read(A/'selected/private/evidence/guards.json')
assert set(g['wildcards'])==set(ag['wildcards']) and len(g['wildcards'])==387
assert set(g['substrings'])==set(ag['substrings']) and len(g['substrings'])==162
assert read(S/'private/focused-history.json')['candidate_metadata']==[] and read(S/'private/focused-history.json')['body_displays']==0
for e in read(S/'private/copied-origins.json'):
 assert sha((PROJECT/e['source']).read_bytes())==e['sha256']==sha((R/e['destination']).read_bytes()) and (R/e['destination']).stat().st_size==e['bytes']
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='contribution-copied-controls-') as td:
 root=Path(td)/'packet';root.mkdir();f=root/'sample.txt';content=b'independent copied review control\n';f.write_bytes(content);f.chmod(0o400);(root/'FINAL.md').write_bytes(b'Copied final\n');(root/'FINAL.md').chmod(0o400);report=Path(td)/'REPORT.md';report.write_bytes(b'Copied report\n');report.chmod(0o400)
 mf=root/'MANIFEST.json';mf.write_text(json.dumps({'files':[dict(path='sample.txt',bytes=len(content),sha256=sha(content),mode='0400')],'directories':{'.':'0500'}}));mf.chmod(0o400);root.chmod(0o500)
 exp={n:sha((report if n=='REPORT.md' else root/n).read_bytes()) for n in anchors}
 def case(label,reject=False,override=None):
  code,result=invoke(root,report,override or exp);assert bool(code)==reject,(label,result);controls.append({'case':label,'observed':'rejected' if reject else 'accepted'})
 case('valid independent copied selection')
 f.chmod(0o600);f.write_bytes(bytes([content[0]^1])+content[1:]);f.chmod(0o400);case('same-size byte mutation',True)
 f.chmod(0o600);f.write_bytes(content);f.chmod(0o400)
 f.chmod(0o600);case('file mode mutation',True);f.chmod(0o400)
 root.chmod(0o700);extra=root/'extra';extra.write_bytes(b'x');root.chmod(0o500);case('extra file',True);root.chmod(0o700);extra.unlink();root.chmod(0o500)
 case('wrong detached anchor',True,dict(exp,**{'FINAL.md':'0'*64}))
 root.chmod(0o700);case('directory mode mutation',True);root.chmod(0o500)
 case('restored copies');root.chmod(0o700)
from fractions import Fraction as F
from math import factorial
x=F(11,8);bound=sum((x**k/F(factorial(k)) for k in range(7)),F(0))+(x**7/F(factorial(7)))/(1-F(11,64))
assert bound==F(92316867089,23341301760) and bound<4
assert 2*(6+20)==52 and 2*52==104<121
assert 3*F(1,8)**2/256+F(22,16)<2
arithmetic={'exp_11_over_8_upper':str(bound),'upper_less_than_four':True,'improved_cosh_coefficient':52,'improved_squared_distance_coefficient':104,'improved_distance_coefficient':11,'improved_radius_geometric_error_div_h_max':str(3*F(1,8)**2/256+F(22,16)),'scope':'Exact finite arithmetic from the full comparison; not a proof gate.'}
assert inventory(R)==review_before and inventory(A)==author_before
(P/'contribution-observed-root.json').write_text(json.dumps(review_before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_manifest_entries':len(expected),'selected_total_files':len(selected['files']),'selected_subdirectories':len(selected['directories']),'entire_review_files':len(review_before['files']),'entire_review_subdirectories':len(review_before['directories']),'entire_author_files':len(author_before['files']),'admitted_author_files':len(admitted),'admitted_author_baseline_matches_parent':True,'verifier':verified,'verifier_sha256':sha((S/'code/verify_packet.py').read_bytes()),'canonical_blobs_authenticated':len(canon),'read_extents_bound':len(logs),'primary_read_extents_bound':sum('/primary/' in x['path'] for x in logs),'read_log_hash_semantics':'Whole-file SHA256 plus exact line/byte extents; inspected helper before replay. Masked furniture is preserved separately.','independent_copied_controls':controls,'independent_exact_rational_checks':arithmetic,'author_originals_unchanged':True,'review_originals_unchanged':True,'history_time_disclosure':'focused-history.json records 22:13:17; reading-events.md labels the pass 22:19:09. These differing recorded times are preserved, not silently reconciled; no history absence claim is used.', 'semantic_scope':'Parent read the complete independent REVIEW, READING-ACCESS-LIMITS, FINAL and outside REPORT. Artifact replay does not inherit reviewer source/primary semantic or visual coverage. Contribution comparison only; full correctness supplied separately by parent-adopted independent review.'}
(P/'contribution-replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

