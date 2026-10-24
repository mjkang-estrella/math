#!/usr/bin/env python3
"""Read-only parent replay; integrity mutations use tiny independent copies."""
from pathlib import Path
import datetime,fnmatch,hashlib,json,os,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;A=P.parent/'fresh-structural-discovery-r226';C=P.parents[1];PROJECT=C.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'FINAL.md':'0f175f0688436b4713ac28ea2132a4c7b8a244e64c702fa2e0850c5055df4a4c','MANIFEST.json':'fda720fc4892c04da55481c8d4d3cffda6192d4ff63a8a16ce5e80802ae7ba2c','REPORT.md':'b1771180ac0c8294fbbcc3e36be39de80b9a2b923d13eaa18aa3233f9cb95c57'}
def inventory(root):
 out={'files':{},'directories':{},'root_mode':stat.S_IMODE(root.stat().st_mode)}
 for base,ds,fs in os.walk(root,followlinks=False):
  for n in ds+fs:
   p=Path(base)/n;rel=p.relative_to(root).as_posix();st=p.lstat();assert not stat.S_ISLNK(st.st_mode)
   if stat.S_ISDIR(st.st_mode):out['directories'][rel]={'path':rel,'mode':stat.S_IMODE(st.st_mode)}
   else:
    assert stat.S_ISREG(st.st_mode);b=p.read_bytes();out['files'][rel]={'path':rel,'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(st.st_mode)}
 return out
before=inventory(A);m=read(A/'MANIFEST.json');assert read(A/'ANCHORS.json')==anchors
for n,h in anchors.items():assert sha((A/n).read_bytes())==h
reserved={'MANIFEST.json','REPORT.md','ANCHORS.json','CONTROLS.json'}
selected={k:v for k,v in before['files'].items() if k not in reserved and not k.startswith('controls/')}
expected={x['path']:dict(x,mode=int(x['mode'],8)) for x in m['files']};assert selected==expected
dirs={k:v for k,v in before['directories'].items() if k!='controls' and not k.startswith('controls/')};dirs['.']={'path':'.','mode':before['root_mode']}
assert dirs=={x['path']:dict(x,mode=int(x['mode'],8)) for x in m['directories']}
def invoke(root,expected):
 r=subprocess.run([sys.executable,'-I','-B',str(A/'verify_packet.py'),'--root',str(root),'--manifest-sha256',expected['MANIFEST.json'],'--final-sha256',expected['FINAL.md'],'--report-sha256',expected['REPORT.md']],capture_output=True,text=True)
 return r.returncode,json.loads(r.stdout) if r.returncode==0 else r.stderr.splitlines()[-1]
code,verified=invoke(A,anchors);assert code==0
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(tb)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree}
records=read(A/'AUTHENTICATED.json');assert len(records)==34
for x in records:
 b=(A/'private/upstream'/x['path']).read_bytes();e=by[x['path']];assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha']
 assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in x['url']
prefixes={x['path'].split('/')[1] for x in records};assert read(A/'PINNED-SELECTION.json')==[x for x in tree if len(x['path'].split('/'))>1 and x['path'].split('/')[1] in prefixes]
reads=[json.loads(x) for x in (A/'READS.jsonl').read_bytes().splitlines()]
for x in reads:
 b=(A/'private/upstream'/x['path']).read_bytes();assert 0<=x['start']<x['end']<=len(b) and sha(b[x['start']:x['end']])==x['sha256']
section_coverage=[]
for x in records:
 p=Path(x['path'])
 if p.suffix!='.tex' or p.name in {'main.tex','paper.tex','preamble.tex','bibliography.tex'}:continue
 spans=sorted((r['start'],r['end']) for r in reads if r['path']==x['path']);end=0
 for lo,hi in spans:assert lo<=end;end=max(end,hi)
 assert end==x['bytes'];section_coverage.append(x['path'])
primary=read(A/'PRIMARY-ACCESS.json')+[read(A/'SUBMERSION-ACCESS.json')]
for x in primary:
 b=(A/'private/primary'/(x['name']+'.pdf')).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'];assert (A/'private/primary'/(x['name']+'.txt')).stat().st_size==x['text_bytes']
pr=[json.loads(x) for x in (A/'PRIMARY-READS.jsonl').read_bytes().splitlines()]
for x in pr:
 b=(A/'private/primary'/(x['name']+'.txt')).read_bytes();lo,hi=x['start'],x['end'];assert sha(b[lo:hi])==x['sha256'];assert all(lo<=a<z<=hi for a,z,*_ in x['omissions'])
guards=read(A/'GUARDS.json');assert len(guards['wildcards'])==375 and len(guards['substrings'])==162
hr=[json.loads(x) for x in (A/'HISTORY-READS.jsonl').read_bytes().splitlines()]
for x in hr:
 rel=x['path'].casefold();assert not any(fnmatch.fnmatchcase(rel,g.casefold()) for g in guards['wildcards']);assert not any(g.casefold() in rel for g in guards['substrings'])
 lo,hi=x['start'],x['end'];copy=A/x.get('local_copy','private/history/'+x['path']+'.'+str(lo)+'-'+str(hi)+'.txt')
 with (PROJECT/x['path']).open('rb') as f:f.seek(lo);b=f.read(hi-lo)
 assert sha(b)==x['sha256'] and copy.read_bytes()==b
formal=read(A/'FORMAL-SOURCES.json')
for x in formal:
 b=(A/'private/upstream'/x['path']).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']
assert sha((A/'SOURCE350-CATALOGUE.txt').read_bytes())=='e7d3505a9e2faf87f0cb25a60453671e52275c9eebdde796ebb0a4034dd1b7f7'
author_controls=[];good=A/'controls/good';good_anchors={n:sha((good/n).read_bytes()) for n in anchors}
for label,reject in [('good',False),('content',True),('mode',True),('extra',True)]:
 code,result=invoke(A/'controls'/label,good_anchors);assert (code!=0)==reject;author_controls.append({'case':label,'observed':'rejected' if reject else 'accepted'})
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='copied-controls-') as td:
 r=Path(td);r.chmod(0o700);f=r/'FINAL.md';data=(A/'FINAL.md').read_bytes();f.write_bytes(data);f.chmod(0o444);report=r/'REPORT.md';report.write_bytes((A/'REPORT.md').read_bytes());report.chmod(0o444)
 content=r/'MATH.txt';content.write_bytes(b'local copied integrity control\n');content.chmod(0o444)
 rows=[{'path':p.name,'bytes':p.stat().st_size,'sha256':sha(p.read_bytes()),'mode':'0444'} for p in [f,content]]
 manifest=r/'MANIFEST.json';manifest.write_text(json.dumps({'schema':'r226-exact-packet-v1','files':rows,'directories':[{'path':'.','mode':'0700'}]}));manifest.chmod(0o444);expected={n:sha((r/n).read_bytes()) for n in anchors}
 def case(label,reject=False,override=None):
  code,result=invoke(r,override or expected);assert (code!=0)==reject,(label,result);controls.append({'case':label,'observed':'rejected' if reject else 'accepted'})
 case('valid independent copied selection');content.chmod(0o644);original=content.read_bytes();content.write_bytes(bytes([original[0]^1])+original[1:]);content.chmod(0o444);case('same-size byte mutation',True);content.chmod(0o644);content.write_bytes(original);content.chmod(0o600);case('file mode mutation',True);content.chmod(0o444);extra=r/'extra';extra.write_bytes(b'x');case('extra file',True);extra.unlink();case('wrong detached anchor',True,dict(expected,**{'MANIFEST.json':'0'*64}));case('restored copies')
assert inventory(A)==before
(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_files':len(selected),'selected_directories_including_root':len(dirs),'entire_author_files':len(before['files']),'entire_author_subdirectories':len(before['directories']),'verifier':verified,'verifier_sha256':sha((A/'verify_packet.py').read_bytes()),'canonical_blobs_authenticated':len(records),'source_read_extents_bound':len(reads),'operative_source_sections_fully_covered_by_recorded_ranges':len(section_coverage),'primary_read_extents_bound':len(pr),'primary_pdfs_authenticated':len(primary),'formal_artifacts_authenticated':len(formal),'original_history_read_records_bound':len(hr),'original_history_distinct_ranges_bound':len({(x['path'],x['start'],x['end']) for x in hr}),'author_copied_controls_replayed':author_controls,'independent_copied_controls':controls,'author_originals_unchanged':True,'semantic_scope':'Parent read START, LIMITS, COVERAGE, DERIVATIONS, FINAL, outside REPORT and verifier. Authentication and recorded-range checks do not inherit child source/primary/history semantic coverage. No mathematical grade.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
