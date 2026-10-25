#!/usr/bin/env python3
"""Read-only S245 artifact replay, independent of mathematical disposition."""
from pathlib import Path
from fractions import Fraction
import ast,datetime,hashlib,json,os,re,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;A=P.parent/'fresh-structural-discovery-r245';Q=A/'packet';C=P.parents[1];PROJECT=C.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'packet/FINAL.md':'79188dcd087be99bcbc1c55aaf84f36811f5c4203ae9aa9694d4a16e74156074','packet/MANIFEST.json':'0d8e597209900e0d48f1ab309e819cc4a3898e87d5cf7483635fea56808541f3','REPORT.md':'5acf1318ec2d21ab0dc6663c74b825f80b403e89049d9e69a72254b4a94947c1'}
def inventory(root):
 out={'root_mode':stat.S_IMODE(root.stat().st_mode),'files':{},'directories':{}}
 for base,ds,fs in os.walk(root,followlinks=False):
  for name in ds+fs:
   p=Path(base)/name;s=p.lstat();rel=p.relative_to(root).as_posix();assert not stat.S_ISLNK(s.st_mode)
   if stat.S_ISDIR(s.st_mode):out['directories'][rel]=stat.S_IMODE(s.st_mode)
   else:
    assert stat.S_ISREG(s.st_mode);b=p.read_bytes();out['files'][rel]={'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(s.st_mode)}
 return out
before=inventory(A)
assert sha((Q/'verify_packet.py').read_bytes())=='50b888a7ae9df60c8a796cf487f3332cabddc8faf0477d16077ef00038cb7433'
def invoke(root,expected):
 args=[sys.executable,'-I','-B',str(Q/'verify_packet.py'),'--packet',str(root/'packet'),'--report',str(root/'REPORT.md')]
 for flag,name in [('final','packet/FINAL.md'),('manifest','packet/MANIFEST.json'),('report','REPORT.md')]:args+=['--'+flag+'-sha256',expected[name]]
 r=subprocess.run(args,capture_output=True,text=True);return r.returncode,r.stdout.strip()or r.stderr.strip()
code,verified=invoke(A,anchors);assert code==0,verified
m=read(Q/'MANIFEST.json');assert len(m['files'])==34 and len(m['directories'])==6
assert {v['path']:v['sha256']for v in read(A/'ANCHORS.json').values()}==anchors
for n,h in anchors.items():assert sha((A/n).read_bytes())==h
mapping={'FINAL.md':'FINAL-draft.md','private/READING-ACCOUNT.md':'SOURCE-READING.md','private/catalogue-slice.txt':'catalogue-slice.txt','private/companion-paths.json':'companion-paths.json','private/tree-selection.json':'tree-selection.json'}
for name in m['files']:
 assert (Q/name).read_bytes()==(A/mapping.get(name,name)).read_bytes(),name
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tb)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree};records=read(A/'private/authentication.json');assert len(records)==10
prefixes={'/'.join(x['path'].split('/')[:2])for x in records};selected=[x for x in tree if '/'.join(x['path'].split('/')[:2])in prefixes]
assert selected==read(A/'tree-selection.json') and len(selected)==13
for x in records:
 b=(A/x['local']).read_bytes();e=by[x['path']]
 assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha']
 assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'in x['url']
g=ast.parse((A/'guards.py').read_text());guards={}
for x in g.body:
 if isinstance(x,ast.Assign) and isinstance(x.targets[0],ast.Name)and x.targets[0].id in ['WILDCARDS','SUBSTRINGS']:
  assert isinstance(x.value,ast.Call)and isinstance(x.value.func,ast.Attribute)and x.value.func.attr=='split';guards[x.targets[0].id]=ast.literal_eval(x.value.func.value).split()
brief=(PROJECT/read(P/'brief-record.json')['brief']).read_text()
assert set(guards['WILDCARDS'])==set(re.findall(r'\*[A-Za-z0-9][A-Za-z0-9*_-]*\*',brief))and len(guards['WILDCARDS'])==413 and len(guards['SUBSTRINGS'])==162
rows=[json.loads(x)for x in(A/'private/read-extents.jsonl').read_bytes().splitlines()];coverage={};primary=0;intervals=0
for x in rows:
 name=x['path'];assert name.startswith('private/');b=(A/name).read_bytes();ls=b.splitlines(keepends=True);start,end=x['lines'];lo,hi=x.get('bytes',x.get('outer_bytes'))
 assert [lo,hi]==[sum(map(len,ls[:start-1])),sum(map(len,ls[:end]))]
 if 'bytes'in x:
  assert sha(b[lo:hi])==x['sha256'];ranges=[(lo,hi)]
 else:
  assert sha(b)==x['full_text_sha256'];ranges=x['displayed_byte_ranges'];primary+=len(ranges)
 for u,v in ranges:assert lo<=u<v<=hi;intervals+=1
 if '/sections/'in name:coverage.setdefault(name,[]).extend(ranges)
for name,ranges in coverage.items():
 end=0
 for lo,hi in sorted(ranges):assert lo<=end;end=max(end,hi)
 assert end==len((A/name).read_bytes())
assert len(coverage)==6 and len(rows)==27
for x in read(A/'private/primary/access.json'):
 b=(A/'private/primary'/(x['name']+'.pdf')).read_bytes();assert len(b)==x['bytes']and sha(b)==x['sha256'];assert (A/'private/primary'/(x['name']+'.txt')).stat().st_size==x['text_bytes']
for x in read(A/'private/lean-authentication.json'):
 b=(A/'private'/('lean370.md'if x['path'].endswith('/370.md')else'HenonEmden.lean')).read_bytes();assert len(b)==x['bytes']and sha(b)==x['sha256']and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob'];assert 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'in x['metadata_url']
assert sha((A/'catalogue-slice.txt').read_bytes())=='5842d75a4cce2675601a4250f777b9cde7dc8a70361c44ce66b2b407b936870f'
for x in read(A/'arithmetic-support.json')['rational_parameter_checks']:
 n,p,q,a,b=[x[k]for k in ['n','p','q','A','B']];alpha=Fraction(2+a+p*(2+b),p*q-1);beta=Fraction(2+b+q*(2+a),p*q-1);gamma=Fraction(n+a,p+1)+Fraction(n+b,q+1)-(n-2)
 assert (alpha,beta,gamma)==tuple(Fraction(x[k])for k in ['alpha','beta','gamma'])
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='tiny-controls-')as td:
 root=Path(td);packet=root/'packet';packet.mkdir(mode=0o700);payload=b'independent tiny control\n';f=packet/'FINAL.md';f.write_bytes(payload);f.chmod(0o600)
 manifest={'format':'r245-exact-selection-v1','files':{'FINAL.md':{'bytes':len(payload),'sha256':sha(payload),'mode':'0600'}},'directories':{'.':'0700'}}
 mp=packet/'MANIFEST.json';mp.write_text(json.dumps(manifest));mp.chmod(0o600);rp=root/'REPORT.md';rp.write_text('independent outside report\n');rp.chmod(0o600);expected={n:sha((root/n).read_bytes())for n in anchors}
 def case(label,reject=False):
  rc,out=invoke(root,expected);assert(rc!=0)==reject;controls.append({'case':label,'observed':'rejected'if reject else'accepted'})
 case('intact synthetic fixture');f.write_bytes(bytes([payload[0]^1])+payload[1:]);case('same-size byte mutation',True)
 f.write_bytes(payload);f.chmod(0o644);case('file mode mutation',True);f.chmod(0o600)
 packet.chmod(0o755);case('directory mode mutation',True);packet.chmod(0o700)
 extra=packet/'extra';extra.write_text('extra');case('extra file',True);extra.unlink();f.unlink();case('missing file',True)
 f.write_bytes(payload);f.chmod(0o600);case('restored fixture')
 rc,_=invoke(root,dict(expected,**{'REPORT.md':'0'*64}));assert rc!=0;controls.append({'case':'wrong detached anchor','observed':'rejected'})
assert inventory(A)==before
(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_payload_files':34,'selected_files_including_manifest':35,'selected_directories':6,'selected_payload_bytes':sum(x['bytes']for x in m['files'].values()),'entire_author_files':len(before['files']),'entire_author_subdirectories':len(before['directories']),'verifier':verified,'original_selected_copies_match':True,'canonical_blobs_authenticated':10,'canonical_exact_tree_entries':13,'read_ledger_rows':len(rows),'text_read_intervals_bound':intervals,'complete_source_section_files_covered':6,'primary_text_intervals_bound':primary,'primary_pdf_identities_bound':3,'history_original_intervals_bound':0,'history_limit':'No original mathematical body admitted; candidate rejected before semantic display. No clearance inferred.','independent_tiny_controls':controls,'rational_parameter_checks':3,'author_originals_unchanged':True,'formal_support':'none; comparator endpoint contains sorry','semantic_scope':'Complete 13-section derivation, reading account, final and report read. No source/primary/history semantic or visual coverage inherited. Truncation recoveries, late comparisons, editorial exposures and boundary overreads remain recorded. No nominee; no mathematical grades/count.','runtime':'gpt-6-astra/xhigh/default confirmed by owned terminal receipt'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
