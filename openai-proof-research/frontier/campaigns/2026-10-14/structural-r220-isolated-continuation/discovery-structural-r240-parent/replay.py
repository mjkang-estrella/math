#!/usr/bin/env python3
"""Read-only S240 artifact replay; retained calculations receive no mathematical grade."""
from pathlib import Path
import datetime,hashlib,json,os,re,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;A=P.parent/'fresh-structural-discovery-r240';C=P.parents[1];PROJECT=C.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'packet/original/FINAL.md':'23d095d36b5f772303c39fd06d1a016330426d129346cd566a79a65f615f1c2c','MANIFEST.json':'91bd9a6948e2258eb1c9d0387c89b003436580de450a35955cfd24e477992626','REPORT.md':'283a10396661980dd544b880acd007ff662fc1e0ff3cd7ab50516bcdd98a1215'}
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
def invoke(root,expected):
 args=[sys.executable,'-I','-B',str(A/'verify_packet.py'),'--packet',str(root/'packet'),'--manifest',str(root/'MANIFEST.json'),'--report',str(root/'REPORT.md'),'--final-relative','original/FINAL.md']
 for flag,name in [('final','packet/original/FINAL.md'),('manifest','MANIFEST.json'),('report','REPORT.md')]:args+=['--'+flag+'-sha256',expected[name]]
 r=subprocess.run(args,capture_output=True,text=True);return r.returncode,json.loads(r.stdout)
code,verified=invoke(A,anchors);assert code==0 and verified['files']==86
assert sha((A/'verify_packet.py').read_bytes())=='9bbf11840245f66ba89c9723b29752b95fb793a2be3a4d476722b109fdb405f8'
for n,h in anchors.items():assert sha((A/n).read_bytes())==h and h in (A/'ANCHORS.txt').read_text()
preserve=read(A/'PRESERVATION.json')
for x in preserve['original_notes']:assert sha((A/x['original']).read_bytes())==x['sha256'] and (A/x['original']).read_bytes()==(A/'packet'/x['selected']).read_bytes()
for p in(A/'packet/private').rglob('*'):
 if p.is_file():
  rel=p.relative_to(A/'packet/private');original=A/rel.name if rel.parts[0]=='setup' else A/'private'/rel
  assert p.read_bytes()==original.read_bytes()
treebytes=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(treebytes)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(treebytes)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree};records=read(A/'private/authentication.json');assert len(records)==34
prefixes={x['path'].split('/')[1]for x in records};selected=[x for x in tree if len(x['path'].split('/'))>1 and x['path'].split('/')[1]in prefixes]
assert read(A/'source-selection.json')==[x for x in selected if x['path'].count('/')>1] and len(selected)==44
for x in records:
 b=(A/'private'/x['path']).read_bytes();e=by[x['path']]
 assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_sha']==e['sha']
 assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in x['url']
rows=lambda name:[json.loads(x)for x in(A/name).read_bytes().splitlines()]
reads=rows('private/semantic-reads.jsonl');coverage={}
for x in reads:
 b=(A/x['path']).read_bytes();ls=b.splitlines(keepends=True);lo=x['start_line'];hi=x['end_line']
 assert sha(b)==x['sha256'] and [sum(map(len,ls[:lo-1])),sum(map(len,ls[:hi]))]==[x['start_byte'],x['end_byte']]
 coverage.setdefault(x['path'],set()).update(range(lo,hi+1))
assert len(coverage)==28
for name,cov in coverage.items():assert cov==set(range(1,len((A/name).read_bytes().splitlines(keepends=True))+1))
fragments=rows('private/semantic-fragments.jsonl')
for x in fragments:
 a,z=x['bytes'];b=(A/x['path']).read_bytes();assert 0<=a<z<=len(b) and sha(b)==x['sha256']
primary=rows('private/primary-reads.jsonl')
for x in primary:
 b=(A/'private/primary'/(x['id']+'.txt')).read_bytes();ls=b.splitlines(keepends=True);lo=x['start_line'];hi=x['end_line']
 assert sha(b)==x['sha256'] and [sum(map(len,ls[:lo-1])),sum(map(len,ls[:hi]))]==[x['start_byte'],x['end_byte']]
access=read(A/'private/primary/access.json');success=[x for x in access if 'error'not in x];assert len(success)==5
for x in success:
 b=(A/'private/primary'/(x['id']+'.pdf')).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256']
g=read(A/'guards.json');brief=(PROJECT/read(P/'brief-record.json')['brief']).read_text()
assert set(g['wildcards'])==set(re.findall(r'\*[A-Za-z0-9][A-Za-z0-9*_-]*\*',brief))and len(g['wildcards'])==403 and len(g['substrings'])==162
h1=read(A/'private/history-navigation.json');h2=read(A/'private/current-history-navigation.json')
assert len(h1['hits'])==1 and h1['hits'][0]['heading']=='## 2. Exact accepted interfaces' and not h2['hits']
assert b'sorry' in (A/'private/Conductivity.lean').read_bytes()
assert sha((A/'source365-entry.txt').read_bytes())=='591a96393a3483e4fe0e9b08b4e9d605e735c839fc0fbe3ba46a95f90579ac14'
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='tiny-controls-')as td:
 root=Path(td);packet=root/'packet';orig=packet/'original';orig.mkdir(parents=True);payload=b'independent tiny control\n';f=orig/'FINAL.md';f.write_bytes(payload);f.chmod(0o444)
 manifest={'format':'source365-exact-tree-v1','files':[{'path':'original/FINAL.md','bytes':len(payload),'sha256':sha(payload),'mode':0o444}],'directories':[{'path':'.','mode':0o555},{'path':'original','mode':0o555}]}
 (root/'MANIFEST.json').write_text(json.dumps(manifest));(root/'REPORT.md').write_text('outside report\n');orig.chmod(0o555);packet.chmod(0o555);expected={n:sha((root/n).read_bytes())for n in anchors}
 def case(label,reject=False):
  rc,out=invoke(root,expected);assert (rc!=0)==reject;controls.append({'case':label,'observed':'rejected'if reject else'accepted'})
 case('intact synthetic fixture')
 f.chmod(0o644);f.write_bytes(bytes([payload[0]^1])+payload[1:]);f.chmod(0o444);case('same-size byte mutation',True)
 f.chmod(0o644);f.write_bytes(payload);case('file mode mutation',True);f.chmod(0o444)
 orig.chmod(0o755);case('directory mode mutation',True);extra=orig/'extra';extra.write_text('extra');orig.chmod(0o555);case('extra file',True);orig.chmod(0o755);extra.unlink();f.unlink();orig.chmod(0o555);case('missing file',True)
 orig.chmod(0o755);f.write_bytes(payload);f.chmod(0o444);orig.chmod(0o555);case('restored fixture')
 rc,_=invoke(root,dict(expected,**{'REPORT.md':'0'*64}));assert rc!=0;controls.append({'case':'wrong detached anchor','observed':'rejected'})
 packet.chmod(0o755);orig.chmod(0o755)
assert inventory(A)==before
(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_files':verified['files'],'selected_directories':verified['directories'],'entire_author_files':len(before['files']),'entire_author_subdirectories':len(before['directories']),'verifier':verified,'original_selected_copies_match':True,'canonical_blobs_authenticated':34,'canonical_exact_tree_entries':44,'source_read_intervals_bound':len(reads),'complete_operative_text_files_covered':28,'late_source_fragment_bound':len(fragments),'primary_read_intervals_bound':len(primary),'primary_pdf_identities_bound':5,'source_and_primary_hash_semantics':'Logs bind whole underlying file identities plus exact interval coordinates, not masked display digests.','guarded_history_passes':2,'admitted_history_mathematical_bodies':0,'history_limit':'One administrative interface hit rejected by human classification despite initial automatic false negative; second narrower pass no hits. No exhaustive clearance.','author_control_cases':len(read(A/'CONTROL-RESULTS.json')['controls']),'independent_tiny_controls':controls,'author_originals_unchanged':True,'formal_support':'none; local pinned declaration contains sorry; no independent formal build','semantic_scope':'Parent read complete CALCULATIONS, DERIVATIONS, compact-calculation, ACCESS, FINAL, outside REPORT and tier note. No source/primary/history semantic or visual coverage is inherited; actual masks, late reads, unlogged small displays and Meyers preliminary formula limitations remain disclosed. Retained calculations are unreviewed; no nominee or mathematical grades/count.','runtime':'Original work default; same-thread continuation gpt-6-astra/xhigh/ultrafast; terminal receipt confirms ultrafast.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
