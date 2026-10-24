#!/usr/bin/env python3
"""Read-only artifact intake. Tiny mutations are isolated from sealed originals."""
from pathlib import Path
import datetime,hashlib,json,os,runpy,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;A=P.parent/'fresh-structural-discovery-r231';S=A/'packet';C=P.parents[1];PROJECT=C.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'FINAL.md':'97f7a651c51c7e0244450cdabbba085ee8610ad5b1b412e0f53fc8baf0fb8869','MANIFEST.json':'e9be2ee4ccca55cdedd87eed08f7d9ed03bbf1153f7ce6e558301a8736dc676a','REPORT.md':'57279d7f00d2398d505cc4f9f1117e63b47c5109d0df10498caaef35918ba75c'}
def inventory(root):
 out={'files':{},'directories':{},'root_mode':stat.S_IMODE(root.stat().st_mode)}
 for base,ds,fs in os.walk(root,followlinks=False):
  for n in ds+fs:
   p=Path(base)/n;rel=p.relative_to(root).as_posix();st=p.lstat();assert not stat.S_ISLNK(st.st_mode)
   if stat.S_ISDIR(st.st_mode):out['directories'][rel]=stat.S_IMODE(st.st_mode)
   else:
    assert stat.S_ISREG(st.st_mode);b=p.read_bytes();out['files'][rel]={'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(st.st_mode)}
 return out
before=inventory(A);selected=inventory(S);m=read(S/'MANIFEST.json')
for k,n in [('FINAL','FINAL.md'),('MANIFEST','MANIFEST.json'),('REPORT','REPORT.md')]:
 e=read(A/'DETACHED-ANCHORS.json')[k];assert e['sha256']==anchors[n] and sha((A/e['path']).read_bytes())==anchors[n]
assert set(selected['files'])-{'MANIFEST.json'}=={x['path']for x in m['entries']};assert {'.':format(selected['root_mode'],'04o'),**{p:format(mode,'04o')for p,mode in selected['directories'].items()}}==m['directories']
def invoke(expected):
 r=subprocess.run([sys.executable,'-I','-B',str(S/'verify_packet.py'),'--packet',str(S),'--report',str(A/'REPORT.md'),'--final-sha256',expected['FINAL.md'],'--manifest-sha256',expected['MANIFEST.json'],'--report-sha256',expected['REPORT.md']],capture_output=True,text=True)
 return r.returncode,json.loads(r.stdout)if r.returncode==0 else r.stderr.strip()
code,verified=invoke(anchors);assert code==0
b=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(b)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(b)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree}
records=read(S/'private/source-authentication.json');assert len(records)==17
for x in records:
 b=(S/x['local']).read_bytes();e=by[x['path']];assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha'];assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'in x['url']
prefix='preprints/Tangent-flow-uniqueness-2026-09-24';assert read(S/'private/tree-selection.json')==[x for x in tree if x['path']==prefix or x['path'].startswith(prefix+'/')]
reads=[json.loads(x)for x in (S/'private/semantic-reads.jsonl').read_bytes().splitlines()]
for x in reads:
 b=(S/x['file']).read_bytes();ls=b.splitlines(keepends=True);i,j=x['line_start'],x['line_end_inclusive'];lo,hi=x['byte_start'],x['byte_end_exclusive'];assert [sum(map(len,ls[:i-1])),sum(map(len,ls[:j]))]==[lo,hi] and sha(b[lo:hi])==x['sha256']
coverage=read(S/'private/source-extent-check.json')['sections'];assert len(coverage)==13
for x in coverage:
 b=(S/x['file']).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'] and not x['gaps'];spans=sorted([r['byte_start'],r['byte_end_exclusive']]for r in reads if r['file']==x['file']);assert spans==x['recorded_intervals'];end=0
 for lo,hi in spans:assert lo<=end;end=max(end,hi)
 assert end==len(b)
primary=[json.loads(x)for x in (S/'private/primary-reads.jsonl').read_bytes().splitlines()];unmasked_lines=0
for x in primary:
 b=(S/x['file']).read_bytes();ls=b.splitlines(keepends=True);i,j=x['lines'];lo,hi=x['start'],x['end'];assert [sum(map(len,ls[:i-1])),sum(map(len,ls[:j]))]==[lo,hi] and sha(b[lo:hi])==x['sha256_unmasked_interval'];bounds=set();offset=lo
 for line in ls[i-1:j]:bounds.add((offset,offset+len(line)));offset+=len(line)
 assert all(tuple(r)in bounds for r in x['selected_ranges']);unmasked_lines+=len(x['selected_ranges'])
recovery=read(S/'private/primary/mask-recovery.json')['recovered']
for x in recovery:
 b=(S/'private/primary'/(x['file']+'.txt')).read_bytes();ls=b.splitlines(keepends=True);i=x['line'];assert [sum(map(len,ls[:i-1])),sum(map(len,ls[:i]))]==[x['start'],x['end']] and b[x['start']:x['end']].decode()==x['fragment']
access=read(S/'private/primary/access.json')+[json.loads(x)for x in (S/'private/primary/additional-access.jsonl').read_bytes().splitlines()];pdfs=[]
for x in access:
 if 'error'in x or x.get('pdf')is False:continue
 f=S/'private/primary'/(x['name']+'.pdf');b=f.read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'];assert len(f.with_suffix('.txt').read_bytes())==x['text_bytes'];pdfs.append(x['name'])
g=read(S/'private/path-guards.json');assert len(g['wildcards'])==385 and len(g['substrings'])==162
module=runpy.run_path(str(S/'verify_packet.py'));entry_check=module['verify_entries']
tiny=A/'tiny-copied-controls';fixture=tiny/'selected.txt';e={'path':'selected.txt','bytes':fixture.stat().st_size,'sha256':sha(fixture.read_bytes()),'mode':format(stat.S_IMODE(fixture.stat().st_mode),'04o')};assert sha(fixture.read_bytes())==sha((S/'SESSION.txt').read_bytes());assert entry_check(tiny,[e])==1
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='copied-controls-')as td:
 r=Path(td);f=r/'selected.txt';original=b'independent tiny copied fixture\n';f.write_bytes(original);f.chmod(0o444);entries=[dict(path='selected.txt',bytes=len(original),sha256=sha(original),mode='0444')]
 def case(label,reject=False):
  try:entry_check(r,entries);failed=False
  except ValueError:failed=True
  assert failed==reject;controls.append({'case':label,'observed':'rejected'if reject else'accepted'})
 case('valid entry selection');f.chmod(0o644);f.write_bytes(bytes([original[0]^1])+original[1:]);f.chmod(0o444);case('same-size byte mutation',True);f.chmod(0o644);f.write_bytes(original);case('file mode mutation',True);f.chmod(0o444);extra=r/'extra';extra.write_bytes(b'x');case('unselected extra file',True);extra.unlink();case('restored copied selection')
code,result=invoke(dict(anchors,**{'MANIFEST.json':'0'*64}));assert code!=0
assert inventory(A)==before;(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_files':len(m['entries']),'selected_directories_including_root':len(m['directories']),'entire_author_files':len(before['files']),'entire_author_subdirectories':len(before['directories']),'verifier':verified,'verifier_sha256':sha((S/'verify_packet.py').read_bytes()),'canonical_blobs_authenticated':len(records),'source_read_extents_bound':len(reads),'operative_sections_completely_covered_by_recorded_ranges':len(coverage),'primary_read_extents_bound':len(primary),'primary_unmasked_line_ranges_bound':unmasked_lines,'recovered_numeric_fragments_bound':len(recovery),'primary_pdfs_authenticated':pdfs,'formal_artifacts_accessed':0,'original_history_bodies_admitted':0,'author_control_log_cases':len(read(S/'private/artifact-controls.json')['results']),'author_tiny_entry_fixture_replayed':True,'independent_copied_entry_controls':controls,'full_readonly_verifier_rejected_wrong_detached_anchor':True,'author_originals_unchanged':True,'semantic_scope':'Complete authored derivations, comparison-and-limits, source-reading notes, FINAL and outside REPORT read. Read-only artifact/range checks do not inherit primary/source reading or prove the mathematical statements. Tiny helper controls test selected entries; full actual verifier separately checks directories, anchors and canonical blobs. No mathematical grades or count assigned.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
