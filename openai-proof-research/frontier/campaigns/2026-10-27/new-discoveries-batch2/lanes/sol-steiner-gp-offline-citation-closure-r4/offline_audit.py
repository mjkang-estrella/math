from setup import *
import re
R=HERE/'inputs/sol-steiner-gp-fixed-gap-closure-r3'
PAT=re.compile(rb'steiner|general.position|false.twin|independent.{0,30}(substitution|fibe?r)|maximum.{0,20}arity|lexicographic|n.ary.transit',re.I)
def blocks(p):
 block=[]
 with p.open('rb') as f:
  for line in f:
   if line.startswith(b'diff --git '):
    if block:yield block
    block=[line]
   elif block:block.append(line)
  if block:yield block
def parse(lines):
 m=re.match(rb'diff --git a/(.*?) b/(.*?)\r?\n',lines[0]);assert m
 a,b=[x.decode() for x in m.groups()];t=b''.join(lines)
 ix=re.search(rb'^index ([0-9a-f]+)\.\.([0-9a-f]+)',t,re.M)
 rec={'old_path':a,'new_path':b,'added':b'new file mode ' in t,'deleted':b'deleted file mode ' in t,'renamed':b'rename from ' in t,'sha256':hashlib.sha256(t).hexdigest(),'old_blob_prefix':ix[1].decode() if ix else None,'new_blob_prefix':ix[2].decode() if ix else None}
 h=None;new=bytearray();hunks=0
 for l in lines[1:]:
  if l.startswith(b'@@ '):
   assert h is None or h==[0,0],(a,h)
   q=re.match(rb'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',l);assert q
   h=[int(q[2] or b'1'),int(q[4] or b'1')];hunks+=1;continue
  if h is not None and h!=[0,0]:
   if l.startswith(b'\\'):continue
   if l[:1]==b' ':h[0]-=1;h[1]-=1
   elif l[:1]==b'-':h[0]-=1
   elif l[:1]==b'+':h[1]-=1;new.extend(l[1:])
   else:raise ValueError((a,l[:100]))
   assert min(h)>=0,(a,h)
  elif l.startswith(b'\\ No newline') and rec['added'] and new.endswith(b'\n'):new=new[:-1]
 assert h is None or h==[0,0],(a,h)
 rec['hunks']=hunks
 if rec['added']:
  digest=hashlib.sha1(b'blob '+str(len(new)).encode()+b'\0'+new).hexdigest()
  rec.update(reconstructed_blob_sha1=digest,reconstructed_bytes=len(new),blob_prefix_matches=digest.startswith(rec['new_blob_prefix']))
  assert rec['blob_prefix_matches'],a
 rec['hits']=[l.decode(errors='replace').rstrip()[:800] for l in lines if PAT.search(l)][:20]
 return rec
def main():
 cs=json.loads((HERE/'cache-inspection.json').read_text())['commits'];trees=json.loads((HERE/'tree-inventory.json').read_text());known={r.get('sha') for r in trees}
 records=[]
 for c in cs[-3:]:
  p=R/'retrieved/patches'/(c['sha']+'.patch');rs=[parse(ls) for ls in blocks(p)]
  records.append({'commit':c['sha'],'parents':c['parents'],'tree':c['tree'],'mail_commits':c['mail_commits'],'single_parent_identity':len(c['parents'])==1 and c['mail_commits']==[c['sha']],'blocks':len(rs),'hunks':sum(r['hunks'] for r in rs),'added_blobs_reconstructed':sum(r['added'] for r in rs),'files':rs,'scope':'retained mail delta only; no independent whole-tree completeness certificate'})
 inherited=[]
 for p in sorted((R/'retrieved/diffs').glob('*.diff')):
  # Constant-memory census, without duplicating the 50MB merge or loading it.
  counts={'blocks':0,'hunks':0,'deleted':0,'renamed':0}
  with p.open('rb') as f:
   for l in f:
    for key,prefix in [('blocks',b'diff --git '),('hunks',b'@@ '),('deleted',b'deleted file mode '),('renamed',b'rename from ')]:
     if l.startswith(prefix):counts[key]+=1
  inherited.append({'file':str(p.relative_to(HERE)),'sha256':sha(p),**counts})
 missing=[{'commit':c['sha'],'root_tree':c['tree'],'local_object_available':c['tree_available'],'cached_tree_listing_available':c['tree'] in known,'parents':c['parents']} for c in cs]
 result={'utc':utc(),'decision':'HOLD','historical_obligation':'PARKED_NO_NETWORK','intervals':json.loads((R/'interval-commits.json').read_text()),'missing_tree_inventory':missing,'retained_diff_census':inherited,'new_mail_delta_audit':records,'merge_obstruction':{'commit':cs[-2]['sha'],'required_first_parent_tree':cs[5]['tree'],'required_result_tree':cs[-2]['tree'],'second_parent_tree':cs[-3]['tree'],'series_omits_merges':['33d754fecd367341f227f360a48b2addf5d3c2e4','571770afec02c8481de48ea9eddd31a6c5f15604'],'reason':'Series enumerates side-branch nonmerge edits only. No result-tree listing or commit object binds the paths/modes/content retained, removed, renamed or resolved at the merge. A commit/tree hash alone cannot recover those bytes. Large side-branch diffs start on a different parent lineage; concatenation does not supply the absent target tree.'},'independent_complete_coverage_certificate':False,'body_screen_scope':'Newly available single-parent mail deltas only; inherited selected-body judgments reused, not re-reviewed. No complete historical body screen certified.'}
 save('offlinecoverage.json',result)
 print(json.dumps({'decision':result['decision'],'diffs':len(inherited),'blocks':sum(r['blocks'] for r in inherited),'hunks':sum(r['hunks'] for r in inherited),'new_mail_deltas':[{k:r[k] for k in ['commit','single_parent_identity','blocks','hunks','added_blobs_reconstructed']} for r in records],'hits':[(r['commit'],f['new_path'],f['hits'][:2]) for r in records for f in r['files'] if f['hits']]}))
if __name__=='__main__':main()
