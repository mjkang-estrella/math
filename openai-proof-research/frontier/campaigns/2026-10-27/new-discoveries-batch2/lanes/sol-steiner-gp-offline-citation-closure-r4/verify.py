from setup import *
from offline_audit import blocks,parse
import re
def main():
 b=json.loads((HERE/'before.json').read_text());a=json.loads((HERE/'after.json').read_text());assert len(b['files'])==len(a['files'])==617
 for r in b['files']:
  for p in [pathlib.Path(r['path']),HERE/r['copy']]:assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
 for r in b['freezes']:assert sha(r['path'])==r['sha256']
 g=json.loads((HERE/'guard-binding.json').read_text());assert sha(g['path'])==g['sha256']
 oc=json.loads((HERE/'offlinecoverage.json').read_text());assert oc['decision']=='HOLD' and not oc['independent_complete_coverage_certificate']
 R=HERE/'inputs/sol-steiner-gp-fixed-gap-closure-r3'
 assert [x['total'] for x in oc['intervals']]==[6,8]
 for rec in oc['new_mail_delta_audit']:
  p=R/'retrieved/patches'/(rec['commit']+'.patch');actual=[parse(x) for x in blocks(p)];assert actual==rec['files']
  with p.open('rb') as f:heads=[l.split()[1].decode() for l in f if re.match(rb'^From [a-f0-9]{40} Mon Sep',l)]
  assert heads==rec['mail_commits']
 for rec in oc['retained_diff_census']:
  p=HERE/rec['file'];assert sha(p)==rec['sha256'];nb=nh=nd=nr=0
  with p.open('rb') as f:
   for l in f:nb+=l.startswith(b'diff --git ');nh+=l.startswith(b'@@ ');nd+=l.startswith(b'deleted file mode ');nr+=l.startswith(b'rename from ')
  assert [nb,nh,nd,nr]==[rec[x] for x in ['blocks','hunks','deleted','renamed']]
 cd=json.loads((HERE/'citationdecisions.json').read_text());assert cd['classified_count_retained']==17 and [r['record'] for r in cd['new_decisions']]==[10,19] and all(r['decision']=='HOLD' for r in cd['new_decisions'])
 for line in (HERE/'access-receipts.jsonl').read_text().splitlines():
  r=json.loads(line)
  if 'sha256' in r:assert sha(HERE/r['file'])==r['sha256']
 m=json.loads((HERE/'final-manifest.json').read_text());expected={r['path'] for r in m['files']};actual={str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file() and str(p.relative_to(HERE)) not in m['exclusions']};assert expected==actual
 for r in m['files']:assert (HERE/r['path']).stat().st_size==r['bytes'] and sha(HERE/r['path'])==r['sha256'],r['path']
 receipt={'utc':utc(),'integrity':'CLEAR_BOUNDED','evidence_closure':'HOLD','originals':617,'manifest_entries':len(m['files']),'manifest_sha256':sha(HERE/'final-manifest.json'),'replayed_new_mail_blocks':446,'retained_diff_blocks':sum(r['blocks'] for r in oc['retained_diff_census']),'retained_hunks':sum(r['hunks'] for r in oc['retained_diff_census']),'no_coverage_pass_inferred':True}
 save('final-verification.json',receipt);print(json.dumps(receipt))
if __name__=='__main__':main()
