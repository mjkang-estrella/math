"""One-time own-packet seal with identical read-only preflight logic."""
import argparse,importlib.util,json,sys
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bn')
spec=importlib.util.spec_from_file_location('packet_verify',ROOT/'verify.py');V=importlib.util.module_from_spec(spec);spec.loader.exec_module(V)
def prepare(root,kind):
 fs,ds=V.inventory(root)
 assert 'MANIFEST.json' not in fs and 'REPORT.md' not in fs,'already has seal envelopes'
 records=[]
 for name in sorted(fs):
  b=(root/name).read_bytes();records.append({'path':name,'bytes':len(b),'sha256':V.sha(b),'mode':fs[name]})
 names=[r['path'] for r in records];assert names==sorted(set(names))
 m={'version':1,'kind':kind,'manifest_mode':33188,'report_mode':33188,
 'directories':[{'path':p,'mode':ds[p]} for p in sorted(ds)],'files':records}
 if kind=='r162bn':m.update(pin=V.PIN,tree_sha256=V.TREE)
 mb=(json.dumps(m,indent=2,ensure_ascii=False)+'\n').encode();mh=V.sha(mb);fh=V.sha((root/'FINAL.md').read_bytes())
 report=('# Detached artifact report\n\n'
 'This report is outside the manifest payload but inside the authorized root.\n'
 'It is authenticated by an explicit external REPORT SHA256 anchor.\n\n'
 f'FINAL SHA256: {fh}\nMANIFEST SHA256: {mh}\n\n'
 f'Payload files: {len(records)}. Whole-root files: {len(records)+2}. Directories including root: {len(ds)}.\n'
 'Exact membership, sorted unique records, bytes, lengths and full modes use the same read-only verification logic in preflight and final verification.\n'
 'For the research packet that logic also checks all pinned source blobs against the complete tree, primary download bindings, and all five exact completed-original copies/modes.\n'
 'Tiny copied-control outcomes were recorded before sealing. These checks authenticate artifacts; they are not mathematical grades or gates.\n'
 'No sealed payload is changed to accommodate a verifier.\n').encode()
 rh=V.sha(report)
 result=V.verify(root,mh,fh,rh,Path('.'),{'MANIFEST.json':mb,'REPORT.md':report})
 return mb,report,mh,fh,rh,result
def write(root,prepared):
 mb,rb,mh,fh,rh,result=prepared
 for name,b in [('MANIFEST.json',mb),('REPORT.md',rb)]:
  with (root/name).open('xb') as f:f.write(b)
 return V.verify(root,mh,fh,rh,Path('.'))
p=argparse.ArgumentParser();p.add_argument('action',choices=['controls','seal']);a=p.parse_args()
if a.action=='controls':
 d=ROOT/'private/tiny-control';d.mkdir(exist_ok=False)
 (d/'FINAL.md').write_bytes(b'Tiny copied artifact control, no mathematical claim.\n')
 (d/'sample.txt').write_bytes((ROOT/'private/DERIVATION.md').read_bytes()[:96])
 pre=prepare(d,'tiny-control');write(d,pre);mh,fh,rh=pre[2:5]
 out={'good':V.verify(d,mh,fh,rh,Path('.'))}
 def rejects(label,call):
  try:call()
  except AssertionError:out[label]='REJECTED'
  else:raise AssertionError('control unexpectedly accepted: '+label)
 rejects('wrong_report_anchor',lambda:V.verify(d,mh,fh,'0'*64,Path('.')))
 old=(d/'sample.txt').read_bytes();(d/'sample.txt').write_bytes(old+b'x')
 rejects('changed_copied_byte',lambda:V.verify(d,mh,fh,rh,Path('.')))
 (d/'sample.txt').write_bytes(old)
 oldmode=(d/'sample.txt').stat().st_mode;(d/'sample.txt').chmod(0o600)
 rejects('changed_full_mode',lambda:V.verify(d,mh,fh,rh,Path('.')))
 (d/'sample.txt').chmod(oldmode & 0o7777)
 out['restored']=V.verify(d,mh,fh,rh,Path('.'))
 (ROOT/'private/control-results.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(out,sort_keys=True))
else:
 assert (ROOT/'private/control-results.json').is_file()
 pre=prepare(ROOT,'r162bn');result=write(ROOT,pre)
 print(json.dumps({'FINAL_SHA256':pre[3],'MANIFEST_SHA256':pre[2],'REPORT_SHA256':pre[4],'verification':result},indent=2))
