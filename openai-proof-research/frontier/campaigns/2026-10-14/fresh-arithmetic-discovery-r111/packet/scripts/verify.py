"""Offline, read-only verification. Requires three independent detached anchors.
No writes, network, imports of preparation scripts, repairs, or resealing.
--integrity-only is for explicitly reduced copied-control fixtures.
"""
import argparse,hashlib,json,os,subprocess,sys
from pathlib import Path,PurePosixPath

def sha(b):return hashlib.sha256(b).hexdigest()
def digest(p):return sha(p.read_bytes())
def safe(s):
 p=PurePosixPath(s)
 assert not p.is_absolute() and '..' not in p.parts and str(p)==s and s not in ('','.');return p

def inventory(base):
 files={};dirs=[]
 for d,ds,fs in os.walk(base,followlinks=False):
  for n in ds+fs:assert not (Path(d)/n).is_symlink(),f'symlink: {n}'
  for n in ds:dirs.append((Path(d)/n).relative_to(base).as_posix())
  for n in fs:
   f=Path(d)/n;assert f.is_file();files[f.relative_to(base).as_posix()]={'size':f.stat().st_size,'sha256':digest(f)}
 return files,sorted(dirs)

def main():
 a=argparse.ArgumentParser();a.add_argument('--root',type=Path,required=True)
 for n in ['final','manifest','report']:a.add_argument('--'+n+'-sha256',required=True)
 a.add_argument('--integrity-only',action='store_true');a.add_argument('--originals',type=Path)
 args=a.parse_args();root=args.root
 assert set(x.name for x in root.iterdir())=={'packet','FINAL.json','MANIFEST.json','REPORT.md'},'root membership'
 for n,h in [('FINAL.json',args.final_sha256),('MANIFEST.json',args.manifest_sha256),('REPORT.md',args.report_sha256)]:
  assert not (root/n).is_symlink();assert digest(root/n)==h,f'detached anchor {n}'
 fin=json.loads((root/'FINAL.json').read_text());out=json.loads((root/'MANIFEST.json').read_text())
 assert fin['manifest_sha256']==args.manifest_sha256 and fin['report_sha256']==args.report_sha256
 packet=root/'packet';assert not packet.is_symlink()
 pm=packet/'manifest.json';ph=digest(pm)
 assert ph==fin['packet_manifest_sha256']==out['packet_manifest_sha256']
 assert out['report_sha256']==args.report_sha256
 m=json.loads(pm.read_text());actual,dirs=inventory(packet);actual.pop('manifest.json')
 assert dirs==m['directories'],'directory membership'
 assert [x['path'] for x in m['files']]==sorted(actual),'exact file membership/order'
 assert len(m['files'])==fin['payload_count']
 for x in m['files']:
  safe(x['path']);assert actual[x['path']]=={k:x[k] for k in ['size','sha256']},'payload mismatch: '+x['path']
 checks={'payloads':len(actual),'directories':len(dirs),'detached_envelopes':3,'scope':'artifact integrity only'}
 if not args.integrity_only:
  tb=(packet/'private/context/preprints-tree.json').read_bytes()
  assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
  tree=json.loads(tb)['tree'];assert len(tree)==13223
  by={x['path']:x for x in tree};pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
  src=json.loads((packet/'private/source/metadata.json').read_text())
  for x in src:
   safe(x['path']);b=(packet/'private/source'/x['path']).read_bytes();t=by[x['path']]
   blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
   assert len(b)==x['size']==t['size'] and blob==x['git_blob']==t['sha'] and sha(b)==x['sha256']
   assert x['url']=='https://raw.githubusercontent.com/openai/math/'+pin+'/'+x['path']
  prim=json.loads((packet/'private/primary/metadata.json').read_text())
  for x,name in zip(prim,['EEL2020','Pauli-Roblot2001'],strict=True):
   f=packet/'private/primary'/name
   assert digest(f.with_suffix('.pdf'))==x['sha256'] and f.with_suffix('.pdf').stat().st_size==x['size']
   assert digest(f.with_suffix('.txt'))==x['text_sha256'] and x['extraction_exit']==0
  hist=json.loads((packet/'private/history/metadata.json').read_text());original_count=0
  for x in hist:
   safe(x['snapshot']);assert digest(packet/x['snapshot'])==x.get('snapshot_sha256',x['sha256'])
   if args.originals:
    safe(x['path']);b=(args.originals/x['path']).read_bytes()
    if x.get('snapshot_is_excerpt'):
     b=b[b.index(b'## Acceptance and publication'):b.index(b'## Model allocation')]
     assert sha(b)==x['snapshot_sha256'],'current acceptance excerpt drift'
    else:assert len(b)==x['size'] and sha(b)==x['sha256'],'current named original drift: '+x['path']
    original_count+=1
  d=subprocess.run([sys.executable,'-B',str(packet/'scripts/diagnostics.py')],capture_output=True,text=True,check=True)
  assert json.loads(d.stdout)==json.loads((packet/'notes/diagnostics.json').read_text())
  checks.update(source_blobs=len(src),tree_entries=len(tree),primary_pairs=len(prim),history_snapshots=len(hist),current_named_original_checks=original_count,finite_diagnostics='replayed')
 print(json.dumps({'status':'verified','checks':checks},sort_keys=True))
if __name__=='__main__':
 try:main()
 except Exception as e:
  print(json.dumps({'status':'rejected','error':str(e)},sort_keys=True));sys.exit(1)
