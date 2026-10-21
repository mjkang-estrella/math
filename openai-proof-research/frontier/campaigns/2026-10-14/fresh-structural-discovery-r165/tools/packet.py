"""Own-root sealing and a small copied fixture; never opens protected peer bodies."""
import hashlib,json,os,stat,sys,shutil,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.dont_write_bytecode=True
from verify_packet import inventory,ENVELOPES,digest

def seal(root):
 if (root/'MANIFEST.json').exists():raise RuntimeError('refuse second seal')
 for cur,ds,fs in os.walk(root,topdown=False):
  for f in fs:(Path(cur)/f).chmod(0o444)
  Path(cur).chmod(0o555)
 files,dirs=inventory(root)
 for name in ENVELOPES:files.pop(name,None)
 # Temporarily allow writing only the new envelope, then restore recorded root mode.
 root.chmod(0o755)
 m={'format':1,'envelopes':list(ENVELOPES),'files':files,'directories':dirs}
 (root/'MANIFEST.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
 (root/'MANIFEST.json').chmod(0o444);root.chmod(0o555)
 return [digest(root/n) for n in ENVELOPES]
def replay(root,anchors):
 r=subprocess.run([sys.executable,'-B',str(root/'tools/verify_packet.py'),str(root),'--final-sha256',anchors[0],'--manifest-sha256',anchors[1],'--report-sha256',anchors[2]],capture_output=True,text=True)
 return r.returncode==0

def controls():
 fixture=ROOT/'private/controls/selected-fixture';fixture.mkdir(parents=True)
 for rel in ['notes/02-integrated-calculation.md','private/source/main.tex','tools/verify_packet.py']:
  dst=fixture/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/rel,dst)
 (fixture/'FINAL.md').write_text('Selected three-file artifact fixture only; no inherited original manifest.\n')
 (fixture/'REPORT.md').write_text('Copied byte controls, not mathematical gates.\n')
 anchors=seal(fixture);results=[]
 def test(name,want):
  got=replay(fixture,anchors);assert got==want,(name,got);results.append({'case':name,'expected':want,'observed':got})
 test('baseline',True)
 p=fixture/'notes/02-integrated-calculation.md';original=p.read_bytes();p.chmod(0o644);p.write_bytes(original+b'altered\n');p.chmod(0o444);test('payload-change',False);p.chmod(0o644);p.write_bytes(original);p.chmod(0o444)
 p.parent.chmod(0o755);p.unlink();p.parent.chmod(0o555);test('missing-member',False);p.parent.chmod(0o755);p.write_bytes(original);p.chmod(0o444);p.parent.chmod(0o555)
 fixture.chmod(0o755);extra=fixture/'extra';extra.write_text('x');extra.chmod(0o444);fixture.chmod(0o555);test('extra-member',False);fixture.chmod(0o755);extra.unlink();fixture.chmod(0o555)
 fixture.chmod(0o755);extra.symlink_to('FINAL.md');fixture.chmod(0o555);test('symlink',False);fixture.chmod(0o755);extra.unlink();fixture.chmod(0o555)
 for i,name in enumerate(ENVELOPES):
  wrong=list(anchors);wrong[i]='0'*64;got=replay(fixture,wrong);assert not got;results.append({'case':'bad-detached-'+name,'expected':False,'observed':got})
 test('restored',True)
 (ROOT/'private/controls/results.json').write_text(json.dumps({'fixture_own_detached_anchors':dict(zip(ENVELOPES,anchors)),'controls':results},indent=2)+'\n')
 print(json.dumps({'copied_controls':len(results),'all_expected_outcomes':True}))
if __name__=='__main__':
 if sys.argv[1:] == ['controls']:controls()
 elif sys.argv[1:] == ['seal']:
  anchors=seal(ROOT);assert replay(ROOT,anchors);print(json.dumps({'detached_anchors':dict(zip(ENVELOPES,anchors))},indent=2))
 else:raise SystemExit('controls or seal required')
