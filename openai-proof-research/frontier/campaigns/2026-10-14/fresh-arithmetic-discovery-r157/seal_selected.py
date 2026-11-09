from pathlib import Path
import hashlib,json,stat,shutil,subprocess
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r157');P=R/'packet'
def sha(b):return hashlib.sha256(b).hexdigest()
def enc(x):return (json.dumps(x,indent=2,sort_keys=True)+'\n').encode()
def inventory(p):
 out=[]
 for f in sorted(p.rglob('*')):
  assert not f.is_symlink()
  if f.is_file():
   b=f.read_bytes();out.append({'path':f.relative_to(p).as_posix(),'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(f.stat().st_mode)})
 return out
# Tiny synthetic copied controls, never a copy of the real research packet.
C=P/'private/controls';C.mkdir(exist_ok=True);gold=C/'golden';(gold/'packet').mkdir(parents=True)
(gold/'packet/FINAL.md').write_text('Tiny artifact fixture. No mathematics.\n');(gold/'packet/data.txt').write_text('abc\n')
mb=enc({'files':inventory(gold/'packet')});(gold/'MANIFEST.json').write_bytes(mb)
f=sha((gold/'packet/FINAL.md').read_bytes());m=sha(mb);rb=enc({'final_sha256':f,'manifest_sha256':m});(gold/'REPORT.json').write_bytes(rb);rr=sha(rb)
results=[]
for name in ['golden','changed','missing','extra']:
 target=C/name
 if name!='golden':shutil.copytree(gold,target)
 if name=='changed':(target/'packet/data.txt').write_text('abd\n')
 if name=='missing':(target/'packet/data.txt').unlink()
 if name=='extra':(target/'packet/extra.txt').write_text('unexpected\n')
 cmd=['python','-B',str(P/'verify_packet.py'),str(target),'--final-sha256',f,'--manifest-sha256',m,'--report-sha256',rr]
 proc=subprocess.run(cmd,capture_output=True,text=True)
 assert (proc.returncode==0)==(name=='golden'),name
 results.append({'control':name,'exit_code':proc.returncode,'expected_match':name=='golden','observed':proc.stdout.strip() if proc.returncode==0 else proc.stderr.strip().splitlines()[-1]})
(P/'private/controls-results.json').write_bytes(enc(results))
# Seal the exact newly selected packet ONCE, with detached files outside it.
mb=enc({'schema':'r157-exact-selected-packet-v1','files':inventory(P)})
with (R/'MANIFEST.json').open('xb') as h:h.write(mb)
f=sha((P/'FINAL.md').read_bytes());m=sha(mb)
report={'schema':'r157-handoff-v1','disposition':'PREFREEZE / no nominee','theorem_frozen':False,'provenance':'Codex / GPT-6 Astra / high / default service tier','pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','source_blobs_authenticated':23,'source_text_blobs_fully_read':14,'final_sha256':f,'manifest_sha256':m,'mathematical_notes':['notes/01-operative-comparison.md','notes/02-integrated-scaling-reduction.md','notes/03-admissible-returns-and-unpaid-operation.md'],'unpaid':'A full-scope admissible boundary return or compatible moving-center/multiple-scale construction retaining a noncollapsed interior anchor and two-sided control. No weaker substitute nominated.','reading_limits':'packet/private/READING-ISOLATION.md and extent JSONs','controls':'Four tiny synthetic copied artifact controls behaved as expected; not mathematical gates.','rights':'Protected bodies and named metadata private/local under original rights.','scope':'Parent alone integrates and assigns grades, acceptance and count.'}
rb=enc(report)
with (R/'REPORT.json').open('xb') as h:h.write(rb)
rr=sha(rb);anchors={'FINAL_SHA256':f,'MANIFEST_SHA256':m,'REPORT_SHA256':rr}
with (R/'DETACHED-ANCHORS.json').open('xb') as h:h.write(enc(anchors))
print(json.dumps(anchors,indent=2))
proc=subprocess.run(['python','-B',str(P/'verify_packet.py'),str(R),'--final-sha256',f,'--manifest-sha256',m,'--report-sha256',rr],capture_output=True,text=True,check=True)
with (R/'VERIFY.txt').open('x') as h:h.write(proc.stdout)
print(proc.stdout)
