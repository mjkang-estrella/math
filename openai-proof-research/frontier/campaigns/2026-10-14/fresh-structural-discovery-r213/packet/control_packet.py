"""Tiny copies only; never mutate selected originals."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r213');C=R/'controls';P=C/'packet'
assert not C.exists();P.mkdir(parents=True)
# Copy a short prefix of our own proof notes, not a protected or shared artifact.
original=(R/'RELATIVE-DERIVATION.md').read_bytes();payload=original[:240]
(P/'FINAL.md').write_bytes(b'Tiny artifact control, not a mathematical packet.\n')
(P/'proof.txt').write_bytes(payload)
report=C/'REPORT.md';report.write_bytes(b'Tiny copied control report.\n');report.chmod(0o444)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
items=[]
for p in sorted(P.iterdir()):
 p.chmod(0o444);items.append({'path':p.name,'bytes':p.stat().st_size,'mode':'0444','sha256':sha(p)})
m={'format':'r213-exact-packet-v1','files':items,'directories':['.']}
(P/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n');(P/'MANIFEST.json').chmod(0o444);P.chmod(0o555)
args=[sys.executable,'-B',str(R/'verify_packet.py'),'--packet',str(P),'--report',str(report),'--final-sha256',sha(P/'FINAL.md'),'--manifest-sha256',sha(P/'MANIFEST.json'),'--report-sha256',sha(report)]
results=[]
def run(name,expected):
 q=subprocess.run(args,capture_output=True,text=True);assert q.returncode==expected,(name,q.stdout,q.stderr)
 results.append({'control':name,'expected_exit':expected,'actual_exit':q.returncode,'result':json.loads(q.stdout or q.stderr)})
run('unaltered copied selection',0)
p=P/'proof.txt';p.chmod(0o644);p.write_bytes(bytes([payload[0]^1])+payload[1:]);p.chmod(0o444)
run('same-size one-byte tamper rejected',1)
p.chmod(0o644);p.write_bytes(payload);p.chmod(0o444)
P.chmod(0o755);e=P/'unexpected.txt';e.write_text('extra');e.chmod(0o444);P.chmod(0o555)
run('unlisted extra file rejected',1)
P.chmod(0o755);e.unlink();P.chmod(0o555)
p.chmod(0o644);run('mode change rejected',1);p.chmod(0o444)
run('restored copied selection',0)
assert (R/'RELATIVE-DERIVATION.md').read_bytes()==original
(R/'private/control-results.json').write_text(json.dumps({'controls_only':True,'original_proof_unchanged':True,'results':results},indent=2)+'\n')
print('Five tiny copied-control checks behaved as expected; originals unchanged.')
