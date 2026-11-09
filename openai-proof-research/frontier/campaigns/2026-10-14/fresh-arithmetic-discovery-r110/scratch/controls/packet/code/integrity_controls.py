"""Small copied controls. Writes only under this packet's scratch directory."""
import argparse,json,shutil,subprocess,sys
from pathlib import Path
from verify import digest, inventory, OUTER
r=Path(__file__).resolve().parents[1]
ap=argparse.ArgumentParser()
for k in ['final','manifest','report']:ap.add_argument('--'+k+'-hash',required=True)
a=ap.parse_args();args=['--final-hash',a.final_hash,'--manifest-hash',a.manifest_hash,'--report-hash',a.report_hash]
copy=r/'scratch/controls/packet';copy.mkdir(parents=True,exist_ok=False)
original_names=inventory(r)+sorted(OUTER)
original_before={n:digest((r/n).read_bytes()) for n in original_names}
for n in original_names:
    q=copy/n;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(r/n,q)
def state():return {n:digest((copy/n).read_bytes()) for n in inventory(copy)+sorted(OUTER)}
results=[]
def check(name,expected,extra=None):
    before=state()
    p=subprocess.run([sys.executable,'-B',str(r/'code/verify.py'),str(copy)]+(extra or args),capture_output=True,text=True,timeout=30)
    assert (p.returncode==0)==expected,(name,p.stdout,p.stderr)
    assert before==state(),'verifier wrote files'
    results.append({'case':name,'accepted':p.returncode==0,'read_only':True,'stdout':p.stdout,'stderr':p.stderr})
check('baseline',True)
target=copy/'notes/kurosh-feasibility.md';old=target.read_bytes()
target.write_bytes(old+b'\nmutation\n');check('changed payload',False);target.write_bytes(old)
target.unlink();check('missing payload',False);target.write_bytes(old)
extra=copy/'.unexpected';extra.write_text('extra\n');check('hidden extra',False);extra.unlink()
wrong=args.copy();wrong[1]='0'*64;check('wrong external FINAL anchor',False,wrong)
check('restored',True)
assert original_before=={n:digest((r/n).read_bytes()) for n in inventory(r)+sorted(OUTER)},'original packet changed'
# Current named originals comparison; no historical/whole-parent certificate.
history=[]
for e in json.loads((r/'private/history/metadata.json').read_text()):
    p=r.parents[3]/e['original'];data=p.read_bytes()
    want=e.get('whole_original_sha256',e.get('sha256'))
    history.append({'path':e['original'],'matches_late_snapshot':digest(data)==want})
result={'controls':results,'original_packet_unchanged':True,'named_originals_current_comparison':history,'scope':'artifact controls only; no mathematical gate, historical whole-parent or OS certificate'}
(r/'scratch/controls/results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'cases':len(results),'all_expected':True,'original_packet_unchanged':True,'named_originals_matching':sum(e['matches_late_snapshot'] for e in history),'named_originals_compared':len(history)}))
