import json,hashlib,zipfile
from pathlib import Path
r=Path(__file__).parent
mods=['Source','Boundary','Gadget','Edges','Degrees','UpperWitness','UpperDegrees','Upper']
p=r/'replay.py';s=p.read_text().replace("MODULES=['Source','Boundary','Gadget','Edges','Degrees']",'MODULES='+repr(mods)).replace("'COMPONENT_REPLAY_PASS_SOURCE_INCOMPLETE'","'UPPER_WITNESS_REPLAY_PASS'").replace('Partial graph definitions, minimum equivalence, size and connectivity, local certificates and retained-neighbor sets; no source refutation','Unconditional actual deletion witness, all retained neighbors/degrees and minimum upper bound for t>=2; no lower bound or source refutation')
p.write_text(s)
p=r/'replay_guard.py';s=p.read_text().replace("'NUMEXPR_NUM_THREADS'","'NUMEXPR_NUM_THREADS','BLIS_NUM_THREADS'").replace(' rss=cpu=0',' sample_start=time.monotonic()\n rss=cpu=0').replace('time.sleep(.04)','time.sleep(max(0,.04-(time.monotonic()-sample_start)))');p.write_text(s)
# Byte identity of all inherited mathematical source files against frozen packet.
zpath=r.parent/'sol-edge-irregulator-source-formal-r1/edge-irregulator-component.zip'
assert hashlib.sha256(zpath.read_bytes()).hexdigest()=='74e2c9ead42007930c623531d4ee290865cf41d245f520ca7bff8270a9fd2f74'
with zipfile.ZipFile(zpath) as z:
 manifest=json.loads(z.read('manifest.json'))
 for n,h in manifest.items(): assert hashlib.sha256(z.read(n)).hexdigest()==h,n
 checks={m:hashlib.sha256((r/'formal'/f'{m}.lean').read_bytes()).hexdigest() for m in mods[:5]}
 for m in mods[:5]: assert (r/'formal'/f'{m}.lean').read_bytes()==z.read(f'formal/{m}.lean')
(r/'inherited-identity.json').write_text(json.dumps({'frozen_archive_sha256':hashlib.sha256(zpath.read_bytes()).hexdigest(),'five_mathematical_sources_byte_identical':checks,'all_frozen_manifest_entries_verified':True},indent=2)+'\n')
