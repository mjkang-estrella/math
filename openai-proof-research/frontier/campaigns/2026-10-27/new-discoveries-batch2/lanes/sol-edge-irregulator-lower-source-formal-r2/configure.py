from pathlib import Path
import zipfile,hashlib,json
R=Path(__file__).parent/'component'
mods=['Source','Boundary','Gadget','Edges','Degrees','Local','Lower','Transport','Refutation','Charges']
old="['Source','Boundary','Gadget','Edges','Degrees']"
for fn in ['OriginAudit','AuditPrint']:
 p=R/'formal'/f'{fn}.lean';s=p.read_text().replace('import Degrees','import Refutation\nimport Charges').replace('#[`Source, `Boundary, `Gadget, `Edges, `Degrees]','#[`Source, `Boundary, `Gadget, `Edges, `Degrees, `Local, `Lower, `Transport, `Refutation, `Charges]');p.write_text(s)
p=R/'replay.py';s=p.read_text().replace(old,repr(mods)).replace('COMPONENT_REPLAY_PASS_SOURCE_INCOMPLETE','SOURCE_REFUTATION_REPLAY_PASS').replace('Partial graph definitions, minimum equivalence, size and connectivity, local certificates and retained-neighbor sets; no source refutation','Unconditional source negation and minimum formulation, actual degrees, disjoint actual charges, and isomorphism transport');p.write_text(s)
p=R/'package.py';s=p.read_text().replace(old,repr(mods));p.write_text(s)
p=R/'guard.py';s=p.read_text();s=s.replace("name=sys.argv[1]; cmd=", "name=sys.argv[1]\narchive=ROOT/'attempts';archive.mkdir(exist_ok=True)\ncount=len(list(archive.glob(name+'-*.lean')))\nfor ext,folder in [('lean','formal'),('log','logs'),('json','logs')]:\n f=ROOT/folder/(name+'.'+ext)\n if f.exists():(archive/(name+'-'+str(count)+'.'+ext)).write_bytes(f.read_bytes())\ncmd=")
p.write_text(s)
with zipfile.ZipFile(R.parent/'inherited.zip') as z:
 original=json.loads(z.read('manifest.json'))
 for n in ['Source','Boundary','Gadget','Edges','Degrees']:
  f='formal/'+n+'.lean';assert (R/f).read_bytes()==z.read(f)
 for n,h in original.items():assert hashlib.sha256(z.read(n)).hexdigest()==h
(R/'inheritance-check.json').write_text(json.dumps({'frozen_archive_sha256':hashlib.sha256((R.parent/'inherited.zip').read_bytes()).hexdigest(),'all_inherited_manifest_entries_verified':True,'five_mathematical_sources_byte_identical':True},indent=2)+'\n')
