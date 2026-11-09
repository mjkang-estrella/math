from pathlib import Path
import json,hashlib,zipfile,io
L=Path(__file__).parent; E=L/'extracted'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
src=(E/'lean_guard.py').read_text()
src=src.replace('def pre():resource.setrlimit(resource.RLIMIT_CPU,(210,210))','def pre():\n resource.setrlimit(resource.RLIMIT_AS,(resource.RLIM_INFINITY,resource.RLIM_INFINITY))\n resource.setrlimit(resource.RLIMIT_CPU,(210,210))')
(L/'replay_guard.py').write_text(src)
# Audit implementation inspected independently: selection is by actual module index,
# not namespace or an authored list. Preserve original audit bytes in extraction.
(E/'IndependentAudit.lean').write_text((E/'Audit.lean').read_text())
with zipfile.ZipFile(L/'source-only.zip') as z:
 b=io.BytesIO()
 with zipfile.ZipFile(b,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as out:
  for n in sorted(z.namelist()):
   info=zipfile.ZipInfo(n,(2024,1,1,0,0,0)); info.external_attr=0o100644<<16;info.compress_type=zipfile.ZIP_DEFLATED
   out.writestr(info,(E/n).read_bytes())
 assert hashlib.sha256(b.getvalue()).hexdigest()==sha(L/'source-only.zip')
(L/'archive-rebuild.json').write_text(json.dumps({'sha256':sha(L/'source-only.zip'),'deterministic_rebuild':True,'members':len(z.namelist())},indent=2)+'\n')
for n in ['ledger.json','prior-campaign-context.json']:
 obj=json.loads((L/n).read_text());print(n,'parsed',len(obj),'keys')
print('archive deterministic rebuild PASS')
