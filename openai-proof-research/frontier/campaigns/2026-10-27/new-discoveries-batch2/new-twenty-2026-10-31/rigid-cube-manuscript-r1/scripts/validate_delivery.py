from pathlib import Path
import json,zipfile,hashlib,os
D=Path(__file__).resolve().parents[1]
def h(b):return hashlib.sha256(b).hexdigest()
assert not list(D.rglob('*.olean'))
for archive,manifest in [('source-only.zip','source-manifest.json'),('full-dossier.zip','dossier-manifest.json')]:
 with zipfile.ZipFile(D/archive) as z:
  m=json.loads(z.read(manifest));assert len(z.namelist())==len(m)+1
  for n,digest in m.items():assert h(z.read(n))==digest,(archive,n)
assert json.loads((D/'fresh-extraction-manifest-check.json').read_text())['archive_sha256']==h((D/'source-only.zip').read_bytes())
m=json.loads((D/'archive-hashes.json').read_text());assert all(h((D/n).read_bytes())==v for n,v in m.items())
assert (D/'independent-certificate.json').read_bytes()==(D/'fresh-replay/independent-certificate.json').read_bytes()
anc=set();p=os.getpid()
while p>1:
 anc.add(p)
 try:p=int(Path(f'/proc/{p}/stat').read_text().split(') ',1)[1].split()[1])
 except OSError:break
jobs=[]
for q in Path('/proc').glob('[0-9]*'):
 try:
  if int(q.name) in anc:continue
  cwd=(q/'cwd').resolve();cmd=(q/'cmdline').read_bytes().replace(b'\x00',b' ').decode(errors='replace')
  if cwd.is_relative_to(D):jobs.append({'pid':q.name,'command':cmd})
 except (OSError,ValueError):pass
assert not jobs,jobs
r={'status':'PASS','archive_entries_verified':True,'exact_delivered_source_archive_replayed':True,'both_source_and_full_manifests_verified':True,'no_oleans_remaining':True,'fresh_coordinate_certificate_identical':True,'no_running_lane_jobs':True,'jobs':jobs}
(D/'final-validation.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
