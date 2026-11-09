import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(35,35))
resource.setrlimit(resource.RLIMIT_FSIZE,(64*1024**2,)*2)
import hashlib,json,shutil,datetime
from pathlib import Path
R=Path(__file__).resolve().parent; B=R.parent
base=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rev(p):
 g=p/'.git'
 if g.is_file():g=(p/g.read_text().strip().removeprefix('gitdir: ')).resolve()
 h=(g/'HEAD').read_text().strip()
 if h.startswith('ref: '):
  ref=h[5:];f=g/ref
  h=f.read_text().strip() if f.exists() else next(x.split()[0] for x in (g/'packed-refs').read_text().splitlines() if x.endswith(' '+ref))
 return h
manifest=json.loads((base/'lake-manifest.json').read_text());pins=[]
for item in manifest['packages']:
 p=base/'.lake/packages'/item['name'];actual=rev(p)
 assert actual==item['rev'],(item['name'],actual)
 pins.append({'name':item['name'],'url':item['url'],'rev':actual,'path':str(p)})
assert len(pins)==9
(R/'pins.json').write_text(json.dumps({'lean_binary':'/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean','lean_sha256':'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550','packages':pins,'manifest_sha256':sha(base/'lake-manifest.json')},indent=2)+'\n')
# Authenticate all discovery-freeze entries before consuming copied evidence.
expected={x['path']:x['expected'] for x in json.loads((B/'sol-steiner-reflection-preliminary-review-r1/freeze-before.json').read_text())['files']}
entries=[]
for name in ['PROOF.md','discovery.md','provenance.json','sources/steiner-v1.pdf','sources/steiner.txt']:
 src=B/'sol-fresh-source-discovery-r42'/name;h=sha(src);assert h==expected[name],name
 dst=R/'frozen'/('source-'+Path(name).name);shutil.copyfile(src,dst)
 entries.append({'origin':str(src),'sha256':h,'copy':str(dst.relative_to(R))})
review=B/'sol-steiner-reflection-preliminary-review-r1'
ev=json.loads((review/'evidence-manifest.json').read_text())
for name in ['review.md','ownchecker-results.json','live-http.json','refresh-http.json']:
 src=review/name;h=sha(src);assert h==ev[name]['sha256'];dst=R/'frozen'/('review-'+name);shutil.copyfile(src,dst)
 entries.append({'origin':str(src),'sha256':h,'copy':str(dst.relative_to(R))})
for src in [B/'root-steiner-reflection-investment-r1/ADOPTION.json',base/'lake-manifest.json']:
 dst=R/'frozen'/src.name;h=sha(src);shutil.copyfile(src,dst);assert sha(dst)==h
 entries.append({'origin':str(src),'sha256':h,'copy':str(dst.relative_to(R))})
(R/'provenance.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_url':'https://arxiv.org/pdf/2505.10501v1','pdf_sha256':sha(R/'frozen/source-steiner-v1.pdf'),'source_dates':{'arxiv_v1':'2025-05-15','internal_pdf':'2025-06-13'},'copies_checked_before_and_after':entries,'external_access_this_lane':False,'source_scope':'arXivv1 only; no target journal version located by inherited review; no new literature claim','status':'IMPLEMENTATION; credit0; root acceptance gates unchanged'},indent=2)+'\n')
print('Pins and evidence verified:',len(pins),len(entries))
