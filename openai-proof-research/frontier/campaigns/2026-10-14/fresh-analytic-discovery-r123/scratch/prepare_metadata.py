from pathlib import Path
import json,hashlib,re,shutil
root=Path(__file__).resolve().parents[1]; packet=root/'packet'; project=root.parents[3]
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
rows=json.loads((packet/'source-register.json').read_text()); removed=[]; kept=[]
extents={0:'Entire ensemble section read; prop:potential-identification and Pauli/weighted-gap comparison. No truth audit.',1:'Entire main argument read in overlapping spans; compactness middle in first combined display partly truncated, reread 1–205 before final seal; 205–end global propagation/form/Agmon/trace read. Exact labels in public note.',2:'Entire functional-consequence section read.',6:'Lines1–250 and1121–1315, including main theorem, MASA corollary, factor/core and general-center ending; bibliography1310–1405/navigation. Central product/energy proofs584–1120 NOT completely read.',7:'Entire completion section read: cor:classification, thm:main completion, cor:weak-l4.',8:'Entire introduction read.',9:'Lines1–180 read: clipping, local boundedness, SBV support and Dirichlet replacement; remainder not fully read.',11:'Lines25–90 and810–1010 read: density contract and horizontal derivative/tail interface; other channel helpers not fully read.',12:'Lines1–235,430–680 read, with first150 repeated. Angle existence, every-minimum convergence, explicit nonassertion of symmetry and full weighted-gap proof. Initial portions of strip proof and quantitative-gap continuation not fully read.',13:'Lines1–210 read, local puncture/full-plane reduction setup; remaining mass-displacement proof not fully read.',16:'Entire Gaussian-energy-transfer section read, prop:density-lp and lem:gaussian-duality.',17:'Entire shifted-mixtures section read, endpoint atoms/shifted Bernstein/Fatou interface.'}
for r in rows:
 n=int(Path(r['local']).name[:2]); p=packet/r['local']
 assert sha(p.read_bytes())==r['sha256']
 if n not in extents:
  r['extent']='Acquired and authenticated; no substantive operative reading used. Removed before seal.'; r['retained']=False; p.unlink();removed.append(r)
 else:
  r['extent']=extents[n];r['labels_present']=re.findall(r'\\label\{([^}]+)\}',p.read_text());kept.append(r)
dump(packet/'public/source-register.json',kept);dump(packet/'public/acquisition-removed.json',removed);(packet/'source-register.json').unlink()
prim=json.loads((packet/'primary-register.json').read_text());out=[]
for r in prim:
 if 'error' in r:
  out.append({'name':r['name'],'url':r['url'],'success':False,'failure':r['error'],'extent':'No body read at failed URL; author-hosted version acquired separately.'});continue
 name=r.get('name','benguria-brezis-lieb1981');p=r.get('pdf',r.get('local')).removeprefix('packet/');t=r['text'].removeprefix('packet/')
 extent={'marrakchi2308v3':'Extracted150–290 (TheoremD);3725–3898 (Theorem10.17 proof, final type cases/countable Lemmas10.21/10.22); opening metadata. Not full paper or every local-quantization helper.','delellis-focardi2025':'Extracted8030–8260: Lemma6.3.1/Proposition6.3.2/Theorem6.1.6 proof interfaces; navigation. Crack-tip first-variation normalization not freshly read.','Last-Simon author-hosted April12-2005':'Extracted700–854, with798–854 repeated: Theorem4.2 and full Proposition4.4 proof. Some OCR formulas damaged; only stated form/compactness operations used. Not whole paper.','benguria-brezis-lieb1981':'Lemma4 entire proof, pp170–171, text145–220; p170 visually inspected after OCR concerns. Introduction via primary web navigation; not whole paper.'}[name]
 out.append({'name':name,'url':r['url'],'success':True,'pdf':p,'pdf_sha256':sha((packet/p).read_bytes()),'pdf_bytes':(packet/p).stat().st_size,'text':t,'text_sha256':sha((packet/t).read_bytes()),'text_bytes':(packet/t).stat().st_size,'version':r.get('version',name),'extent':extent,'extraction':'pdftotext -layout; exit0; OCR not typographic certification'})
dump(packet/'public/primary-register.json',out);(packet/'primary-register.json').unlink()
render=packet/'private/primary/bbl-lemma4.png';dump(packet/'public/render-register.json',[{'local':str(render.relative_to(packet)),'sha256':sha(render.read_bytes()),'source':'private/primary/benguria-brezis-lieb1981.pdf','page_1_based':4,'command':'pdftoppm -f 4 -l 5 -scale-to 1500 -png -singlefile; warning: only first requested page written','extent':'Complete page170 visually read, including Lemma4 Cauchy–Schwarz display. Page171 last inequality read from extracted text.'}])
context=[]
for p in sorted((packet/'private/context').iterdir()):
 context.append({'local':str(p.relative_to(packet)),'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size})
dump(packet/'public/context-register.json',context)
# Modest operative historical excerpts only; copied entire-file bytes do not imply entire-file reading.
hspec=[('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r29/screen-278.md',None,'Entire operative body read; before final disposition.'),('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r84/form-domain.md',None,'Entire operative body read.'),('frontier/campaigns/2026-10-14/fresh-structural-discovery-r96/proof.md',None,'Entire64-line body read.'),('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r120/packet/public/geometric-screens.md',None,'Entire body read late AFTER initial crack-tip/stationary feasibility, before any freeze.'),('frontier/iterations/i137-crystalline-coherence.md',(1,150),'Opening1–150 actually read; later combined output truncated. Copied only this extent.'),('frontier/iterations/i122-variational-free-boundary-discovery.md',None,'Section3 operative free-boundary screens read; earlier/later broad display partial. Full modest body copied for context, not full read claim.'),('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r118/packet/public/conditioning.md',None,'Entire conditioning body read; primary not freshly acquired in r123.')]
history=[]
for i,(s,span,extent) in enumerate(hspec):
 p=project/s; data=p.read_bytes();dest=packet/'private/history'/f'{i:02d}-{p.name}'
 copied=data if span is None else b''.join(data.splitlines(keepends=True)[span[0]-1:span[1]])
 dest.write_bytes(copied);history.append({'origin':s,'origin_sha256':sha(data),'origin_bytes':len(data),'local':str(dest.relative_to(packet)),'sha256':sha(copied),'bytes':len(copied),'copied_lines':span,'extent':extent})
dump(packet/'public/history-register.json',history)
# Retain no huge copied source/JSON search bodies: preserve exact query receipts, raw-output hashes and all location hits.
searchdir=packet/'private/search';searchdir.mkdir(exist_ok=True);search=[]
for p in sorted((root/'scratch').glob('*search.json')):
 dest=searchdir/p.name;shutil.copy2(p,dest);search.append({'local':str(dest.relative_to(packet)),'sha256':sha(dest.read_bytes()),'kind':'exact command/result receipt'})
for name in ['history-hits.txt','operation-search.txt','lattice-hits.txt','final-operative-search.txt','final-operative-authored.txt']:
 p=root/'scratch'/name;data=p.read_bytes();text=data.decode(errors='replace');locs=[]
 for line in text.splitlines():
  m=re.match(r'(.+?):(\d+):',line)
  if m:locs.append({'path':m.group(1),'line':int(m.group(2))})
  else:locs.append({'path_or_diagnostic':line[:1200]})
 dest=searchdir/(name+'.locations.json');dump(dest,{'raw_sha256':sha(data),'raw_bytes':len(data),'raw_lines':len(text.splitlines()),'raw_removed_before_seal':True,'meaning':'Navigation inventory only; no semantic reading or priority clearance. Full source/context/JSON matching lines intentionally not recopied.','locations':locs})
 search.append({'local':str(dest.relative_to(packet)),'sha256':sha(dest.read_bytes()),'kind':'all matched locations plus original output hash; raw oversized output removed'})
 p.unlink()
dump(packet/'public/search-register.json',search)
print(json.dumps({'sources_retained':len(kept),'sources_removed':len(removed),'primary_successes':sum(x['success'] for x in out),'history_copies':len(history),'project':str(project)}))
