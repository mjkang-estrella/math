import runpy,pathlib,re,json
X=runpy.run_path(str(pathlib.Path(__file__).with_name('research.py')));L=X['L'];freeze=X['freeze'];sha=X['sha']
R=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
P=R/'frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-euler-turan-final-review/fresh/trureturing'
terms=re.compile(r'mcnamara|sagan|1208.2683|0707.2340|0808.1065|springer.number|irreducible.polynomial|infinite.{0,5}log.concav|stable.matrices|rayleigh|franel|derangement|bell.number|tangent.number|van.doorn|2411.03073|harmonic.{0,30}(convex|root)|loewner|real.stable.matrix|1309.1679|monopoli|distinct.{0,25}absolute|reduced.system.{0,20}residues',re.I)
files=list((P/'Problems').glob('*.md'))
if __import__('sys').argv[-1]=='proofs':files=list((P/'D5').rglob('*.lean'))
B=R/'frontier/campaigns/2026-10-27/new-discoveries-batch2'
for lane in (B/'lanes').iterdir():
 if lane==L or not lane.is_dir():continue
 for n in ['SUMMARY.md','SCOUTING.md','discovery.md','review.md','STATUS.md']:
  if (lane/n).is_file():files.append(lane/n)
hits=[]
for p in files:
 if p.stat().st_size>1500000:continue
 d=freeze(p);s=d.decode(errors='replace');matches=list(terms.finditer(s))
 if matches:
  hits.append({'path':str(p),'sha256':sha(d),'hits':[s[max(0,m.start()-100):m.end()+160] for m in matches[:12]]})
 assert sha(p.read_bytes())==sha(d)
(L/('semantic-proof-hits.json' if __import__('sys').argv[-1]=='proofs' else 'semantic-hits.json')).write_text(json.dumps(hits,indent=2));print('scanned',len(files),'hits',len(hits))
for h in hits:
 if any(t in h['path'].lower() for t in ['sun','monopoli','giacomelli','borcea']):print(h['path'],h['hits'][:2])
