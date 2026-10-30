from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def rec(p):
 b=p.read_bytes();return {'path':str(p.relative_to(L)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
g=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')
http=[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()]
save('provenance.json',{'sealed_at_utc':now,'local_date':'2026-10-29','claim':'Kametaka1985 normalized F_n irreducibility all n>=3','status':'unresolved / zero credit','guard':{'path':str(g),'sha256':hashlib.sha256(g.read_bytes()).hexdigest(),'unchanged':True,'AS_bytes':536870912,'group_RSS_bytes':536870912,'CPU_s':210,'wall_s':230,'nominal_sample_ms':40,'limits':'sampled RSS; initial unguarded inventory deviation in progress.md'},'http':http,'early_events':'failures.json','chronology':'Kametaka published1985; Kaneko–Ochiai2003; Roffelsen2010,2012; local investigation2026-10-30UTC. No pre-existing complete proof located, no absolute novelty certified.','source_byte_inventory':[rec(p) for p in sorted((L/'sources').glob('*')) if p.is_file()],'history':'history-receipt.json and alias-final.json; qualified r157/r159/r162/r164 reuse; no matching original','registry':'registry-screen.json; both historical300-path caps and current1000-entry limit remain','math':'checks.json/newton.json; finite exact controls only','public_actions':False,'credit':0})
exclude={'provenance.json','scientific-freeze.json','finalmanifest.json','manifest-verification.json'}
science=[rec(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in exclude]
save('scientific-freeze.json',{'utc':now,'scope':'all local science, source and reproducibility bytes; no complete proof','files':science})
files=[rec(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in {'finalmanifest.json','manifest-verification.json'}]
save('finalmanifest.json',{'utc':now,'files':files})
for j in [science,files]:
 for r in j:
  b=(L/r['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==r['sha256'] and len(b)==r['bytes']
save('manifest-verification.json',{'utc':now,'verified':True,'scientific_paths':len(science),'manifest_paths':len(files),'self_reference_policy':'manifest-verification and finalmanifest excluded from manifest; provenance/freeze covered; no circular hash claim'})
print('verified science',len(science),'manifest',len(files))
