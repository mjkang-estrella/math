import json,hashlib,sys,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
if len(sys.argv)>1 and sys.argv[1]=='verify':
 j=json.loads((L/'finalmanifest.json').read_bytes())
 for p,h in j['files'].items():assert sha(L/p)==h,p
 print('PASS manifest',len(j['files']));sys.exit()
h=json.loads((L/'history-receipt.json').read_bytes());print('history counts',h['paths'],h['unique_bodies'],len(h['new_or_changed_paths']))
reports=[p for v in h['aliases'].values() for p in v if any(f'sol-fresh-source-discovery-r{i}/' in p for i in [111,112,113])]
print('retained original scientific reports',reports)
source={str(p.relative_to(L)):dict(bytes=p.stat().st_size,sha256=sha(p)) for p in sorted((L/'sources').iterdir()) if p.is_file()}
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
prov=dict(lane=str(L),created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='NO NOMINEE; substantive full scope resolution absent',credit=0,questions=['Tuganbaev2204.12127v2 Q1.1.11 tensor closure: routine excluded','Tuganbaev conference formal series closure: unresolved','Calugareanu-Pop2021 Conj1.1 / Calugareanu2022 Conj3.1: unresolved'],http=[json.loads(l) for l in (L/'http.jsonl').read_text().splitlines()],source_files=source,helper_guard=dict(path=str(guard),sha256=sha(guard),AS_MiB=512,group_RSS_MiB=512,CPU_seconds=210,wall_seconds=230,sampling_nominal_ms=40,BLAS_threads=1),history=dict(paths=h['paths'],bodies=h['unique_bodies'],changed=len(h['new_or_changed_paths']),original_r111_r113=reports,limits=h['limits']),external_actions=False,novelty_clearance=False,root_acceptance_only=True)
(L/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
omit={'finalmanifest.json','scientific-freeze.json'}
allfiles={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in omit}
science={p:h for p,h in allfiles.items() if p not in {'progress.md','context-receipts.json'}}
(L/'scientific-freeze.json').write_text(json.dumps(dict(files=science,exclusion='progress and mutable context receipt; NEXT itself not copied or frozen'),indent=2)+'\n')
allfiles['scientific-freeze.json']=sha(L/'scientific-freeze.json')
(L/'finalmanifest.json').write_text(json.dumps(dict(files=allfiles,self_excluded=True),indent=2)+'\n')
print('manifest',len(allfiles),'science',len(science))
