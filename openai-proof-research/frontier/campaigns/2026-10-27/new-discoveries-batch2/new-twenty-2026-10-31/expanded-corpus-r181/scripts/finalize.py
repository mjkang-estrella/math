from pathlib import Path
import json,hashlib,datetime
D=Path(__file__).resolve().parents[1];r=json.loads((D/'results.json').read_text())
r['350069']['mathematical_attempts']+=' Second mechanism: 24 deterministic-seed hill-climb starts for each n=9..14 and k=5,7,9 (432 starts total), half random and half perturbed carousel, at most 30 improving steps per start. Each score uses exact regular/local-transitivity recognition of odd carousels. No score exceeded the source carousel baseline; no uniqueness claim from this local search. logs/hill.log.'
r['350624']['mathematical_attempts']+=' The deeper run completed q=1,2,3 for all 32,767 nonempty hypergraphs on four labelled vertices; q=4 was not completed before wall cap 140.015 seconds (SIGKILL). Last completed counts are in logs/fractional-deeper.log; no full JSON was written. No positive grid gap in any completed level. Not restarted.'
for i,o in r.items():
 a=o['source_url'].rsplit('/',1)[-1]
 o['literature_receipts']=[a+'.abs.html.receipt.json',a+'.pdf.receipt.json']
for i,names in {'349708':['groups-followup'],'350439':['matroid-followup'],'350624':['fractional-published'],'350638':['inversion-followup'],'351193':['metric-followup','metric2025'],'351194':['metric-followup','metric2025']}.items():
 for name in names:r[i]['literature_receipts'].append(name+'.pdf.receipt.json')
(D/'results.json').write_text(json.dumps(r,indent=2,ensure_ascii=False)+'\n')
registry=json.loads((D/'outputs/registry-screen.json').read_text());registry['interpretation']='All Pool keyword hits were inspected in context: unrelated Barr/Barros/barren/coupled physics, Bernstein concentration, Walsh Fourier, Tuza-Valtr, inverse algebra, and fibre terminology. No target-ID/arXiv match or corresponding target statement identified. Omega hits are unrelated paths and were not treated as proof clearance.'
(D/'outputs/registry-screen.json').write_text(json.dumps(registry,indent=2,ensure_ascii=False)+'\n')
assert set(r)=={str(x) for x in json.loads((D/'reservation.json').read_text())['ids']}
assert len(r)==20 and all(o['credit']==0 for o in r.values())
manifest={}
for p in sorted(D.rglob('*')):
 if p.is_file() and p.name!='manifest.json':manifest[str(p.relative_to(D))]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
(D/'outputs/manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('Validated 20 ID-keyed entries;',len(manifest),'files hashed; six prior-result exclusions and fourteen parked. No Lean endpoint.')
