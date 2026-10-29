from pathlib import Path
import json,hashlib,subprocess,re,datetime
L=Path(__file__).resolve().parent;R=L.parents[5];B=L.parent.parent
paths=[R/'AGENTS.md',B/'AGENTS.md',B/'NEXT.md',B/'ledger.json',B/'prior-campaign-context.json',L.parent/'root-edge-irregulator-final-freeze-r1/CURRENT-REGISTRIES.json',L.parent/'sol-fresh-source-discovery-r91/SUMMARY.md',L.parent/'sol-fresh-source-discovery-r91/provenance.json',L.parent/'sol-fresh-source-discovery-r88/SUMMARY.md',L.parent/'sol-fresh-source-discovery-r86/SUMMARY.md',L.parent/'sol-fresh-source-discovery-r89/SUMMARY.md',L.parent/'sol-fresh-source-discovery-r90/SUMMARY.md']
out=[]
for p in paths:
 if not p.exists():out.append({'path':str(p),'missing':True});continue
 t=p.read_text();out.append({'path':str(p),'bytes':len(p.read_bytes()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'read_complete':True,'lead':t[:250]})
(L/'context-read.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
# All-date, all-report screening, unrestricted extension and full source inventory.
pattern=r'2410[.]20460|2512[.]21401|plactic.{0,25}centraliz|centraliz.{0,25}plactic|Sagan.{0,8}Wilson|2507[.]01332|inverse.{0,5}Z.polynomial|2601[.]17314|plactic.peak.counterexample'
p=subprocess.run(['rg','-l','-i',pattern,str(R)],capture_output=True,text=True)
hits=[x for x in p.stdout.splitlines() if not x.startswith(str(L)+'/')]
(L/'duplicate-all.txt').write_text('\n'.join(hits)+'\n')
reports=[]
for p in R.rglob('*'):
 if p.is_file() and any(s in p.name.lower() for s in ['findings','discovery','summary','provenance']):reports.append(str(p))
(L/'report-inventory.txt').write_text('\n'.join(sorted(reports))+'\n')
rhits=[p for p in hits if p in reports];(L/'duplicate-reports.txt').write_text('\n'.join(rhits)+'\n')
print('exact report hits',rhits)
# Full contexts are loaded and hashed, no concurrent lane polling.
