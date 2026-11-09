import pathlib,json,hashlib,zipfile
D=pathlib.Path(__file__).resolve().parents[1]
paths=['CANDIDATE.md','SUMMARY.md','results.json','lean/README.md','lean/PlaneData.lean','raw/333709.jsonl','extracted.json','reservation.json','sources/333709.pdf','sources/333709.txt','sources/abs-333709.html','outputs/percolation-sym-5-5.cnf','outputs/percolation-5-5.lrat','outputs/percolation-5-5-trim.lrat','outputs/lrat-check.json','outputs/percolation-three-round.json','outputs/percolation.json','outputs/percolation-sat.json','outputs/percolation-sat-sym.json','outputs/registry-screen.json','outputs/http.jsonl','outputs/compliance-incident.json','outputs/percolation-prior-search.json','scripts/limited.py','scripts/percolation.py','scripts/percolation_sat.py','scripts/percolation_sym.py','scripts/check_lrat.py','logs/lrat-independent.log','logs/lrat-independent.receipt.json','logs/lean-plane-r2.log','logs/lean-plane-r2.receipt.json','logs/lean-fresh.log','logs/lean-fresh.receipt.json','logs/leanchecker-aux-r2.log','logs/leanchecker-aux-r2.receipt.json']
manifest={'status':'INCOMPLETE Lean packet; no literal kernel refutation endpoint','target':'333709','files':{x:hashlib.sha256((D/x).read_bytes()).hexdigest() for x in paths}}
(D/'outputs/packet-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
with zipfile.ZipFile(D/'Lean-packet.zip','w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for x in paths:z.write(D/x,x)
 z.write(D/'outputs/packet-manifest.json','packet-manifest.json')
print('packet bytes', (D/'Lean-packet.zip').stat().st_size,'sha256',hashlib.sha256((D/'Lean-packet.zip').read_bytes()).hexdigest())
