import pathlib,json,hashlib
O=pathlib.Path(__file__).parent;excluded=['manifest.json','final-receipt.json']
j={'excluded':excluded,'files':[{'path':str(p.relative_to(O)),'size':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(O.rglob('*')) if p.is_file() and str(p.relative_to(O)) not in excluded]}
(O/'manifest.json').write_text(json.dumps(j,indent=2)+'\n')
