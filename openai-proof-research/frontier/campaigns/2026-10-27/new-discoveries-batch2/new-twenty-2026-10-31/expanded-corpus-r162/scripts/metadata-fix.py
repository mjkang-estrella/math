import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1]
p=D/'outputs/finite-more.json';o=json.loads(p.read_text())
for r in o['342666']:
 old=r['exhausted'];r['completed_without_cutoff']=old;r['exhausted']=old and not r['found']
p.write_text(json.dumps(o,indent=2))
print('Clarified search flags: successful witness searches completed without cutoff, not exhaustive order enumeration.')
