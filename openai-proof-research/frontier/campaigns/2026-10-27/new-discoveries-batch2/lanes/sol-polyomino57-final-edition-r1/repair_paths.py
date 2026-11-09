from pathlib import Path
import json
L=Path('source');p=L/'PROVENANCE.json';v=json.loads(p.read_text())
for e in v['final_edition_evidence']:
 if '/extracted/logs/' in e['packet_path']:
  a=L/e['packet_path'];e['packet_path']=e['packet_path'].replace('/extracted/logs/','/logs/');b=L/e['packet_path'];b.parent.mkdir(parents=True,exist_ok=True);a.rename(b);a.parent.rmdir();a.parent.parent.rmdir()
p.write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
p=L/'verify_packet.py';p.write_text(p.read_text().replace('/extracted/logs/','/logs/'))
p=L/'FINAL-EDITION-NOTES.md';p.write_text(p.read_text()+"\nInitial packaging failed closed because documentary audit logs were copied under a directory named extracted, which pack.py deliberately rejects. Only their evidence paths were moved to logs, preserving every log byte; the verifier and evidence metadata were updated. The consequent reproduction attempt found no ZIP and failed without testing it. Failed reproduction directory remains outside the packet.\n")
