from pathlib import Path
import re,json,hashlib,shutil
L=Path(__file__).resolve().parent;P=L/'packet';F=P/'evidence/current-failures'
shutil.copyfile(P/'formal/AuditPrint.lean',F/'AuditPrint-v1.lean.txt');shutil.copyfile(P/'logs/AuditPrint.log',F/'AuditPrint-v1.log');shutil.copyfile(P/'logs/AuditPrint.json',F/'AuditPrint-v1.json')
mods=re.search(r'let mods := (.*)',(P/'formal/OriginAudit.lean').read_text())[1]
a=(L/'upper/formal/AuditPrint.lean').read_text().replace('import Upper','import Result');a=re.sub(r'let mods := .*','let mods := '+mods,a);(P/'formal/AuditPrint.lean').write_text(a)
p=P/'paper.tex';s=p.read_text().replace('enumerates actual declarations all 167 declarations','enumerates all 167 declarations').replace('\\sloppy','\\raggedright');p.write_text(s)
# Build external resource pins are verified before every offline paper build.
files=[Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/t088p133-manuscript-r2/tools/tectonic')]+[p for p in (Path.home()/'.cache/tectonic').rglob('*') if p.is_file()]
(P/'paper-pins.json').write_text(json.dumps({str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},indent=2)+'\n')
print('configured')
