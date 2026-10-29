from pathlib import Path
import re,json
L=Path(__file__).resolve().parent;P=L/'packet'
p=P/'paper.tex';s=p.read_text().replace('\nsloppy\n','\n\\sloppy\n').replace('S. Marcille','C. Marcille');s=s.replace('from all fourteen\nmathematical module origins','all 167 declarations from fourteen\nmathematical module origins');p.write_text(s)
log=(P/'logs/OriginAudit.log').read_text();rows=re.findall(r'^AUDIT (\S+) (\S+)\nTYPE (.*?)\nAXIOMS \[([^\]]*)\]\nFLAGS unsafe=(\w+) partial=(\w+) axiom=(\w+)$',log,re.M|re.S)
assert len(rows)==167
(P/'audit-inventory.json').write_text(json.dumps([{'origin':r[0],'name':r[1],'actual_type':r[2],'axioms':re.findall(r'[\w.]+',r[3]),'unsafe':r[4],'partial':r[5],'axiom':r[6]} for r in rows],indent=2)+'\n')
a='import Result\nset_option autoImplicit false\nset_option warningAsError true\nset_option linter.auxLemma false\n'
for r in rows:a+='#check '+r[1]+'\n#print axioms '+r[1]+'\n'
(P/'formal/AuditPrint.lean').write_text(a)
r=(P/'replay.py').read_text().replace("MODULES+['OriginAudit']","MODULES+['OriginAudit','AuditPrint']")
(P/'replay.py').write_text(r)
print('audit',len(rows))
