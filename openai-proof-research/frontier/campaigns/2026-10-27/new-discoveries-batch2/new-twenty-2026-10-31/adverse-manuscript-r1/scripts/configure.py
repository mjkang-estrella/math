from pathlib import Path
R=Path(__file__).resolve().parents[1]
p=R/'scripts/bounded.py';s=p.read_text();s=s.replace('private RSS','total RSS').replace("vals=(proc/'smaps_rollup').read_text().splitlines()\n    rss+=sum(int(s.split()[1])*1024 for s in vals if s.startswith(('Private_Clean:','Private_Dirty:','Private_Hugetlb:')))","vals=(proc/'status').read_text().splitlines()\n    rss+=sum(int(s.split()[1])*1024 for s in vals if s.startswith('VmRSS:'))").replace('peak_sampled_private_rss_bytes','peak_sampled_total_rss_bytes');p.write_text(s)
s=(R/'formal/Audit.lean').read_text().replace('import Main','import Reviewer\nimport Main',1).replace('`Main]','`Main, `Reviewer]');(R/'formal/DossierAudit.lean').write_text(s)
p=R/'replay.py';s=p.read_text().replace("+['Bridges','Quadratic','Main']","+['Bridges','Quadratic','Main','Reviewer']").replace("formal/Audit.olean','formal/Audit.lean","formal/DossierAudit.olean','formal/DossierAudit.lean")
s=s.replace('receipts=[]', '''# Hash identity and forbidden-token checks precede any compilation.
import re
binding=json.loads((root/'MODULE-HASHES.json').read_text())
for name,digest in binding.items():
 assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest, name
for m in mods:
 assert not re.search(r'\\b(sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool|implemented_by|extern)\\b',(root/'formal'/f'{m}.lean').read_text()),m
receipts=[]
receipts.append(run('lean.sh','toolchain',['--version']))
v=(root/'logs/toolchain.log').read_text()
assert '4.34.1' in v and '5045d0056413266e57c625dcd7c365b10e377c52' in v
''')
s=s.replace('assert count and count>100','assert count == 167, count')
s=s.replace("receipts.append(run('lean.sh','full-audit'", "receipts.append(run('lean.sh','full-audit'")
s=s.replace('# The audit output',"receipts.append(run('checker.sh','checker-DossierAudit',['DossierAudit']))\n# The audit output")
p.write_text(s)
import json,hashlib
(R/'MODULE-HASHES.json').write_text(json.dumps({'formal/'+p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (R/'formal').glob('*.lean')},indent=2)+'\n')
