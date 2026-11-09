from pathlib import Path
import json
P=Path(__file__).resolve().parent
s=(P/'formal/PacketAudit.lean').read_text()
mods=json.loads((P/'inputs/integrated-core-hashes.json').read_text())['mathematical_modules']
for n in mods:
 t=s[s.index('set_option'):]
 a=t.index('  let mods := #[');b=t.index('\n  let allowed',a)
 t=t[:a]+f'  let mods := #[`{n}]'+t[b:]
 (P/'formal'/f'PacketAudit_{n}.lean').write_text(f'import {n}\nimport Lean\n'+t)
(P/'formal/PacketAudit.lean').unlink()
v=(P/'verify.py').read_text().replace("files['PacketAudit']=P/'formal/PacketAudit.lean'","audits=sorted((P/'formal').glob('PacketAudit_*.lean'))\n for p in audits:files[p.stem]=p")
v=v.replace("audit=(out/'logs/PacketAudit.log').read_text();", "audit='\\n'.join((out/'logs'/(p.stem+'.log')).read_text() for p in audits);")
v=v.replace("if n!='PacketAudit'","if not n.startswith('PacketAudit_')")
v=v.replace("'audit_total':audit.split('AUDIT_TOTAL ')[-1].strip()", "'audit_total':sum(int(line.split('AUDIT_TOTAL ')[1]) for line in audit.splitlines() if 'AUDIT_TOTAL ' in line)")
(P/'verify.py').write_text(v)
s=(P/'main.tex').read_text().replace(' A=(C_4-C_1C_d+(5/d)H_1H_d)/2,\\qquad\n B=H_1(C_5-C_d)/2,\\quad U=(DB)A-B(DA)-A^2,\\quad V=-4BA.', '\\begin{gathered}\n A=(C_4-C_1C_d+(5/d)H_1H_d)/2,\\quad B=H_1(C_5-C_d)/2,\\\\\n U=(DB)A-B(DA)-A^2,\\qquad V=-4BA.\n\\end{gathered}')
(P/'main.tex').write_text(s)
