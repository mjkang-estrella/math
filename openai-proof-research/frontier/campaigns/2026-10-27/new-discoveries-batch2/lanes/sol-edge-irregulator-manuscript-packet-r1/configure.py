from pathlib import Path
import re
L=Path(__file__).resolve().parent;P=L/'packet'
mods=['Source','Boundary','Gadget','Edges','Degrees','Local','Lower','Charges','Transport','Refutation','UpperWitness','UpperDegrees','Upper','Result']
a=(L/'upper/formal/OriginAudit.lean').read_text();a=a.replace('import Upper','import Result');a=re.sub(r'let mods := #\[.*?\]', 'let mods := #['+', '.join('`'+m for m in mods)+']',a);(P/'formal/OriginAudit.lean').write_text(a)
r=(L/'upper/replay.py').read_text();r=re.sub(r'MODULES=\[.*?\]',repr('MODULES')+'='+repr(mods),r).replace("'MODULES'=",'MODULES=')
r=r.replace("MODULES+['OriginAudit','AuditPrint']","MODULES+['OriginAudit']").replace("'UPPER_WITNESS_REPLAY_PASS'","'IMPLEMENTATION_UNION_REPLAY_PASS'").replace('Unconditional actual deletion witness, all retained neighbors/degrees and minimum upper bound for t>=2; no lower bound or source refutation','Combined closed exact minimum, Fin transport and source negation; implementation replay only, independent final root review pending')
r=r.replace("(dest/'logs').mkdir()","(dest/'logs').mkdir(exist_ok=True)")
(P/'replay.py').write_text(r)
# Separate helper supervisor; Lean is launched in its own session by guard.py.
(P/'replay_guard.py').write_bytes((L/'helper_guard.py').read_bytes())
print('configured 14 mathematical modules')
