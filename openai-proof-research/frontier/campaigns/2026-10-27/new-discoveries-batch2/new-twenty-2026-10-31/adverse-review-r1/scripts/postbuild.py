from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from run import run,BIN,R
assert run('reviewer',[str(BIN/'lean'),'-j1','-DwarningAsError=true','-o','formal/Reviewer.olean','formal/Reviewer.lean'])==0
assert run('checker-reviewer',[str(BIN/'leanchecker'),'Reviewer'])==0
s=(R/'extracted/formal/Audit.lean').read_text().replace('import Main','import Reviewer',1).replace('`Quadratic, `Main]','`Quadratic, `Main, `Reviewer]')
(R/'extracted/formal/ReviewerAudit.lean').write_text(s)
assert run('all-declarations',[str(BIN/'lean'),'-j1','-DwarningAsError=true','formal/ReviewerAudit.lean'])==0
controls={
 'false-alpha':'import Main\nopen Adverse381433\nexample : alpha latinGraph = 6 := by exact alpha_eq_five\n',
 'false-Q':'import Main\nopen Adverse381433\nexample : QGraph latinGraph := by exact graph_adverse\n',
 'false-completeness':'import Reviewer\nopen Adverse381433\nexample : latinGraph.Adj (0,0) (1,1) := by unfold latinGraph; decide\n',
 'false-deletion':'import Main\nopen Adverse381433\nexample : upsilon (deleteOpen latinGraph (0,0)) = 5 := by exact deletion_upsilon (0,0)\n'}
for n,s in controls.items():
 (R/'extracted/formal/Negative.lean').write_text(s)
 assert run('negative-'+n,[str(BIN/'lean'),'-j1','-DwarningAsError=true','formal/Negative.lean'])==1
 assert 'error:' in (R/'logs'/('negative-'+n+'.log')).read_text()
