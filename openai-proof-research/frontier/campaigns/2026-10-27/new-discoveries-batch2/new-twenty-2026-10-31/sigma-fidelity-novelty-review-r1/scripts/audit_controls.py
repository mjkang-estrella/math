"""Run after rebuild.py; independent reviewer declarations are in fresh/."""
from rebuild import *
run('NegativeControls',[str(BIN/'lean'),'-j1','-DwarningAsError=true','-o','NegativeControls.olean','NegativeControls.lean'])
run('ReviewerSanity-final',[str(BIN/'lean'),'-j1','-DwarningAsError=true','-o','ReviewerSanity.olean','ReviewerSanity.lean'])
for module in ['NegativeControls','ReviewerSanity']:
 run(module+'-checker-tree',[str(BIN/'leanchecker'),module])
run('ReviewerAudit-final',[str(BIN/'lean'),'-j1','-DwarningAsError=true','ReviewerAudit.lean'])
for name in ['Ordered','EdgeOnly','Balanced']:
 run('Reject'+name,[str(BIN/'lean'),'-j1','-DwarningAsError=true','Reject'+name+'.lean'],expected=1)
