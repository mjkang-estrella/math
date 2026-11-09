from run_audit import *
for n in ['Defs','BoolProbe','Checker','Endpoint']:
 if run('kernel-fixed-'+n,[str(BIN/'leanchecker'),n])['exit']:break
else:
 run('review-inventory-final',[str(BIN/'lean'),'-j1','-DwarningAsError=true','ReviewAudit.lean'])
 (F/'FalseProof.lean').write_text('import Endpoint\nset_option warningAsError true\nexample : False := by exact True.intro\n')
 run('negative-false-proof',[str(BIN/'lean'),'-j1','-DwarningAsError=true','FalseProof.lean'])
 (F/'BadCertificate.olean').write_bytes(b'Deliberately invalid Lean certificate\n')
 run('negative-bad-certificate',[str(BIN/'leanchecker'),'BadCertificate'])
 (F/'WrongEndpoint.lean').write_text('import Endpoint\nset_option warningAsError true\nexample : Palette.SourceClaim := Palette.source_refutation\n')
 run('negative-wrong-endpoint',[str(BIN/'lean'),'-j1','-DwarningAsError=true','WrongEndpoint.lean'])
