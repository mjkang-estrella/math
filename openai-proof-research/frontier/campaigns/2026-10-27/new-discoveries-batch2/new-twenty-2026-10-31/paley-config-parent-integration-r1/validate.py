from run import *
checks=[]
for name,args in [('fresh-build-Yip',[str(B/'lean'),'-j1','-DwarningAsError=true','-o','Yip355956.olean','Yip355956.lean']),('full-types-Yip',[str(B/'lean'),'-j1','-DwarningAsError=true','TypeAudit.lean']),('kernel-Yip',[str(B/'leanchecker'),'Yip355956'])]:
 result=run(name,args);checks.append(result);assert result['returncode']==0
(D/'root-validation.json').write_text(json.dumps(checks,indent=2))
