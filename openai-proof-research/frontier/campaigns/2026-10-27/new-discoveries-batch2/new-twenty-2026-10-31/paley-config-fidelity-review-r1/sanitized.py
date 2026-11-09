from run import *
out=[]
for m in ['Yip355956','V3Config355701']:
 out.append(run('sanitized-build-'+m,[str(B/'lean'),'-j1','-DwarningAsError=true','-o',m+'.olean',m+'.lean']))
 out.append(run('sanitized-checker-'+m,[str(B/'leanchecker'),m]))
(D/'sanitized.json').write_text(json.dumps(out,indent=2))
