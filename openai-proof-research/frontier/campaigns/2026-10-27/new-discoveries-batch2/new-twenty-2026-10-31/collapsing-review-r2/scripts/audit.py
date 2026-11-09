exec((__import__('pathlib').Path(__file__).with_name('more.py')).read_text().split('\nH=')[0])
E['PATH']=B+':/usr/bin:/bin'
for name,cmd in [('leanchecker-correct-path',[B+'/leanchecker','MathDB378395']),('ReviewAudit',[B+'/lean','-j1','-DwarningAsError=true','ReviewAudit.lean']),('ReviewSanity',[B+'/lean','-j1','-DwarningAsError=true','ReviewSanity.lean'])]:
 assert run(name,cmd,F,E)==0

assert run('BadOlean-correct-path',[B+'/leanchecker','Bad'],F,E)!=0
