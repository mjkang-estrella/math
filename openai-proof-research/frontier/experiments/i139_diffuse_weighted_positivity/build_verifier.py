"""Preparation-only construction of the standalone verifier; never run inherited code."""
from pathlib import Path
R=Path(__file__).resolve().parents[3];E=R/'frontier/experiments/i139_diffuse_weighted_positivity'
old=(R/'frontier/experiments/i136_birational_positivity_discovery/verify.py').read_text()
p=old.replace('I136','I139').replace('i136_birational_positivity_discovery','i139_diffuse_weighted_positivity').replace('i136-birational-positivity-discovery.md','i139-diffuse-weighted-positivity.md')
p=p.replace("def context_check(freeze):\n stream=read(S+", "def context_check(freeze):\n OLD='frontier/sources/i136_birational_positivity_discovery'\n stream=read(OLD+")
p=p.replace("cov=data(S+'/context-coverage.json')", "cov=data(OLD+'/context-coverage.json')")
p=p.replace("(134|135)","(137|138)")
start=p.index(" mandatory='frontier/iterations/iteration133")
end=p.index(" domain=data(",start)
p=p[:start]+''' mandatory='frontier/iterations/iteration136-birational-positivity-discovery-task.json'
 assert sha(read(mandatory))=='fb761d762d453a405d6ce3a740f5c6ceea3c7863c372648aeed781d82ea306cd'
 OLD='frontier/sources/i136_birational_positivity_discovery'
 pieces,coverage=context_check(data(OLD+'/input-freeze.json'))
 def decoded(obj,key='task'):
  out=[]
  if isinstance(obj,dict):
   for k,v in obj.items():out.extend(decoded(v,key+'/'+str(k)))
  elif isinstance(obj,list):
   for i,v in enumerate(obj):out.extend(decoded(v,key+'/'+str(i)))
  else:out.append('FIELD '+key+'\\n'+(obj if isinstance(obj,str) else json.dumps(obj,ensure_ascii=False)))
  return out
 expected='\\n\\n'.join(decoded(data(mandatory)))+'\\n'
 assert read(S+'/direct-context.txt').decode()==expected
 assert data(S+'/original-audit-checkpoint.json')['required_i136_sha256']==sha(read(mandatory))
 assert data(S+'/reading-notes.json')['mandatory_context_completed_before_audit'] is True
''' +p[end:]
p=p.replace("for x in data(S+'/selected-source-bindings.json'):","for x in data(OLD+'/selected-source-bindings.json'):")
p=p.replace("p['convention']=='splitlines'","p['convention'].startswith('splitlines')")
p=p.replace("  if 'passage' in p:assert part==p['passage']","  if 'passage' in p:assert part==p['passage']\n  if 'ending' in p:assert ls[p['end']-1]==p['ending']")
p=p.replace("overlap=data(S+'/overlap-search.json')","overlap=data(OLD+'/overlap-search.json')")
start=p.index(" for rec in data(S+'/primary/retrievals.json'):")
end=p.index(" # This is the only executable",start)
p=p[:start]+''' for rec in data(S+'/primary/retrievals.json'):
  if 'failure' not in rec:
   h=read(S+'/primary/'+rec['name']+'.html');t=read(S+'/primary/'+rec['name']+'.txt')
   assert sha(h)==rec['sha256'];assert extract(h)==t;assert len(t.decode().splitlines())==rec['lines']
 for name,v in [('ito',2),('roe',1),('dumnicki',1),('evans',3)]:
  versions=[int(x) for x in re.findall(r'<strong>\\[v(\\d+)\\]</strong>',read(S+'/primary/'+name+'-abs.html').decode())]
  assert versions and max(versions)==v,(name,versions)
 assert sys.dont_write_bytecode
''' +p[end:]
# Read-only policy also blocks cwd changes and further common filesystem mutations.
p=p.replace("'os.fork'}", "'os.fork','os.chdir','os.fchdir','os.replace','os.unlink','os.rmdir','os.chown','os.lchown','os.fchmod','os.fchown','os.ftruncate','os.setxattr','os.removexattr'}")
(E/'verify.py').write_text(p)
for name in ['validate.py','seal_once.py']:
 q=(R/'frontier/experiments/i136_birational_positivity_discovery'/name).read_text().replace('I136','I139').replace('i136_birational_positivity_discovery','i139_diffuse_weighted_positivity').replace('i136-birational-positivity-discovery.md','i139-diffuse-weighted-positivity.md');(E/name).write_text(q)
