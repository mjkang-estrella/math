from pathlib import Path
import shutil,json,hashlib,importlib.util,stat
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r204')
s=importlib.util.spec_from_file_location('r204_verifier',R/'verify_packet.py');v=importlib.util.module_from_spec(s);s.loader.exec_module(v)
B=R/'copied-controls';assert not B.exists();B.mkdir()
# Tiny fresh toy selection, copied from our own original prose; no inherited manifest.
base=B/'baseline';p=base/'packet';p.mkdir(parents=True)
(p/'FINAL.md').write_bytes((R/'FINAL.md').read_bytes()[:256]);(p/'FINAL.md').chmod(0o444);p.chmod(0o755)
m={'format':'r204-exact-selection-v1','manifest_mode':'0444','directories':{'.':'0755'},'files':[{'path':'FINAL.md','bytes':256,'mode':'0444','sha256':v.digest(p/'FINAL.md')}]}
(p/'MANIFEST.json').write_text(json.dumps(m,sort_keys=True,indent=2)+'\n');(p/'MANIFEST.json').chmod(0o444)
(base/'REPORT.md').write_text('Tiny copied artifact control only; no mathematical validation.\n');(base/'REPORT.md').chmod(0o444)
a={k:v.digest(p/f) for k,f in [('final_sha256','FINAL.md'),('manifest_sha256','MANIFEST.json')]};a['report_sha256']=v.digest(base/'REPORT.md')
results=[]
for name in ['intact','altered-payload','altered-mode','extra-file','altered-report']:
 c=B/name;shutil.copytree(base,c);q=c/'packet';f=q/'FINAL.md'
 if name=='altered-payload':
  b=f.read_bytes();f.chmod(0o644);f.write_bytes(bytes([b[0]^1])+b[1:]);f.chmod(0o444)
 if name=='altered-mode':f.chmod(0o644)
 if name=='extra-file':(q/'unlisted.txt').write_text('extra\n')
 if name=='altered-report':
  f=c/'REPORT.md';f.chmod(0o644);f.write_text('altered\n');f.chmod(0o444)
 try:
  result=v.verify(q,c/'REPORT.md',**a);ok=True;detail=result
 except AssertionError as e:ok=False;detail=str(e)
 assert ok==(name=='intact'),(name,ok,detail)
 results.append({'case':name,'accepted':ok,'detail':detail})
assert v.digest(p/'FINAL.md')==a['final_sha256']
assert v.digest(R/'FINAL.md')!=a['final_sha256'] # toy is deliberately truncated, never represented as full FINAL
out={'purpose':'five tiny copied artifact controls, not mathematical gates','full_packet_untouched':True,'fresh_toy_selection':True,'results':results}
(R/'private/artifact-controls.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
