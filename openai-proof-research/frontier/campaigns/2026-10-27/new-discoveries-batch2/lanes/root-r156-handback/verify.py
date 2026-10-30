from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r156'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
rows=json.loads((S/'finalmanifest.json').read_text())['files']
def verify():
 for r in rows:
  p=S/r['path'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],str(p)
verify();Q=P/'replay';Q.mkdir(exist_ok=True)
for f in ['checks.py','explore.py','control.py']:shutil.copyfile(S/f,Q/f)
logs=[]
for args in [['checks.py'],['explore.py','initial'],['explore.py','corrected'],['control.py']]:
 r=subprocess.run([sys.executable,str(Q/args[0])]+args[1:],capture_output=True,text=True,check=True)
 logs.append(' '.join(args)+'\n'+r.stdout+r.stderr)
(P/'replay.log').write_text('\n'.join(logs))
for f in ['checks.json','explore-initial.json','explore-corrected.json','control.json']:
 a=json.loads((S/f).read_text());b=json.loads((Q/f).read_text());a.pop('utc',None);b.pop('utc',None);assert a==b,f
sys.path.insert(0,str(Q));from checks import cover
assert cover(18,16,(1,2))[0] is None
verify();c=json.loads((Q/'explore-corrected.json').read_text());assert all(r['found'] is not None for r in c['records'])
out={'status':'PASS','manifest_paths_before_and_after':len(rows),'replay_equal_except_utc':True,'corrected_cycles':len(c['records']),'visited_states':c['states'],'controls':json.loads((Q/'control.json').read_text()),'known_exception_18_16_two_head_test':True,'universal_result':False,'credit':0}
(P/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
