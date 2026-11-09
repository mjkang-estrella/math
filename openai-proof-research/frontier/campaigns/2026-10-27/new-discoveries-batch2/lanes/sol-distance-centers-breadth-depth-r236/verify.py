from research import *
errors=[];m=json.loads((L/'manifest.json').read_text());inventory=m['files']
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
if actual!=set(inventory):errors.append('manifest inventory mismatch')
for n,r in inventory.items():
 p=L/n
 if not p.exists() or sha(p)!=r['sha256'] or p.stat().st_size!=r['bytes']:errors.append('manifest '+n)
count=0
for line in (L/'bindings.jsonl').read_text().splitlines():
 r=json.loads(line);count+=1
 for k in ['original','copy']:
  if not pathlib.Path(r[k]).is_file() or sha(r[k])!=r['sha256']:errors.append('binding '+k+' '+r[k])
for script in ['checks.py','intervals.py']:
 r=subprocess.run([os.sys.executable,str(L/script)],capture_output=True,text=True)
 if r.returncode:errors.append(script+': '+r.stderr)
 # Results are deterministic; independently recheck recorded outputs after replay.
for n in ['checks-result.json','interval-check.json']:
 if sha(L/n)!=inventory[n]['sha256']:errors.append('nondeterministic '+n)
save('verification-receipt.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pass':not errors,'errors':errors,'verified_files':len(inventory),'scientific_binding_records':count,'manifest_sha256':sha(L/'manifest.json'),'checks':'exact rational finite diagnostics and continuous interval arrangements replayed','main_proof_status':'unresolved; TMNA4.10 unread; no novelty clearance','counts':[9,39,40]})
print((L/'verification-receipt.json').read_text())
raise SystemExit(bool(errors))
