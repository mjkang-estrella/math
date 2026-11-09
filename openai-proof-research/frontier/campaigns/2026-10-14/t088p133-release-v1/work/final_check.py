from pathlib import Path
import hashlib,json,subprocess,sys
r=Path(__file__).resolve().parents[1]
anchors={'final':'6e0fef720ba9e2bc067ce3fcf334c36eb19c7f738c7750d50873b706a8002652','manifest':'018d81cc1895f6fdaa4c2429403b2811e2f7b2428df60696ca6497e4f5e22d95','report':'d6238a8ce2b7fa19f7ed6482bf5548fd1ab3477a338a433f5956ab698464507c','archive':'0248221680c2c06a7031c98105b837562b5f184bab5c0bbdbde955f1b36ee096'}
paths={'final':'FINAL.json','manifest':'MANIFEST.json','report':'REPORT.md','archive':'release.zip'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,p in paths.items():assert sha(r/p)==anchors[n]
f=json.loads((r/'FINAL.json').read_text());assert sha(r/'public-source/verify.py')==f['verifier_sha256']
args=[]
for n,p in paths.items():args+=['--'+n,str(r/p),'--'+n+'-sha256',anchors[n]]
results=[]
for src in ['public-source','work/clean-extraction']:
 cp=subprocess.run([sys.executable,'-B',str(r/src/'verify.py'),*args,'--root',str(r/src)],text=True,capture_output=True);assert cp.returncode==0,cp.stderr;results.append({'root':src,'exit':cp.returncode,'output':json.loads(cp.stdout)})
# Final externally anchored extraction is separately checked again; full reproduction
# already ran the same exact ZIP/source bytes with the provisional execution envelope.
c=subprocess.run([sys.executable,'-B',str(r/'work/clean-extraction/integrity_controls.py'),'--root',str(r/'work/clean-extraction'),'--output',str(r/'work/final-controls'),*args],text=True,capture_output=True);assert c.returncode==0,c.stderr
assert sha(r/'verification/MANIFEST.json')==f['verification_manifest_sha256']
v=json.loads((r/'verification/MANIFEST.json').read_text())
for n,x in v['files'].items():assert sha(r/'verification'/n)==x['sha256'] and (r/'verification'/n).stat().st_size==x['bytes']
# Check exact executable bootstrap bytes and generated-file assembly bindings.
m=json.loads((r/'MANIFEST.json').read_text());am=json.loads((r/'public-source/assembly-map.json').read_text())
for n,x in am['generated'].items():assert sha(r/'public-source'/n)==x['sha256']==m['files'][n]['sha256']
result={'final_anchors':anchors,'verifications':results,'final_controls':json.loads(c.stdout),'control_stderr':c.stderr,'separate_local_evidence_named_files':len(v['files']),'generated_assembly_bindings_match':True,'archive_reassembly_identical':(r/'release.zip').read_bytes()==(r/'work/assembly-2/release.zip').read_bytes(),'scope':'Postseal receipt outside immutable artifact to avoid circular binding; no gate assigned.'}
(r/'work/final-verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
