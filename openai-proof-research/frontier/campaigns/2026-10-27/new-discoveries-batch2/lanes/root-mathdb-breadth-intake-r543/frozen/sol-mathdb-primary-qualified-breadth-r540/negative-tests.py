import pathlib,subprocess,sys,json
P=pathlib.Path(__file__).resolve().parent;out=[]
for kind in ['hash','size','extra']:
 r=subprocess.run([sys.executable,'-B',str(P/'verify.py'),'--negative',kind],capture_output=True,text=True)
 assert r.returncode!=0
 out.append({'mutation':kind,'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr,'originals_mutated':False,'mode':'in-memory altered expected entry or virtual extra filename, actual verifier path'})
(P/'negative-test-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
