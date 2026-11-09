import subprocess,sys,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1]
for i in range(15):
 name=f'row{i}';r=subprocess.run([sys.executable,'-I',str(D/'scripts/limited.py'),name,sys.executable,'-I',str(D/'scripts/leanrun.py'),'-o',f'Row{i}.olean',f'Row{i}.lean'])
 rec=json.loads((D/f'logs/{name}.receipt.json').read_text());print(name,rec['returncode'],flush=True)
 if rec['returncode']!=0:sys.exit(1)
