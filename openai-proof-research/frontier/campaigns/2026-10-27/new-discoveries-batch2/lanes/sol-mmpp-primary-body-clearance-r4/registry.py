import pathlib,json,subprocess
L=pathlib.Path(__file__).resolve().parent
x=json.loads((L/'sources/omega-delta.json').read_text());args=[]
for i,d in enumerate(x['files']):args += [f'omega-body-{i}.md','https://raw.githubusercontent.com/the-omega-institute/trureturing/28414a3d55d5b97458b138701407d5678e167a8e/'+d['filename']]
subprocess.run(['python',str(L/'fetch.py')]+args,check=True)
x=json.loads((L/'sources/cox-archive-metadata.json').read_text());print('ARCHIVE',json.dumps(x['metadata'],indent=2));print('FILES',[(d['name'],d.get('private')) for d in x['files'] if d['name'].endswith(('.pdf','.txt'))])
