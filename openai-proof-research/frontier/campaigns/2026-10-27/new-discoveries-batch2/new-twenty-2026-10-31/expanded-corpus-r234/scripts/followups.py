import pathlib,json,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1];root=json.loads((D/'sources/openai-root.body').read_text());head=json.loads((D/'sources/openai-head.body').read_text())['sha'];print('openai commit',head)
args=[]
for x in root['tree']:
 if x['path']=='preprints':args.extend(['openai-preprints','https://api.github.com/repos/openai/math/git/trees/'+x['sha']+'?recursive=1'])
args.extend(['uc-2019','https://arxiv.org/pdf/1707.06110','uc-2019-abs','https://arxiv.org/abs/1707.06110','uc-shortened-abs','https://arxiv.org/abs/2204.02910'])
subprocess.run([sys.executable,'-I','-B',str(D/'scripts/fetch.py'),*args],check=True)
subprocess.run(['pdftotext','-layout',str(D/'sources/uc-2019.body'),str(D/'sources/uc-2019.txt')])
