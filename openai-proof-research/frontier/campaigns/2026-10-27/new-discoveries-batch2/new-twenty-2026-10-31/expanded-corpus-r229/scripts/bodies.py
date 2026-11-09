import pathlib,re,json,subprocess
namespace={'__file__':str(pathlib.Path(__file__).resolve().with_name('fetch.py')),'__name__':'fetch'}
exec(compile(pathlib.Path(namespace['__file__']).read_text(),namespace['__file__'],'exec'),namespace)
get=namespace['get']
D=pathlib.Path(__file__).resolve().parents[1]
todo=[]
for p in sorted((D/'sources').glob('*.abs')):
 a=p.stem; s=p.read_text(); vs=sorted(set(re.findall(r'/abs/'+re.escape(a)+r'(v\d+)',s))) or ['v1']
 for v in vs:todo.append(a+v)
todo += ['2303.12222','2509.13877','2603.22262']
for a in todo:
 get(a+'.pdf','https://arxiv.org/pdf/'+a)
 p=D/'sources'/(a+'.pdf')
 if p.exists() and p.read_bytes().startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
(D/'evidence/version-list.json').write_text(json.dumps(todo,indent=2))
