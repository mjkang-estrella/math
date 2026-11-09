import pathlib,json,copy,importlib.util
P=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('independent_verify',P/'verify.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
m=json.loads((P/'manifest.json').read_text());results=[]
for kind in ['hash','size','extra']:
 t=copy.deepcopy(m)
 if kind=='hash':t['files'][0]['sha256']='0'*64
 if kind=='size':t['files'][0]['size']+=1
 if kind=='extra':t['files']=t['files'][1:] # actual first file becomes an unlisted extra
 try:v.exact(P,t)
 except AssertionError as ex:results.append({'test':kind,'rejected':True,'error':str(ex)})
 else:raise RuntimeError('negative accepted '+kind)
print(json.dumps(results,indent=2))
