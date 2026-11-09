import pathlib,json
import verify
D=pathlib.Path(__file__).resolve().parent
files=verify.payloadfiles();m={'files':[{'path':n,'size':len(b),'sha256':verify.digest(b)} for n,b in files.items()]}
verify.payloadcheck(files,m)
results=[];n='dispositions.json';b=files[n]
for kind,alter in [('hash',{**files,n:bytes([b[0]^1])+b[1:]}),('size',{**files,n:b+b' '}),('extra-file',{**files,'unexpected.tmp':b'x'})]:
 try:verify.payloadcheck(alter,m)
 except ValueError as e:results.append({'test':kind,'rejected':True,'reason':str(e)})
 else:raise AssertionError('accepted '+kind)
(D/'negative-tests.json').write_text(json.dumps({'method':'Same verifier payload function; in-memory mutations of actual lane bytes. No originals or payload files mutated.','control_pass':True,'tests':results},indent=2)+'\n')
print(results)
