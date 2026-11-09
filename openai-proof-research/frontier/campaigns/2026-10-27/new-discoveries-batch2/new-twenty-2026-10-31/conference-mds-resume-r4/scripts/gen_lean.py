# Emit the Lean endpoint from certificate data. Usage: python3 -I gen_lean.py <lean_cert.json> <out.lean>
import json, sys
c=json.load(open(sys.argv[1])); W=c['W']
def rows(M): return ',\n'.join('    ['+', '.join(str(x) for x in r)+']' for r in M)
src=open(sys.argv[0].replace('gen_lean.py','Template.lean')).read()
for key,val in {'@WROWS@':rows(W),'@WORD@':', '.join(map(str,c['word'])),'@COEFF@':', '.join(map(str,c['coeff'])),
                '@BROWS@':rows(c['B']),'@DROWS@':rows(c['D'])}.items():
    src=src.replace(key,val)
assert '@' not in src.replace('@[','')
open(sys.argv[2],'w').write(src)
