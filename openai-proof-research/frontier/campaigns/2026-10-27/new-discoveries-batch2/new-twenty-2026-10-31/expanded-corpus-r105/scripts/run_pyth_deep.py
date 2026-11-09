import ctypes,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];ctypes.CDLL('libm.so.6',mode=ctypes.RTLD_GLOBAL);lib=ctypes.CDLL(str(D/'scripts/pyth_deep.so'));old=json.load(open(D/'outputs/pythagorean.json'));left=[];found=[]
for g,h in old['unresolved']:
 if lib.witness(g,h):found.append([g,h])
 else:left.append([g,h])
 (D/'outputs/pythagorean-deep.json').write_text(json.dumps(dict(checked=len(found)+len(left),new_two_step=found,unresolved=left,bounds='Euclidean primitive direction parameters 2<=m<=100,1<=n<m; swapped/signed; scale -500..500 excluding zero. Integer squared-length equality checked after floating sqrt proposal.'),indent=2))
print('new witnesses',len(found),'unresolved',len(left))
