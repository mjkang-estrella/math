import pathlib,zipfile,re,hashlib,json
D=pathlib.Path(__file__).resolve().parents[1]
modules=['Definitions','Arithmetic','Certificate']+['EdgeRows'+str(i) for i in range(8)]+['Endpoint']
with zipfile.ZipFile(D/'lean-input.zip','w',zipfile.ZIP_DEFLATED) as z:
 for m in modules:
  b=(D/f'lean/{m}.lean').read_bytes()
  assert not re.search(rb'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',b)
  z.writestr(m+'.lean',b)
R=D/'replay';R.mkdir()
with zipfile.ZipFile(D/'lean-input.zip') as z:
 assert set(z.namelist())=={m+'.lean' for m in modules}
 for name in z.namelist():
  assert '/' not in name and '\\' not in name
  b=z.read(name);assert not re.search(rb'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',b)
  (R/name).write_bytes(b)
print('fresh empty extraction; forbidden-token scan passed; archive SHA256',hashlib.sha256((D/'lean-input.zip').read_bytes()).hexdigest())
