import json,pathlib,hashlib
D=pathlib.Path(__file__).resolve().parent;p=D/'literal-records.json';b=p.read_bytes();print('DERIVATIVE BIND',hashlib.sha256(b).hexdigest(),len(b))
for x in json.loads(b):
 r=x['record'];print(str(r['mathdb_id'])+' '+r['statement']+' SOURCE '+r['source_name']+' '+r['source_url'])
