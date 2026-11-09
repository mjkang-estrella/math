from fetch import get,D
import json
sha=json.load(open(D/'sources/omega-head.json'))['sha']
for x in [('omega-Foata.lean',f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{sha}/D5/S0/Certificates/Combinatorics/UnitIntervalParkingFoata.lean'),('2604.27868.pdf','https://arxiv.org/pdf/2604.27868')]:print(get(x),flush=True)
