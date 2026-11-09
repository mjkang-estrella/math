from fetch import D,get
import json,gzip
print(get(('networkx-head.json','https://api.github.com/repos/networkx/networkx/commits/HEAD')))
o=json.loads((D/'sources/networkx-head.json').read_text())
print(get(('atlas.dat.gz','https://raw.githubusercontent.com/networkx/networkx/'+o['sha']+'/networkx/generators/atlas.dat.gz')))
b=gzip.decompress((D/'sources/atlas.dat.gz').read_bytes());(D/'sources/atlas.dat').write_bytes(b)
