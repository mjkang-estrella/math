from pathlib import Path
L=Path(__file__).parent
s=(L/'acquire.py').read_text();a=s.index('jobs=');z=s.index('\nrows=',a);s=s[:a]+"jobs=[('toric-arxiv-successor','https://arxiv.org/pdf/1409.3109v1'),('bj-successor','https://arxiv.org/pdf/1705.05985v1')]"+s[z:];s=s.replace('rows=[]',"rows=json.loads((L/'sources.json').read_text())");exec(compile(s,str(L/'acquire.py'),'exec'))
