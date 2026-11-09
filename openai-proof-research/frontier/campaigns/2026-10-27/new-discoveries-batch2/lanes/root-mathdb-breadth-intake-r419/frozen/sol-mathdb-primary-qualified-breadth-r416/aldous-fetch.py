import pathlib,runpy,sys,json
L=pathlib.Path(__file__).parent
for n in ['fields','congestion','graph_compression','random_proximity','stretch','cities','sirsn','partition','online_zeta3','compact','hammersley_flow']:
 sys.argv=['fetch.py',n,'https://www.stat.berkeley.edu/~aldous/Research/OP/'+n+'.html'];runpy.run_path(str(L/'fetch.py'),run_name='__main__')
 m=json.loads((L/'evidence'/(n+'.provenance.json')).read_text())
 if '403' in m.get('error','') or '429' in m.get('error',''):break
