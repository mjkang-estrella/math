import pathlib,runpy,time,urllib.parse
D=pathlib.Path(__file__).resolve().parents[1];f=runpy.run_path(str(D/'scripts/fetch.py'),run_name='fetchmodule')['fetch']
for j,q in enumerate(['"Keszegh" lean','"Meszaros" "percolation" lean','"Patkos" lean','"Vizer" lean','"line percolation" lean','333709 lean']):
 f('https://api.github.com/search/repositories?q='+urllib.parse.quote(q),'github-percolation-333709-%d.json'%j);time.sleep(7)
