import sys,pathlib,time,urllib.parse,json
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from net import get,D
queries=['("meandric" OR "1708.05188" OR "Goulden Nica") lean','("heterochromatic" OR "1708.08562" OR "Montellano") lean','("excessive index" OR "1301.1521" OR "Mazzuoccolo") lean','("exponential domination" OR "1511.01398") lean','("memoryless" OR "1310.6008" OR "Gadouleau") lean','("cross number" OR "1410.6867") lean','("fighting fish" OR "2509.16667") lean','("dual polar" OR "1510.01697") lean']
for n,q in enumerate(queries,1):
 rec=get(f'github-search-{n:02}.json','https://api.github.com/search/repositories?q='+urllib.parse.quote(q))
 if rec.get('status') in (403,429):break
 if n<8:time.sleep(8)
