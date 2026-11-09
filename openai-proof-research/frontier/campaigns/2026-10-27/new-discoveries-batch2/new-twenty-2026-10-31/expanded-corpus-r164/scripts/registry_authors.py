import pathlib,json,urllib.parse,time
D=pathlib.Path(__file__).resolve().parents[1]
exec(compile((D/'scripts/fetch.py').read_text().split("if __name__")[0],str(D/'scripts/fetch.py'),'exec'))
for i,q in [('333364','"Khovanova" lean'),('337410','"Goncalves" "Ramsey" lean'),('332342','"Kitaev" lean'),('337293','"Golowich" lean'),('337830','"Togni" lean'),('333709','"Gerbner" "percolation" lean')]:
 fetch('https://api.github.com/search/repositories?q='+urllib.parse.quote(q),'github-author-'+i+'.json');time.sleep(7)
