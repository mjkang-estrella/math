import pathlib,urllib.parse,time
P=pathlib.Path(__file__).resolve().parent/'fetch.py';ns={'__name__':'fetch','__file__':str(P)};exec(compile(P.read_text(),str(P),'exec'),ns)
for key,q in [('nim-source','"1502.04068" "Duchene" lean'),('competition-source','"1503.05617" "Nakamura" lean'),('restraint-source','"1611.09536" "Erey" lean')]:
 ns['get']('github-search-'+key+'.json','https://api.github.com/search/repositories?q='+urllib.parse.quote(q));time.sleep(8)
