from fetch import get
for key,sha in [('D5', 'cdaa43926262bac33e2144adcffcc2bc48c8edf0'), ('Problems', '2d71ae5398ba520674e52fe6de87ab880bac595a')]:
 print(get(("omega-"+key+".json","https://api.github.com/repos/the-omega-institute/trureturing/git/trees/"+sha+"?recursive=1")),flush=True)
print(get(("2406.02982.html","https://arxiv.org/html/2406.02982")),flush=True)
