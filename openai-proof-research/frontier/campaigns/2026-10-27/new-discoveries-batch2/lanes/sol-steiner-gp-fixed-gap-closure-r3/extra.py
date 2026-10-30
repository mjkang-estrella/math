from work import *
for i,pii in [(10,'S0166218X24001719'),(19,'S0166218X2600034X')]:
 fetch('https://www.sciencedirect.com/science/article/abs/pii/'+pii,f'citations/{i}-source.html')
fetch('https://mathdb.com/api/search?q=Steiner%20general%20position&limit=40','mathdb-search.json')
# Public immutable commit patch is a distinct ordinary source representation, not an access-control workaround.
for c in ['9e4754fb1dc0369470b4719571ff1b2dda64511b']:
 fetch('https://github.com/the-omega-institute/trureturing/commit/'+c+'.patch','patches/'+c+'.patch')
