from pathlib import Path
import urllib.parse
exec(Path('scripts/prior_refresh.py').read_text().split('for short,repo in ')[0])
queries=[('pragada-search','Pragada, Shivaramakrishna','author'),('kumar-wheel-search','Kumar wheel chromatic','all'),('ultimate-search','ultimate independence ratio','all'),('wheel-chromatic-search','wheel chromatic','all')]
for n,q,typ in queries:get(n,'https://arxiv.org/search/?'+urllib.parse.urlencode(dict(query=q,searchtype=typ,abstracts='show',order='-announced_date_first',size=50)))
for a in ['2610.13852','2607.19817','2609.00210','2607.05961','2607.22915']:get('body-'+a,'https://arxiv.org/html/'+a)
