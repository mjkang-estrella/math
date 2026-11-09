exec(compile(open('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r166/scripts/fetch.py').read().split("if sys.argv[1]")[0], 'fetch.py','exec'))
for aid,name in [('1301.2341','prior-commuting-correct'),('2404.02244','prior-pfr')]:fetch('https://arxiv.org/pdf/'+aid,name+'.pdf')
