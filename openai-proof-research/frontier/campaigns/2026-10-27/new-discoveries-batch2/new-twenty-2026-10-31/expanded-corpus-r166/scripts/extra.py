exec(compile(open('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r166/scripts/fetch.py').read().split("if sys.argv[1]")[0], 'fetch.py','exec'))
for url,name in [('https://arxiv.org/pdf/1803.09416','prior-broersma.pdf'),('https://web.math.princeton.edu/~mchudnov/isk4.pdf','prior-isk4.pdf'),('https://arxiv.org/pdf/2608.07360','prior-acmax.pdf'),('https://arxiv.org/pdf/1208.4253','prior-commuting.pdf'),('https://arxiv.org/html/1407.5480v1','328372-body.html')]:fetch(url,name)
sha=json.loads((D/'sources/lean-pool-head.json').read_text())['sha']
for p in ['LeanPool/ACMax.lean','LeanPool/ACMax/ACMax.lean']:fetch(f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/{p}','pool/'+p)
