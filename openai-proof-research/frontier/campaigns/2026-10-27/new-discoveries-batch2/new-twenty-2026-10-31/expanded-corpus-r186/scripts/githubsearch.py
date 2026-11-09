exec(compile(open('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r186/scripts/fetch.py').read().split("if __name__")[0],'fetch.py','exec'))
queries=['"1802.09513" lean','"1805.05196" lean','"1801.03432" lean','"1807.11012" lean','"1802.04511" lean','"1803.03954" lean','"1802.03817" lean','"1801.03379" lean']
out=[]
for j,q in enumerate(queries):
 if j:time.sleep(8)
 d,r=fetch('https://api.github.com/search/repositories?q='+urllib.parse.quote(q),'github-search-'+str(j+1));out.append({'query':q,'receipt':r,'response':json.loads(d) if d else None})
 if r.get('status') in [403,429]: break
(L/'outputs/github-search.json').write_text(json.dumps(out,indent=2))
