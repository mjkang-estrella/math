exec(compile(open('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r186/scripts/fetch.py').read().split("if __name__")[0],'fetch.py','exec'))
vers=json.loads((L/'outputs/versions.json').read_text())
start=int(sys.argv[1]);end=int(sys.argv[2])
for i,r in list(vers.items())[start:end]:
 for v in r['versions']:
  fetch('https://arxiv.org/pdf/'+r['arxiv']+'v'+v,i+'-v'+v+'-pdf')
