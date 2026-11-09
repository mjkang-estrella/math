import pathlib,json,importlib.util,sys
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r174')
s=importlib.util.spec_from_file_location('fetch',L/'scripts/fetch.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
for aid in list(dict.fromkeys(d['record']['source_url'].split('/')[-1] for d in json.loads((L/'outputs/intake.json').read_text()).values()))[int(sys.argv[1]):int(sys.argv[2])]:
 m.fetch('https://arxiv.org/abs/'+aid,'sources/abs-'+aid+'.html')
