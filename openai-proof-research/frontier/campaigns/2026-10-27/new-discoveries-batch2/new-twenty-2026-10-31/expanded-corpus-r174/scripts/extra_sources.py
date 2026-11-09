import pathlib,json,importlib.util
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r174')
s=importlib.util.spec_from_file_location('fetch',L/'scripts/fetch.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
for aid in ['2512.17342v1','2512.17342v2','2512.17342v3','2602.21427v1','2602.21427v2','2512.17114v1','2512.04486','2509.24354','2501.03754']:
 m.fetch('https://arxiv.org/html/'+aid,'sources/'+aid+'.html')
