import pathlib,json,urllib.parse
L=pathlib.Path(__file__).resolve().parents[1]
u=[['https://arxiv.org/pdf/2411.09698','hamming-followup'],['https://arxiv.org/pdf/1912.08328','ramsey-followup'],['https://arxiv.org/pdf/2610.18713','exponents-followup']]
for n in ['openai','omega']:
 x=json.loads((L/f'sources/{n}-head/body').read_text())
 u.append([f"https://api.github.com/repos/{'openai/math' if n=='openai' else 'the-omega-institute/trureturing'}/git/trees/{x['sha']}",n+'-root-nonrecursive'])
(L/'scripts/extraurls.json').write_text(json.dumps(u))
