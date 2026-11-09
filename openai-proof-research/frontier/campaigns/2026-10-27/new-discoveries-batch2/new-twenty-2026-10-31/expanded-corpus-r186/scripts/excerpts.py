import pathlib,re,json
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r186')
out=[]
for p in sorted((L/'sources').glob('*-pdf.txt')):
 if re.search(r'-v[1234]-pdf',p.name):continue
 s=p.read_text(); lines=s.splitlines(); matches=[i for i,l in enumerate(lines) if re.search('Conjecture|conjecture|Theorem 2.3|Theorem 2\\.',l)]
 out.append('\nFILE '+p.name+'\n'+'\n'.join('\n'.join(lines[max(0,i-2):i+8]) for i in matches[:12]))
(L/'outputs/excerpts.txt').write_text('\n'.join(out))
