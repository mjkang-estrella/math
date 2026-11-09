exec(compile((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text().split('with concurrent.futures.ThreadPoolExecutor')[0],str(__file__),'exec'))
jobs=[('fair-thesis.pdf','https://dyuthi.cusat.ac.in/xmlui/bitstream/handle/purl/5086/Dyuthi-T2152.pdf.pdf?sequence=1'),('wang.pdf','https://arxiv.org/pdf/2609.29878v5')]
for n in ['BalancedRyser','RyserCovering','RyserOddExtensions']:
 jobs.append((n+'.lean','https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/lean/ComparatorChallenges/'+n+'.lean'))
jobs.append(('Nielsen.lean','https://raw.githubusercontent.com/openai/math/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Analysis/FreeGroupFactor/Nielsen.lean'))
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(fetch,jobs):print(r,flush=True)
