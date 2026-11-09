exec(compile((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text(),str(__import__('pathlib').Path(__file__).parent/'fetch.py'),'exec'))
if sys.argv[1]=='extra':
 for a in ['2409.18195','2306.15785','1907.06235']:
  get('https://arxiv.org/abs/'+a,a+'.html');get('https://arxiv.org/pdf/'+a,a+'.pdf')
 get('https://www.cambridge.org/core/services/aop-cambridge-core/content/view/D5EC200A0B634C26FC4617B3B4FACECE/S0017089500006480a.pdf/free_bands_and_free_bands.pdf','free-bands.pdf')
 s=json.loads((D/'sources/pool-head.json').read_text())['sha']
 for x in json.loads((D/'sources/pool-tree.json').read_text())['tree']:
  if x['path'].endswith('projects.yml'):get(f"https://raw.githubusercontent.com/Vilin97/lean-pool/{s}/{x['path']}",'pool-projects.yml')
elif sys.argv[1]=='extra2':
 get('https://cs.du.edu/~paulhorn/pap/flex.pdf','flex-prior.pdf')
 get('https://cse.hkust.edu.hk/faculty/cding/JOURNALS/amc211.pdf','design-published.pdf')
 get('https://pi.math.cornell.edu/~kbrown/papers/toronto.pdf','brown-bands.pdf')
 heads=json.loads((D/'outputs/registry-screen.json').read_text())['heads']
 s=heads['omega'];r=get(f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{s}','omega-root.json')
 if r.get('status')==200:
  for x in json.loads((D/'sources/omega-root.json').read_text())['tree']:
   if x['path'] in ['D5','Problems']:get(f"https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{x['sha']}?recursive=1",'omega-'+x['path']+'.json')
