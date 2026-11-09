import pathlib,json,re,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1];tree=json.loads((D/'sources/openai-preprints.body').read_text());pat=re.compile('hurlbert|universal.*cycl|permutation.*cycl|quasipolar|shuffle.*lattice|haros|Macchia',re.I)
r={'sha':tree['sha'],'truncated':tree.get('truncated'),'matches':[x['path'] for x in tree['tree'] if pat.search(x['path'])]};(D/'notes/openai-preprints-matches.json').write_text(json.dumps(r,indent=2));print(r)
# All known versions of the most relevant two companions, not only latest PDF.
args=[]
for name,a in [('uc-2019','1707.06110'),('uc-shortened','2204.02910')]:
 txt=(D/'sources'/f'{name}-abs.body').read_text()
 for v in re.findall(r'\[v([0-9]+)\]',txt):
  args.extend([name+'-v'+v,'https://arxiv.org/pdf/'+a+'v'+v])
subprocess.run([sys.executable,'-I','-B',str(D/'scripts/fetch.py'),*args],check=True)
for p in (D/'sources').glob('uc-*-v*.body'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))])
