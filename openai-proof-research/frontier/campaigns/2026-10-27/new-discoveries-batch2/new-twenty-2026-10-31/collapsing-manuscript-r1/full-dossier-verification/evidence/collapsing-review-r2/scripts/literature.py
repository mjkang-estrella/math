import runpy,sys,pathlib
p=str(pathlib.Path(__file__).with_name('fetch.py'))
for n,u in {
'hjjs-arxiv.pdf':'https://arxiv.org/pdf/0808.2383',
'fr2012.pdf':'https://arxiv.org/pdf/1104.3618',
'bsnormal.pdf':'https://arxiv.org/pdf/1508.05461',
'sullivant.pdf':'https://arxiv.org/pdf/0906.1784',
'rinaldo-thesis.pdf':'https://www.stat.cmu.edu/~brian/720-2007-source/nice%20materials/rinaldo-thesis.pdf',
}.items():
 sys.argv=[p,n,u];runpy.run_path(p,run_name='__main__')
