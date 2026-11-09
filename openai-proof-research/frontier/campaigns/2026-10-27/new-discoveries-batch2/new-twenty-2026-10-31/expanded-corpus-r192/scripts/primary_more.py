import pathlib,json,runpy,sys
D=pathlib.Path(__file__).resolve().parents[1]
a=[('tableau-vor','https://www.combinatorics.org/ojs/index.php/eljc/article/download/v22i2p44/pdf/'),('word-vor','https://emis.de/ft/19479'),('anti-vor','https://www.combinatorics.org/ojs/index.php/eljc/article/download/v24i2p39/pdf/'),('beer-vor','https://ruj.uj.edu.pl/server/api/core/bitstreams/5b61b327-00d2-418e-bcb7-fe21633a988c/content'),('eta-vor','https://people.math.rochester.edu/faculty/doug/otherpapers/guillou-isaksen-eta.pdf'),('lss-followup','https://www.mathematik.uni-marburg.de/~welker/preprints/FinalLSS.pdf'),('supersimple-followup','https://arxiv.org/pdf/1510.06680'),('anti-followup','https://arxiv.org/pdf/1604.08819'),('bisection-followup','https://www.tandfonline.com/doi/full/10.1016/j.akcej.2020.01.001')]
args=[]
for name,url in a:args += [name,url]
sys.argv=[str(D/'scripts/fetch.py')]+args;runpy.run_path(sys.argv[0],run_name='__main__')
