import runpy,sys,pathlib,subprocess
L=pathlib.Path(__file__).resolve().parent
groups=[['1412.7408v1','1412.7488v4','1803.10224v2','1001.1571v2'],['2012.15502v1','math/0607789v1','math/0508327v1','1412.8682v1'],['1401.2313v1','1706.05230v1','2010.01511v1','0908.3473v1'],['0704.1914v1','1505.04806v4','1106.1883v1','1810.07919v2','1412.7408v3']]
for id in groups[int(sys.argv[1])]:
 name=id.replace('/','-')+'.pdf'
 sys.argv=['run.py','fetch',name,'https://arxiv.org/pdf/'+id];runpy.run_path(str(L/'run.py'),run_name='__main__')
 if (L/'primary'/name).exists():
  sys.argv=['run.py','text',name];runpy.run_path(str(L/'run.py'),run_name='__main__')
