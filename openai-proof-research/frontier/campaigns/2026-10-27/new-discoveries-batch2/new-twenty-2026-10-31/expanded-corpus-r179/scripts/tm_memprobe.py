import sys,resource,runpy
sys.argv=['tm_ap2.py',sys.argv[1],sys.argv[2],'NOSTAGE3']
g=runpy.run_path(sys.argv[0].replace('tm_ap2.py','')+__file__.replace('tm_memprobe.py','tm_ap2.py'),run_name='__main__')
print('maxrss MB',resource.getrusage(resource.RUSAGE_SELF).ru_maxrss//1024)
