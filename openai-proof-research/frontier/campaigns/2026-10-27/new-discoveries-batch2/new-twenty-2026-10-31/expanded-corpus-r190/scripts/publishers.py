import pathlib,json,sys,runpy
D=pathlib.Path(__file__).resolve().parents[1]
urls=[('vor-334235','https://doi.org/10.1007/s11005-017-0950-2'),('vor-334453','https://yufeizhao.com/research/extremal-regular-graphs.pdf'),('vor-329603','https://www.research.lancs.ac.uk/portal/services/downloadRegister/245000276/NSTWexpandingspheresSubmitted.pdf'),('vor-path','https://www.combinatorics.org/ojs/index.php/eljc/article/download/v24i3p41/pdf/'),('vor-occupancy','https://www.ams.org/mcom/2026-95-360/S0025-5718-2025-04121-2/S0025-5718-2025-04121-2.pdf')]
args=[]
for a,b in urls[int(sys.argv[1]):int(sys.argv[2])]:args += [a,b]
sys.argv=[str(D/'scripts/fetch.py')]+args;runpy.run_path(str(D/'scripts/fetch.py'),run_name='__main__')
