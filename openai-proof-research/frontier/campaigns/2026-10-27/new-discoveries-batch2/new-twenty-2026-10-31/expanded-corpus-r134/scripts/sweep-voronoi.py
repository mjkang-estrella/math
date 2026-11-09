import pathlib,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1]
for n,k in [(3,5),(3,6),(3,7),(3,8),(4,6),(4,7),(4,8),(4,9),(4,10),(5,5),(5,6),(5,7),(6,5)]:
 subprocess.run([sys.executable,str(D/'scripts/limited.py'),f'voronoi-n{n}k{k}',sys.executable,str(D/'scripts/run-voronoi.py'),str(n),str(k)],check=True)
 print((D/f'logs/voronoi-n{n}k{k}.log').read_text(),flush=True)
