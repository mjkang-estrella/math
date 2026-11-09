import ctypes,pathlib,sys
D=pathlib.Path(__file__).resolve().parents[1];lib=ctypes.CDLL(str(D/'scripts/inversions128.so'))
for n in range(int(sys.argv[1]),int(sys.argv[2])+1):
 for k in range(3,n+1):
  if lib.run(n,k):raise RuntimeError((n,k))
