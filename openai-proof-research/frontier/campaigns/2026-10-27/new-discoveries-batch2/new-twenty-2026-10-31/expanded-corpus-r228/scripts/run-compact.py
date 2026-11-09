import pathlib,ctypes,sys
D=pathlib.Path(__file__).resolve().parents[1];lib=ctypes.CDLL(str(D/'scripts/compact-inversions.so'))
for n in range(int(sys.argv[1]),int(sys.argv[2])+1):
 for k in map(int,sys.argv[3:]):
  if lib.run(n,k):raise RuntimeError((n,k))
