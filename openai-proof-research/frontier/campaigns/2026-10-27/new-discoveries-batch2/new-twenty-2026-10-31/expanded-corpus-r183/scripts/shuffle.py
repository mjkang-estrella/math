from pathlib import Path
import ctypes,sys
D=Path(__file__).resolve().parents[1]
a=ctypes.CDLL(str(D/'outputs/shuffle.so'));a.run.argtypes=[ctypes.c_int];a.run.restype=ctypes.c_int
for n in range(int(sys.argv[1]),int(sys.argv[2])+1):assert a.run(n)==0
