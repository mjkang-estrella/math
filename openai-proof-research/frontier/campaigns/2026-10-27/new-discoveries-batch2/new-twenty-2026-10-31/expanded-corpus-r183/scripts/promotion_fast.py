from pathlib import Path
import ctypes,sys
D=Path(__file__).resolve().parents[1]
s=ctypes.CDLL(str(D/'outputs/promotion.so'));s.run.argtypes=[ctypes.c_int];s.run.restype=ctypes.c_int
assert s.run(int(sys.argv[1]))==0
