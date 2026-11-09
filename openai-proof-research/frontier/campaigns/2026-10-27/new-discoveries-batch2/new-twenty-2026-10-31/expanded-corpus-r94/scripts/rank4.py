import ctypes,sys,pathlib
lib=ctypes.CDLL(str(pathlib.Path(__file__).with_suffix('.so').resolve()))
for n in range(int(sys.argv[1]),int(sys.argv[2])+1):
 for model in [0,1]:lib.run(n,model)
