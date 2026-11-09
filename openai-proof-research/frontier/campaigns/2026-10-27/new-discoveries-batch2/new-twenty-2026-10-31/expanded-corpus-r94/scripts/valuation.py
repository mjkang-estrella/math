import ctypes,pathlib,sys
ctypes.CDLL(str(pathlib.Path(__file__).with_suffix('.so').resolve())).run(int(sys.argv[1]),int(sys.argv[2]))
