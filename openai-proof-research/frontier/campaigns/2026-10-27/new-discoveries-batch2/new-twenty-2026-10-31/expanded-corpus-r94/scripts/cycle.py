import ctypes,sys,pathlib
ctypes.CDLL(str(pathlib.Path(__file__).with_suffix('.so').resolve())).run(int(sys.argv[1]))
