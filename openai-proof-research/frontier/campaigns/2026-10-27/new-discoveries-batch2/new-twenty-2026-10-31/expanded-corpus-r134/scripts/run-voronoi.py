import ctypes,sys,pathlib
f=ctypes.CDLL(str(pathlib.Path(__file__).with_name('voronoi.so').resolve()))
a=[b'voronoi']+[x.encode() for x in sys.argv[1:]]
f.main(len(a),(ctypes.c_char_p*len(a))(*a))
