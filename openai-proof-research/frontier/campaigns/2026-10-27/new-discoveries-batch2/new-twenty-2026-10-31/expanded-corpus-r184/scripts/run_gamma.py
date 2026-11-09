import ctypes,pathlib,sys
D=pathlib.Path(__file__).resolve().parents[1]
lib=ctypes.CDLL(str(D/'outputs/gamma.so'))
a=(ctypes.c_char_p*2)(b'gamma',sys.argv[1].encode());lib.main(2,a)
