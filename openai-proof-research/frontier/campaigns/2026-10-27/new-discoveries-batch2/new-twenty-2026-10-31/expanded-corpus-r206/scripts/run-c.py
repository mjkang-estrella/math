import pathlib,ctypes,sys
D=pathlib.Path(__file__).resolve().parents[1]
l=ctypes.CDLL(str(D/('scripts/meander12.so' if len(sys.argv)>2 else 'scripts/meander.so')));a=(ctypes.c_char_p*2)(b'meander',sys.argv[1].encode());l.main(2,a)
