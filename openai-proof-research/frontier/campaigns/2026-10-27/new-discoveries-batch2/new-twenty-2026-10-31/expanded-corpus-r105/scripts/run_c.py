import ctypes,sys,pathlib
p=pathlib.Path(__file__).resolve().parent
lib=ctypes.CDLL(str(p/'lengyel.so'));args=[b'lengyel']+[x.encode() for x in sys.argv[1:]];lib.main(len(args),(ctypes.c_char_p*len(args))(*args))
