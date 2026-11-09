import ctypes,sys,pathlib
lib=ctypes.CDLL(str(pathlib.Path(__file__).resolve().parent/'chip_fast.so'));args=[b'chip']+[x.encode()for x in sys.argv[1:]];lib.main(len(args),(ctypes.c_char_p*len(args))(*args))
