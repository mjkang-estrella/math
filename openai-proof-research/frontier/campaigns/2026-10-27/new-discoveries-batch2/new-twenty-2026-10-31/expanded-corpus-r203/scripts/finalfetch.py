import sys,pathlib
sys.path.insert(0,str(pathlib.Path(sys.argv[1])/'scripts'));from fetch import fetch
fetch('https://doi.org/10.37236/15082','vor-fs-doi')
