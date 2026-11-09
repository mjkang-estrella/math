import pathlib
p=pathlib.Path(__file__).resolve().parent/'verify_morse.py'
s=p.read_text().replace("len(str(full[0]))", "full[0].bit_length()")
exec(compile(s,str(p),'exec'))
