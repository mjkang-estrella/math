for f in sorted((P/'texts').glob('*.txt')):
 s=f.read_text();print('FILE',f.name)
 hits=list(re.finditer(r'Conjecture[ \n]+[0-9]+|conjecture is|conjecture holds|disprov|counterexample|Theorem 1\.',s))
 for m in hits[-5:]:print(re.sub(r'\s+',' ',s[max(0,m.start()-70):m.end()+650]))
