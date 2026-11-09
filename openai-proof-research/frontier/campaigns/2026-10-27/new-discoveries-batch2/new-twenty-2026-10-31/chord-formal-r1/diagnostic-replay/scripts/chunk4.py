from pathlib import Path
for k in range(4):
 p=Path(f'ChordFour{k}.lean');s=p.read_text();start=s.index(f'theorem exception{k}_raw');end=s.index(f'theorem exception{k}_values')
 out=[]
 for mask in range(16):
  bits=' '.join('true' if mask>>i&1 else 'false' for i in range(4))
  c=f'side8{k} {bits} b4 b5 b6 b7'
  out.append(f'theorem exception{k}_chunk{mask} : ∀ b4 b5 b6 b7 : Bool, boundary exception{k} ({c}) = 2 ∨ boundary exception{k} ({c}) = 4 := by decide')
 args=' '.join(f'b{i}' for i in range(8));c=f'side8{k} {args}'
 out += [f'theorem exception{k}_raw : ∀ {args} : Bool, boundary exception{k} ({c}) = 2 ∨ boundary exception{k} ({c}) = 4 := by',f'  intro {args}','  cases b0 <;> cases b1 <;> cases b2 <;> cases b3','  all_goals first']
 out += [f'    | exact exception{k}_chunk{mask} b4 b5 b6 b7' for mask in range(16)]
 p.write_text(s[:start]+'\n'.join(out)+'\n'+s[end:])
