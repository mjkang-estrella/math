from pathlib import Path
s=Path('ChordFourWitnesses.lean').read_text()
head=s[:s.index('/-- Literal')]
chunks=s[s.index('/-- Literal'):].split('/-- Literal')
for k,chunk in enumerate(chunks[1:]):
    chunk=chunk.removesuffix('end Chord\n')
    Path(f'ChordFour{k}.lean').write_text(head+'/-- Literal'+chunk+'end Chord\n')
Path('ChordFourWitnesses.lean').write_text(''.join(f'import ChordFour{k}\n' for k in range(4)))
