import json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
h=json.loads((D/'sources/openai-head.json').read_text())['sha']
q=[('openai-root.json',f'https://api.github.com/repos/openai/math/git/trees/{h}'),('openai-contents.md',f'https://raw.githubusercontent.com/openai/math/{h}/CONTENTS.md'),('multicone-proof.html','https://www.researchgate.net/publication/331154809_C_Which_multicone_graphs_n_m_K_K_are_determined_by_their_signless_Laplacian_spectrum_The_proof_of_a_conjecture'),('sphere-2026.pdf','https://www.ejgta.org/index.php/ejgta/article/viewFile/1957/pdf_351')]
(D/'queue3.json').write_text(json.dumps(q))
