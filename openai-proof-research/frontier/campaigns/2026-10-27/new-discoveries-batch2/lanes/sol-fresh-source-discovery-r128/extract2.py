from extract import Parser
from research import H
import subprocess
for n in ['partite-v2','spectral-public-proof','spectral-public-versions']:
 p=Parser();p.feed((H/'sources'/f'{n}.html').read_text());(H/'sources'/f'{n}.txt').write_text(''.join(p.a))
subprocess.run(['pdftotext','-layout',str(H/'sources/domino-companion.pdf'),str(H/'sources/domino-companion.txt')],check=True)
