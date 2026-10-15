"""Rebuild the draft; a changed PDF requires renewed visual and manuscript review."""
from pathlib import Path
import argparse
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--tectonic', default='tectonic')
args = parser.parse_args()
root = Path(__file__).resolve().parent
(root / 'output/pdf').mkdir(parents=True, exist_ok=True)
(root / 'qa').mkdir(exist_ok=True)
commands = [
    [args.tectonic, '--keep-logs', '--outdir', 'output/pdf', 'main.tex'],
    ['pdftoppm', '-r', '95', '-png', 'output/pdf/main.pdf', 'qa/page'],
    ['pdftotext', '-layout', 'output/pdf/main.pdf', 'qa/main.txt'],
]
for command in commands:
    subprocess.run(command, cwd=root, check=True)
