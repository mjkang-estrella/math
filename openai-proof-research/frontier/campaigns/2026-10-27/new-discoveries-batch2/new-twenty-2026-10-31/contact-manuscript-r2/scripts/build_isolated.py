from pathlib import Path
import sys,runpy
lane=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(lane/"tmp/pdf-deps"))
runpy.run_path(str(lane/"paper/build_paper.py"),run_name="__main__")
