from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED
root=Path(__file__).resolve().parent.parent
modules=(root/'module-order.txt').read_text().splitlines()
with ZipFile(root/'proof-source.zip','w',ZIP_DEFLATED) as z:
    for module in modules:
        z.write(root/'src'/f'{module}.lean',f'{module}.lean')
    z.write(root/'module-order.txt','module-order.txt')
