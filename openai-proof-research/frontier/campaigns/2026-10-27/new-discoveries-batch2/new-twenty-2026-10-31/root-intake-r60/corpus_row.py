import json,glob,sys
from pathlib import Path
def row(i):
    C=Path(__file__).resolve().parent.parent
    for f in sorted(glob.glob(str(C/'../lanes/pi-mathdb-full-corpus-inventory-r301/corpus/*.jsonl'))):
        for line in open(f,encoding='utf-8'):
            if f'"mathdb_id": {i},' in line:
                r=json.loads(line)
                if r['mathdb_id']==i: return r
if __name__=='__main__':
    r=row(int(sys.argv[1])); print(r['title']); print(r['statement']); print(r['source_name'],r['source_url'])
