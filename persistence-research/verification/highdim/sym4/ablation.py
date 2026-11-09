"""Bounded ablation on the two first-pass successes; save complete trees only."""
import sys
sys.dont_write_bytecode = True
import concurrent.futures
import json
import multiprocessing
import pathlib
import signal
import time

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
from gen_sym import Generator, Budget
from gen_precomputed import PrecomputedGenerator


def run(args):
    key, rec, variant = args
    old = json.loads((HERE.parent/'supply_B.json').read_text())
    new = json.loads((HERE/'supply.json').read_text())
    choices = {
        'baseline':(Generator,old,(2,3,7,3,2,2,2,3)),
        'schedule':(Generator,old,(2,3,2,3,5,2)),
        'tailrank':(PrecomputedGenerator,old,(2,3,2,3,5,2)),
        'supply':(PrecomputedGenerator,new,(2,3,2,3,5,2))}
    constructor,supply,schedule = choices[variant]
    def alarm(*unused):
        raise Budget('wall alarm')
    signal.signal(signal.SIGALRM,alarm)
    signal.setitimer(signal.ITIMER_REAL,25)
    start = time.monotonic()
    K = 9*rec['S_low']-1
    q = max(3,(K & -K).bit_length())
    g = constructor(rec['far'],K,q,supply=supply,seconds=25,lifts=100000000,
                    nodes=1000000,mcap=10**72,depth=250)
    out = {'key':key,'variant':variant,'status':'BUDGET'}
    try:
        g.run(schedule)
        file = HERE/'certs'/'ablation'/('%s_K%d.jsonl'%(variant,K))
        g.write(file,extra={'ablation':variant,'configuration':key})
        out.update(status='COMPLETE_PENDING_CHECKS',file=str(file))
    except Budget as e:
        out['reason']=str(e)
    finally:
        signal.setitimer(signal.ITIMER_REAL,0)
    out.update(seconds=round(time.monotonic()-start,3),nodes=len(g.nodes),lifts=g.lifts,
               trace=g.trace,at=g.at)
    return out


def main():
    cfg = json.loads((HERE/'assignment.json').read_text())['configurations']
    keys = ('14112:263|9,9,45,54','14112:663|9,9,18,45')
    output = []
    with concurrent.futures.ProcessPoolExecutor(max_workers=8,mp_context=multiprocessing.get_context('fork')) as pool:
        futures = [pool.submit(run,(key,cfg[key],variant)) for key in keys
                   for variant in ('baseline','schedule','tailrank','supply')]
        for f in concurrent.futures.as_completed(futures):
            output.append(f.result())
            (HERE/'ablation_results.json').write_text(json.dumps(output,indent=1)+'\n')
            print(output[-1]['key'],output[-1]['variant'],output[-1]['status'],output[-1]['seconds'],flush=True)


if __name__ == '__main__':
    main()
