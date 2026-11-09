from pathlib import Path
import os, json, subprocess, hashlib
lane = Path(__file__).resolve().parent.parent
modules = ['ShoeBase','ShoeProbability','ShoeStopping','ShoeBlock','ShoePair',
           'ShoeConditional','ShoeDiagonal','ShoeTermination','ShoeControls','ShoeAxiomAudit']
build = lane/'replay/build'
build.mkdir(parents=True,exist_ok=True)
assert not list(build.iterdir()), 'Replay requires an empty build'
pins = json.loads((lane/'PINS.json').read_text())
upstream = os.environ['LEAN_PATH'].split(':')[1:]
assert all(str(lane) not in p for p in upstream)
env = dict(os.environ)
env['LEAN_PATH'] = ':'.join([str(build)]+upstream)
records=[]
for module in modules:
    source=lane/'src'/f'{module}.lean'
    rel=f'replay/src/{module}.lean'
    subprocess.run(['python3','-I','-B',str(lane/'write_lane.py'),rel],
                   input=source.read_text(),text=True,check=True)
    copied=lane/rel
    assert source.read_bytes()==copied.read_bytes()
    cmds=[(f'replay_lean_{module}',[pins['lean_bin'],'-j1','-M3500','-DwarningAsError=true',
          '-o',str(build/f'{module}.olean'),str(copied)]),
          (f'replay_checker_{module}',[pins['leanchecker_bin'],module])]
    for label,cmd in cmds:
        subprocess.run(['python3','-I','-B',str(lane/'runner.py'),label,'--']+cmd,
                       env=env,cwd=lane,check=True)
    assert source.read_bytes()==copied.read_bytes()
    records.append({'module':module,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
                    'copied_source_sha256':hashlib.sha256(copied.read_bytes()).hexdigest(),
                    'post_checker_olean_sha256':hashlib.sha256((build/f'{module}.olean').read_bytes()).hexdigest()})
subprocess.run(['python3','-I','-B',str(lane/'write_lane.py'),'results/PARTIAL-REPLAY.json'],
 input=json.dumps({'scope':'Current partial modules only; no literal endpoint exists',
 'initial_build_empty':True,'lean_path':env['LEAN_PATH'],'records':records},indent=2)+'\n',
 text=True,check=True)
