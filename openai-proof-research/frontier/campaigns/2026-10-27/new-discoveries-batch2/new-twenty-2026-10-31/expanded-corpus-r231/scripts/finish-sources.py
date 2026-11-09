import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];o=json.loads((D/'sources/Sq-head.json').read_text());sha=o['sha'];todo=[('Sq-Main.lean','https://raw.githubusercontent.com/ShengtongZhang-alt/Sq/'+sha+'/Sq/Main.lean'),('Sq-Definition.lean','https://raw.githubusercontent.com/ShengtongZhang-alt/Sq/'+sha+'/Sq/Definition.lean')]
(D/'fetch-final.json').write_text(json.dumps(todo)+'\n')
