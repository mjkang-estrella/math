import pathlib
D=pathlib.Path(__file__).resolve().parents[1];s=(D/'scripts/word_sam.py').read_text();s=s.replace("json.loads((D/'outputs/words-random.json').read_text())['best_ratio'][1]['directive']","json.loads((D/'outputs/word-sam.json').read_text())['best'][1]['directive']").replace('range(600)','range(2000)').replace('j<400','j<1600').replace('65536','131072').replace("outputs/word-sam.json","outputs/word-sam-extended.json")
# Keep the input from the completed first SAM run.
s=s.replace("json.loads((D/'outputs/word-sam-extended.json').read_text())","json.loads((D/'outputs/word-sam.json').read_text())")
(D/'scripts/word_sam_extended.py').write_text(s)
