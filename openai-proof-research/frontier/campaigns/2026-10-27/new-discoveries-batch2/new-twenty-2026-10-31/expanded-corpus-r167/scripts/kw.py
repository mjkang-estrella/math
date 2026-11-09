import re,sys,pathlib
KW=r"egerv|deming|k[oö]nig|pseudoline|bichromatic|rigidity|well.dominat|strong.product|irredundant|colou?r.balanced|iswap|pieri|robinson.schensted|orlik|terao|zonotop|pancycl|bang.jensen|double.wheel|induced.minor|tree.independence|rainbow|kohnert|quadratic.variet|r[oö]dl|ksba|connective|monochromatic.component|apex|2205\.10598|2302\.06669|2306\.12222|2308\.12881|2309\.07747|2402\.17499|2403\.08303|2407\.01121|2407\.20849|2410\.07993|2411\.04898|2412\.18058|2502\.12768|2502\.14982|2504\.21628|2508\.16199|2509\.04026|2601\.20574|2602\.11892|2605\.19923"
ID=r"(?<![0-9a-f])(357416|372835|373112|374800|367172|367211|368246|369903|370158|362060|362299|363761|364157|365232|365712|366393|358858|359651|359935|354706)(?![0-9a-f])"
for f in sys.argv[1:]:
    t=pathlib.Path(f).read_text(errors='replace')
    for pat in (KW,ID):
        for m in re.finditer(pat,t,re.I):
            print(pathlib.Path(f).name,'|',m.group(0),'|',t[max(0,m.start()-70):m.end()+70].replace('\n',' '))
