"""Exclusive inventory/seal controls. Never overwrites or regenerates a seal."""
import ast
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(__file__).resolve().parent


def verifier():
    path=BASE/"verify.py"
    ns={"__file__":str(path),"__name__":"packaging_control"}
    exec(compile(path.read_bytes(),str(path),"exec"),ns)
    return ns


def write_json(path, data):
    with path.open("x") as out:
        json.dump(data,out,indent=2,sort_keys=True)
        out.write("\n")


def reserve():
    assert not (BASE/"inventory.json").exists()
    v=verifier()
    for name,args in (("inventory",["package.py","inventory"]),
                      ("prevalidation",["verify.py","--prevalidate"]),
                      ("seal",["package.py","seal"]),
                      ("final-replay",["verify.py"])):
        directory=BASE/(name+"-sources")
        directory.mkdir()
        for path in sorted(BASE.glob("*.py")):
            ast.parse(path.read_bytes(),filename=path.name)
            with (directory/path.name).open("xb") as out:
                out.write(path.read_bytes())
        write_json(BASE/(name+"-invocation.json"),
                   {"argv":["python3","-I","-B",*args],
                    "sources":[v["record"](p.relative_to(ROOT).as_posix())
                               for p in sorted(directory.iterdir())],
                    "output":"Prevalidation controls capture stdout/stderr; "
                             "other control and final read-only receipts go to caller."})
    # Files exist but stay empty during prevalidation until the final print.
    for name in ("prevalidation.json","prevalidation.stderr"):
        with (BASE/name).open("xb"):
            pass
    print(json.dumps({"status":"RESERVED","source_sets":4}))


def inventory():
    v=verifier()
    assert not (BASE/"seal.json").exists()
    for name in ("prevalidation.json","prevalidation.stderr"):
        assert (BASE/name).read_bytes()==b""
    controls=v["CONTROLS"]
    rows=[v["record"](p) for p in v["membership"]() if p not in controls]
    write_json(BASE/"inventory.json",{
        "status":"I183_BOUNDED_FINALIZATION","owned":rows,"controls":controls,
        "policy":"Only generated controls omitted from owned rows; "
                 "seal binds inventory, successful prevalidation and empty stderr."})
    print(json.dumps({"status":"INVENTORIED","owned":len(rows)}))


def seal():
    v=verifier()
    assert not (BASE/"seal.json").exists()
    inv=(BASE/"inventory.json").read_bytes()
    pre=(BASE/"prevalidation.json").read_bytes()
    stderr=(BASE/"prevalidation.stderr").read_bytes()
    envelope=v["seal_record"](inv,pre,stderr)
    v["validate_controls"](inv,envelope,pre,stderr)
    assert json.loads(pre)["seal_link_pretests"]==5
    inventory=json.loads(inv)
    assert v["membership"]()==sorted(
        {x["path"] for x in inventory["owned"]} |
        (set(v["CONTROLS"])-{v["SEAL"]}))
    for row in inventory["owned"]:
        assert v["record"](row["path"])==row
    frozen=json.loads((BASE/"inputs.json").read_bytes())
    for row in frozen["strict"]:
        assert v["record"](row["path"])==row
    assert [v["record"](p) for p in v["CONTEXT"]]==json.loads(pre)["contexts_current"]
    write_json(BASE/"seal.json",envelope)
    print(json.dumps({"status":"SEALED_ONCE",
                      "seal_sha256":hashlib.sha256((BASE/"seal.json").read_bytes()).hexdigest()}))


if __name__=="__main__":
    assert sys.flags.isolated and sys.dont_write_bytecode
    {"reserve":reserve,"inventory":inventory,"seal":seal}[sys.argv[1]]()
