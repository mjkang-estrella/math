# T212M release development

This mutable development directory is not a sealed release or an acceptance gate. Manuscript review remains pending. It supplements, without modifying, the frozen preparation scaffold.

`reproduce_supplement.py` builds the two original Lean modules and the separately reviewed `Independent.lean` in a new output directory. It authenticates both externally supplied frozen manifest anchors and every used source, lock, execution receipt and reference log. It checks the exact compiler binary and dependency commits, then requires the entire fresh inventory log to equal the independently reviewed log byte for byte. It writes nothing in the source packets or dependency cache. Cache metadata is fingerprinted before and after; this is not a rebuild or content authentication of every cached dependency artifact.

Run with absolute paths and a new output directory:

```sh
python3 -B reproduce_supplement.py \
  --formal /absolute/path/t212m-formal-v1 \
  --review /absolute/path/t212m-formal-review-r1 \
  --formal-anchor cc09818fed56aa44deda1f8fb9baf6d018bf6d4c3f8317f7bb6612f31624ce00 \
  --review-anchor 9e5a5cf03fab9b0759048f28848156d26d811981203df5e21b5ee556b5ea01fc \
  --lean /absolute/path/to/lean \
  --cache /absolute/path/to/pinned/packages \
  --output /var/tmp/t212m-supplement-fresh
```

The positive replay passed with identical inventory output: 17 original-module constants, 34 control-module constants, and 60 reviewer constants. Six copied-input refusal cases cover a wrong anchor, modified or linked supplement, linked packet root, output overlap, and missing reference log. See the two JSON receipts. This replay does not repeat the independent review's semantic mutation experiments, add a new mathematical review, or formalize the stochastic theorem.

Final release integration must explicitly add `t212m-formal-review-r1/independent-logs/Independent.lean.log` to the public selection; the frozen preparation selection currently includes the execution receipt and source but omits this reference log. The final release must authenticate its whole selected inventory separately: this driver only authenticates the particular inputs it consumes. It must also bind the actual manuscript verdict and parent adoption before assembly and acceptance.

Original driver copyright Myeongjin Kang, MIT. The independent source and evidence retain their reviewer provenance. Compiler and cached dependencies are trusted, not rebuilt. No upload or publication.
