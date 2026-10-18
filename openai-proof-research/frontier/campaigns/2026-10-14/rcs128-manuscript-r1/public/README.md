# RCS128 manuscript source

Myeongjin Kang, no affiliation. Author-side manuscript, pending independent manuscript review. This is a source-relative theorem assuming the pinned ordinary superstring manuscript's count, layer, and connection contracts. It is not an independent proof of ordinary SCS. The companion Lean work proves sixteen support lemmas, not the algorithm.

The article is `article.tex`, with original section sources under `sections/` and manually checked references in `references.tex`. The generated 17-page article is `output/pdf/rcs128.pdf`. No third-party paper bodies are included.

Rebuild from this directory or a copy:

```sh
python3 build.py --output /absolute/path/to/NEW-output-directory --tectonic /path/to/tectonic
```

The output directory must not exist and must be outside this source directory. The tested engine is Tectonic 0.17.0 with its pre-existing cached TeX resources. The script runs offline (`--only-cached`), sets `SOURCE_DATE_EPOCH=1792195200` and `TZ=UTC`, preserves logs, compiles cross-references, and rejects overfull boxes or unresolved-reference warnings. It does not download or vendor TeX resources. A source copy built in a disposable directory produced exactly the same PDF bytes. Reproduction with another TeX engine/cache is not certified.

Original prose is CC BY 4.0; original code is MIT. See LICENSE.txt. Bibliographic references do not imply rights to redistribute third-party texts. Attribution and reading limitations are stated in the article and full packet ledger. Publication, acceptance and upload are not performed by this packet.
