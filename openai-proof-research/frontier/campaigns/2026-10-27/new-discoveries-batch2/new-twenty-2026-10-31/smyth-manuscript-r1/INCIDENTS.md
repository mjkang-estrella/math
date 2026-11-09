# Development record

- Initial staging lacked the receipts directory; data copying and safe extraction completed before receipt writing failed. The directory was created and staging was rerun. No input was altered.
- System reportlab and TeX engines were unavailable. Groff had no PDF device or installed ms macros. Failed authoring calls are recorded in receipts. The final build uses a local macro file, groff PostScript and Ghostscript; no installation or network access was used.
- Initial render review caught absent section headings and incorrect superscript/subscript grouping. These were corrected and all final pages were rendered and inspected again. Historical generator patch scripts remain for provenance; do not rerun them.
- The b=31..43 family batch reached its existing CPU cap after completing b=42. It exited without a b=43 result; no cap was increased. A separate capped b=43 run succeeded. That batch's negative exit and sampled RSS are preserved in receipts/family31-43.json. No job was left running.
- All authored files are within this lane. No git, network, messages, browser, Lean, lake, leanchecker, child agents or shared-ledger edits were used. The PDF skill's marker was run successfully; its standard reportlab recommendation was replaced by the available local toolchain.
