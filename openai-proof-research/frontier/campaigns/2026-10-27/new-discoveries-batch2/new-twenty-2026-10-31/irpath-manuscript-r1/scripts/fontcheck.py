"""Report TrueType table tags and coverage of the characters the manuscript needs (read-only)."""
import sys
sys.dont_write_bytecode = True
import struct

FONTS = ["/usr/share/fonts/liberation-serif-fonts/LiberationSerif-Regular.ttf",
         "/usr/share/fonts/liberation-serif-fonts/LiberationSerif-Italic.ttf",
         "/usr/share/fonts/liberation-serif-fonts/LiberationSerif-Bold.ttf",
         "/usr/share/fonts/liberation-mono-fonts/LiberationMono-Regular.ttf",
         "/usr/share/fonts/google-noto/NotoSansMath-Regular.ttf"]
NEED = "∈∉⊆⊂⊊⊄≅≃¬∀∃∅∪∩→←↔≥≤−⋂⋃∧∨×·…–—‘’“”§≠∼∖ℕ⟨⟩□∎Γγπ√ΔḠ̄"


def cmap_chars(b):
    n = struct.unpack_from(">H", b, 4)[0]
    tabs = {b[12 + 16 * i:16 + 16 * i].decode("latin1"): struct.unpack_from(">II", b, 20 + 16 * i) for i in range(n)}
    off, _ = tabs["cmap"]
    cm = b[off:]
    chars = set()
    for k in range(struct.unpack_from(">H", cm, 2)[0]):
        pid, eid, so = struct.unpack_from(">HHI", cm, 4 + 8 * k)
        fmt = struct.unpack_from(">H", cm, so)[0]
        if fmt == 4:
            segx2 = struct.unpack_from(">H", cm, so + 6)[0]
            for j in range(segx2 // 2):
                end = struct.unpack_from(">H", cm, so + 14 + 2 * j)[0]
                start = struct.unpack_from(">H", cm, so + 16 + segx2 + 2 * j)[0]
                chars.update(range(start, end + 1))
    return sorted(tabs), chars


for f in FONTS:
    b = open(f, "rb").read()
    tags, chars = cmap_chars(b)
    print(f.split("/")[-1], len(b), "glyf" in tags, "CFF " in tags, "missing:", "".join(c for c in NEED if ord(c) not in chars))
