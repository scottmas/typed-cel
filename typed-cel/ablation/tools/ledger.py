"""Fill one story's column of docs/PERFORMANCE.md's "Fast-path ledger" from a `--cycles-median` file.

    python3 tools/ledger.py <median-file> <column: S2..S6> ../docs/PERFORMANCE.md
"""
import sys

median, column, doc = sys.argv[1], sys.argv[2], sys.argv[3]
COL = {"bytecode_facts": "(3b)", "specialized": "(4)"}
cells, nested = {}, {}
for line in open(median):
    if not line.startswith("@cycles\t"):
        continue
    _, wid, col, ns, cyc = line.rstrip("\n").split("\t")[:5]
    if col in COL:
        cells[(wid, COL[col])] = f"{float(cyc):.0f} ({float(ns):.1f})"
    if wid == "nested_fields":
        nested[col] = (cyc, ns)
if nested:
    f = lambda c: f"{float(nested[c][0]):.0f}"
    cells[("nested_fields", "floor: lean / fused / closures")] = (
        f"{f('floor_lean')} / {f('floor_fused')} / {f('floor_closures')}"
    )
    cells[("nested_fields", "Rust")] = f"{f('rust')} ({float(nested['rust'][1]):.1f})"

lines = open(doc).read().split("\n")
start = lines.index("### Fast-path ledger")
header = next(i for i in range(start, len(lines)) if lines[i].startswith("| workload |"))
at = [c.strip() for c in lines[header].strip("|").split("|")].index(column)
filled = 0
i = header + 2
while i < len(lines) and lines[i].startswith("|"):
    c = [x.strip() for x in lines[i].strip("|").split("|")]
    key = (c[0].strip("`"), c[1])
    if key in cells:
        c[at] = cells[key]
        filled += 1
    lines[i] = "| " + " | ".join(c) + " |"
    i += 1
open(doc, "w").write("\n".join(lines))
print(f"{column}: filled {filled} rows")
