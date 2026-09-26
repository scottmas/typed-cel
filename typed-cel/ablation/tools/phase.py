import subprocess, sys, re, collections
B, tr, disp, ret_line = sys.argv[1], sys.argv[2], sys.argv[3].split(","), sys.argv[4]
addrs = [l.strip() for l in open(tr) if l.strip()]
uniq = sorted(set(addrs))
p = subprocess.run(["addr2line", "-C", "-e", B] + ["0x" + a for a in uniq],
                   capture_output=True, text=True).stdout.splitlines()
loc = {a: re.sub(r".*/(src|benches|library)/", r"\1/", p[i]).split(" ")[0] for i, a in enumerate(uniq)}
L = [loc[a] for a in addrs]
first = next(i for i, l in enumerate(L) if l in disp)
last = max(i for i, l in enumerate(L) if l == ret_line)
c = collections.Counter()
for i, l in enumerate(L):
    if l.startswith("benches/ablation.rs") and "Facts" not in l or "result.rs" in l or "hint.rs" in l:
        c["harness"] += 1
    elif i < first: c["fixed entry"] += 1
    elif i > last: c["fixed exit"] += 1
    elif l in disp: c["dispatch"] += 1
    elif "host.rs" in l: c["Facts read"] += 1
    elif l == "??:0" or "cmp.rs" in l: c["string compare"] += 1
    else: c["op bodies"] += 1
for k, v in c.most_common(): print(f"{v:5d}  {k}")
print(f"{len(L):5d}  TOTAL")
