"""Write audit/AuditAll.lean: `#print axioms` for every theorem in ReleasePath/."""
import re
from pathlib import Path

root = Path(__file__).resolve().parent.parent
names = []
for p in sorted((root / "ReleasePath").glob("*.lean")):
    ns = []
    for line in p.read_text(encoding="utf-8").split("\n"):
        m = re.match(r"^namespace (\S+)", line)
        if m and m.group(1) != "ReleasePath":
            ns.append(m.group(1))
        elif re.match(r"^end (\S+)", line) and ns and line.split()[1] == ns[-1]:
            ns.pop()
        m = re.match(r"^(?:@\[[^\]]*\]\s*)?(?:theorem|lemma) (\S+)", line)
        if m:
            names.append(".".join(["ReleasePath"] + ns + [m.group(1)]))
out = ["import ReleasePath", ""] + [f"#print axioms {n}" for n in names]
(root / "audit" / "AuditAll.lean").write_text("\n".join(out) + "\n", encoding="utf-8")
print(len(names), "theorems")
