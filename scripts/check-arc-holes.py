#!/usr/bin/env python3
"""Fail if a partitioned arc contains a proof hole or breaks its file discipline.

Scoped to the arcs of this repository under the model/proof partition —
Mahi-Mahi (`docs/mahi-mahi.md` §9), Black Marlin (`docs/black-marlin.md`
§7), FinWhale (`docs/finwhale.md` §15) and Barnacle
(`docs/barnacle.md` §10) — over both their source and
their witness directories. Three checks, after stripping comments so prose may use the
words:

  sorry / admit / axiom / native_decide / unsafe / partial
      are absent everywhere in the arc;
  Statement.lean files are proof-free  (no theorem/lemma/example/instance),
  Model/ files are theorem-free        (no theorem/lemma/example; instances
                                        by `inferInstanceAs` are allowed);
  View.full appears in no Statement.lean and no Model/ file
                                       (a liveness statement concludes on a
                                        view a validator can hold — issue #12;
                                        `full := ...` record fields and the
                                        `def View.full` site itself are
                                        vocabulary, not claims, and are exempt,
                                        as are the allowlisted files awaiting
                                        restatement).

Part of the trusted base: meant to be read once and believed. Keep it dumb.
"""

import re
import sys
from pathlib import Path

FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|native_decide|unsafe|partial)\b")
STATEMENT_FORBIDDEN = re.compile(r"^\s*(theorem|lemma|example|instance)\b")
MODEL_FORBIDDEN = re.compile(r"^\s*(theorem|lemma|example)\b")
FULLVIEW = re.compile(r"\bView\.full\b")
FULLVIEW_FIELD = re.compile(r"^\s*full\s*:=")
FULLVIEW_DEF = re.compile(r"^\s*def View\.full\b")
FULLVIEW_ALLOW = {
    "LeanDag/MahiMahi/Liveness/Statement.lean",    # MM3a-c await restatement (issue #12)
    "LeanDag/BlackMarlin/Liveness/Statement.lean",  # BML2 awaits restatement (issue #12)
}
ROOT = Path(__file__).resolve().parent.parent
ARCS = ["MahiMahi", "BlackMarlin", "FinWhale", "Barnacle", "Hydrozoan", "OptimalHydrozoan"]
SOURCES = [f"{top}/{arc}" for arc in ARCS for top in ("LeanDag", "LeanDagTest")]


def lean_files():
    for entry in SOURCES:
        path = ROOT / entry
        if path.is_dir():
            yield from sorted(path.rglob("*.lean"))


def strip_comments(lines):
    """Yield (lineno, code) with line comments and (nesting) block comments removed."""
    depth = 0
    for lineno, line in enumerate(lines, start=1):
        code = []
        i = 0
        while i < len(line):
            if depth == 0 and line.startswith("--", i):
                break
            if line.startswith("/-", i):
                depth += 1
                i += 2
            elif depth > 0 and line.startswith("-/", i):
                depth -= 1
                i += 2
            elif depth == 0:
                code.append(line[i])
                i += 1
            else:
                i += 1
        yield lineno, "".join(code)


def main():
    holes = []
    for path in lean_files():
        rel = path.relative_to(ROOT)
        in_model = "Model" in path.parent.parts
        for lineno, code in strip_comments(path.read_text(encoding="utf-8").splitlines()):
            match = FORBIDDEN.search(code)
            if match:
                holes.append(f"{rel}:{lineno}: {match.group(0)}")
            if path.name == "Statement.lean":
                match = STATEMENT_FORBIDDEN.search(code)
                if match:
                    holes.append(f"{rel}:{lineno}: {match.group(1)} (proof material in a Statement file)")
            elif in_model and str(rel).startswith("LeanDag/"):
                match = MODEL_FORBIDDEN.search(code)
                if match:
                    holes.append(f"{rel}:{lineno}: {match.group(1)} (theorem material in a Model file)")
            if (path.name == "Statement.lean" or (in_model and str(rel).startswith("LeanDag/"))) \
                    and str(rel) not in FULLVIEW_ALLOW \
                    and FULLVIEW.search(code) and not FULLVIEW_FIELD.search(code) \
                    and not FULLVIEW_DEF.search(code):
                holes.append(f"{rel}:{lineno}: View.full (a liveness statement concludes on a view)")
    if holes:
        print("Partitioned-arc discipline violations:")
        for hole in holes:
            print(f"  {hole}")
        return 1
    print(f"Partitioned arcs ({', '.join(ARCS)}): no holes, discipline intact.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
