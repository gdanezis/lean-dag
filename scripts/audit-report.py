#!/usr/bin/env python3
"""Two mechanical checks on docs/report.md, per docs/style.md section 4.

  1. every section cross-reference names a section that exists;
  2. every backticked Lean identifier names a declaration that exists;
  3. every displayed theorem statement still matches its source signature;
  4. every displayed statement is a faithful abridgement of the source;
  5. the banned-phrase list of docs/style.md is absent, appendices included;
  6. every section reference in a source docstring names its document;
  7. every theorem the body displays has an Appendix A row.

Check 7 enforces the statement index's criterion — Appendix A indexes
what the narrative presents — and, since Appendix C admits everything
Appendix A names, keeps the reference appendices complete over the
narrative.

Check 6 exists because a bare `§4.2` in a docstring surfaces in the
generated appendices, where a reader takes it for a report section; twice
this session such a reference resolved to a report section by
coincidence, which check 1 cannot catch.

Check 4 is the strict one: the report's rendering, tokenised, must be a
subsequence of the declaration's own text. Dropping binders or clauses is
allowed -- the report elides for layout, marking it with a horizontal
ellipsis -- but reordering, rewording or inventing a hypothesis is not.
It needs docs/decls.json; run scripts/extract-decls.py first.

Check 3 catches the failure the first two cannot: a displayed statement
that has drifted from the declaration it claims to show. It compares the
declaration names appearing in the report's rendering of `theorem X`
against those in `X`'s actual signature, and reports any the source no
longer mentions.

The declaration list is read from docs/depgraph/deps.tsv, the extraction of
the compiled environment that also drives the support diagrams. Regenerate
it (see docs/depgraph/README.md) before trusting a failure from check 2.

    scripts/audit-report.py [report.md ...]

Exit status is 1 if anything failed, so it can gate a commit.
"""
import json
import re
import sys
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent

# A backticked token is treated as a Lean name only if it looks like one:
# a dotted or underscored identifier, not a file path and not English prose.
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_.'′]*$")
FILE_SUFFIX = re.compile(r"\.(lean|md|py|sh|tsv|svg|pdf|toml|yml|json)$")
# Words that are legitimately backticked in the report but are not declarations.
ALLOW = {
    "sorry", "decide", "omega", "simp", "rfl", "native_decide", "propext",
    "Classical.choice", "Quot.sound", "true", "false", "n", "f", "r", "k",
    # Lean core and Mathlib names the report mentions; the extraction keeps
    # only this development's declarations, so these cannot be checked here.
    "Environment.constants", "ConstantInfo.value", "Finset.card", "Fintype.card",
    "Finset.filter", "Finset.min", "Finset.max", "lt_trichotomy", "Correct.card", "Finset.max'", "Nat.succ", "refs.card",
    "LeanDagTest.Growth", "LeanDagTest.Unbounded", "Environment.constants",
    "le_antisymm", "not_lt", "List.finRange", "Finset.sort",
    # Names of the reference implementation (the `mysticeti` repository, Rust)
    # that the Mahi-Mahi arc's docstrings quote.
    "enough_leader_blame", "is_certificate", "try_indirect_decide",
    # Core Lean names the Barnacle statements name in comments.
    "Nat.one_pos",
    # The paper's threshold names and the core names the Hydrozoan
    # docstrings quote.
    "q_fast", "q_cert", "q_slow", "q_weak", "parents.card", "Nat.find",
    "t_plain", "t_equiv",
}


def sections(text):
    """Section numbers that exist, e.g. {'1', '1.1', '10.3', 'A'}."""
    found = set()
    for line in text.splitlines():
        m = re.match(r"^#{2,4}\s+(?:Appendix\s+([A-Z])|([0-9]+(?:\.[0-9]+)*))[.:]?\s", line)
        if m:
            found.add(m.group(1) or m.group(2))
    return found


def declarations(tsv):
    """Fully-qualified declaration names from the extraction."""
    names = set()
    for line in tsv.splitlines():
        parts = line.split("\t")
        if len(parts) >= 2 and parts[0] == "NODE":
            names.add(parts[1])
    return names


def resolves(name, decls, suffixes):
    """A report name resolves if it is a declaration or a suffix of one.

    The report also writes projections applied to a variable — `U.block` for
    `BlockUniverse.block`, `V.ids` for `View.ids` — so a dotted name whose
    tail resolves is accepted too.
    """
    if name in decls or name in suffixes:
        return True
    return "." in name and name.split(".")[-1] in suffixes


DECL_START = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)?"
                        r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+"
                        r"([A-Za-z_][A-Za-z0-9_.'\u2032]*)")


def source_declarations(root):
    """name -> full declaration text (statement and proof).

    The whole declaration rather than the signature alone: a signature
    cannot be delimited reliably, since named arguments such as
    `(Validator := Validator)` contain the token that would end it. The
    coarser text still catches a displayed statement naming something the
    declaration no longer mentions anywhere, which is the drift that
    matters.
    """
    decls = {}
    for f in (root / "LeanDag").rglob("*.lean"):
        lines = f.read_text().split("\n")
        starts = [i for i, l in enumerate(lines) if DECL_START.match(l)]
        for n, i in enumerate(starts):
            end = starts[n + 1] if n + 1 < len(starts) else len(lines)
            name = DECL_START.match(lines[i]).group(1)
            # Short names may repeat across namespaces (a protocol variant
            # lives in its own namespace, per the style guide), so keep the
            # text of every declaration of the name: a displayed statement
            # is checked against all of them, and drift means matching none.
            decls[name] = decls.get(name, "") + " " + " ".join(lines[i:end])
    return decls


def displayed_statements(text):
    """name -> displayed statement text, from the report's lean blocks."""
    out = {}
    for block in re.findall(r"^```lean\n(.*?)^```$", text, re.M | re.S):
        lines = block.split("\n")
        i = 0
        while i < len(lines):
            m = re.match(r"^(?:theorem|def|abbrev|structure|class)\s+"
                         r"([A-Za-z_][A-Za-z0-9_.'\u2032]*)", lines[i])
            if m:
                buf = []
                j = i
                while j < len(lines):
                    if j > i and re.match(r"^(?:theorem|def|abbrev|structure|class)\s",
                                          lines[j]):
                        break
                    buf.append(lines[j])
                    j += 1
                out.setdefault(m.group(1), " ".join(buf))
                i = j
                continue
            i += 1
    return out


TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_.'\u2032]*|[^\sA-Za-z0-9]")


def tokens(text):
    """Tokens for comparison.

    Line comments are dropped from both sides: the report annotates its
    displayed blocks (`-- as in ViewSync`) and the source carries field
    docstrings, and neither is part of the statement.
    """
    text = re.sub(r"--[^\n]*", " ", text)
    text = re.sub(r"/--.*?-/", " ", text, flags=re.S)
    return [t for t in TOKEN.findall(text) if t not in "\u2026"]


def subsequence_gap(shown, src):
    """First token of `shown` not matchable in order against `src`."""
    i = 0
    for t in shown:
        while i < len(src) and src[i] != t:
            i += 1
        if i == len(src):
            return t
        i += 1
    return None


def extracted_names(root):
    """Declaration and module names known to the source extraction.

    Wider than the compiled graph: it includes private lemmas, which the
    dependency extraction drops but docstrings still name.
    """
    path = root / "docs/decls.json"
    if not path.exists():
        return set()
    names = set()
    for d in json.loads(path.read_text()):
        names.add(d["name"])
        names.add(d["name"].rsplit(".", 1)[-1])
        names.add(d["module"])
        names.add(d["module"].removeprefix("LeanDag."))
    return names


# High-precision register violations only; docs/style.md carries the tables.
BANNED = re.compile(
    r"\b(load[- ]bearing|earns its keep|for free|buys|bought|at the price"
    r"|turned out|an earlier (?:draft|version)|worth recording|first draft"
    r"|the old (?:schedule|spacing|proof)|gets cheaper|is spent"
    # commercial metaphor extended to clauses, blocks and thresholds
    r"|pays? for itself|spends? the|charges? (?:a|the|it)|costs? nothing"
    r"|more cheaply|unaffordable|affordable"
    # figurative verbs and nouns
    r"|seen to bite|does not bite|vindication of|headline on data"
    r"|is its engine)\b", re.I)

# A docstring section reference is qualified when a document name or the
# word "report" sits within forty characters before or after it.
SECREF = re.compile(r"§§?\d")
QUALIFIER = re.compile(r"\.md`|report", re.I)


def load_extracted(root):
    path = root / "docs/decls.json"
    if not path.exists():
        return None
    out = {}
    for d in json.loads(path.read_text()):
        if d["module"].startswith("LeanDag."):
            out.setdefault(d["name"], []).append(d["statement"])
    return out


def unwrapped(text):
    """The text with soft line wraps collapsed to single spaces, paragraph
    breaks retained, and a parallel map giving each character's source line.

    Matching the register line by line misses a phrase a wrap splits, which
    is how "costs nothing" stood in `barnacle.md` while the check passed.
    Collapsing every run of whitespace instead would join the end of one
    paragraph to the start of the next and report a phrase neither
    contains, so a run holding a blank line becomes a newline rather than a
    space: `\\b` then keeps it out of any match.
    """
    out, lines = [], []
    line, run, run_line = 1, "", 1
    for ch in text:
        if ch.isspace():
            if not run:
                run_line = line
            run += ch
        else:
            if run and out:
                out.append("\n" if run.count("\n") > 1 else " ")
                lines.append(run_line)
            run = ""
            out.append(ch)
            lines.append(line)
        if ch == "\n":
            line += 1
    return "".join(out), lines


def banned_failures(text):
    """Every banned phrase in `text`, each named by the line it starts on."""
    flat, at = unwrapped(text)
    return [("banned", f"line {at[m.start()]}: `{m.group(0)}`")
            for m in BANNED.finditer(flat)]


def audit_register(path):
    """The banned-phrase check alone.

    Design records cite the report's sections and name declarations that
    may not exist yet, so the cross-reference and identifier checks do
    not apply to them. The register does: it is the one rule that holds
    of every document in `docs/`.
    """
    failures = banned_failures(path.read_text())
    for kind, detail in failures:
        print(f"{path.name}: {kind}: {detail}")
    return len(failures)


def audit(path, decls, suffixes):
    text = path.read_text()
    failures = []

    have = sections(text)
    for ref in sorted(set(re.findall(r"§([0-9]+(?:\.[0-9]+)*|[A-Z]\b)", text))):
        if ref not in have:
            # a bare "§10" is satisfied by the existence of section 10
            failures.append(("xref", ref))

    seen = set()
    for tok in re.findall(r"`([^`\n]+)`", text):
        tok = tok.strip()
        if tok in seen or tok in ALLOW:
            continue
        seen.add(tok)
        if not IDENT.match(tok):
            continue
        if FILE_SUFFIX.search(tok) or "/" in tok:
            continue
        if "_" not in tok and "." not in tok:
            continue  # a single English word, not a Lean name
        if not resolves(tok, decls, suffixes):
            failures.append(("ident", tok))

    # check 5: the banned phrases, over the whole document, matched across
    # soft line wraps (`unwrapped`)
    failures.extend(banned_failures(text))

    # check 6: docstring section references are qualified
    dpath = ROOT / "docs/decls.json"
    if dpath.exists():
        for d in json.loads(dpath.read_text()):
            if not d["module"].startswith("LeanDag."):
                continue
            doc = d["doc"]
            for m in SECREF.finditer(doc):
                window = doc[max(0, m.start() - 40):m.end() + 40]
                if not QUALIFIER.search(window):
                    failures.append(("secref",
                                     f"{d['name']} ({d['module'].removeprefix('LeanDag.')}): "
                                     f"…{doc[max(0, m.start() - 24):m.end() + 6]}…"))
                    break

    # check 7: body-displayed theorems are indexed in Appendix A
    if extracted_marker := "## Appendix A" in text:
        body_part = text[:text.index("## Appendix A")]
        appA = text[text.index("## Appendix A"):]
        gen = appA.find("<!-- BEGIN GENERATED")
        if gen >= 0:
            appA = appA[:gen]
        anames = set()
        for lean in re.findall(r"^\|[^|]+\|[^|]+\| (.+?) \|$", appA, re.M):
            anames.update(n.rsplit(".", 1)[-1] for n in
                          re.findall(r"`([A-Za-z][A-Za-z0-9_.'\u2032]*)`", lean))
        dpath2 = ROOT / "docs/decls.json"
        thm_names = set()
        if dpath2.exists():
            thm_names = {d["name"].rsplit(".", 1)[-1]
                         for d in json.loads(dpath2.read_text())
                         if d["module"].startswith("LeanDag.")
                         and d["kind"] in ("theorem", "lemma")}
        for block in re.findall(r"^```lean\n(.*?)^```$", body_part, re.M | re.S):
            for m in re.finditer(r"^theorem\s+([A-Za-z_][A-Za-z0-9_.'\u2032]*)",
                                 block, re.M):
                short = m.group(1).rsplit(".", 1)[-1]
                if short in thm_names and short not in anames:
                    failures.append(("unindexed",
                                     f"`{m.group(1)}` is displayed but has no "
                                     f"Appendix A row"))

    # check 3: displayed statements still match their source signatures
    sigs = source_declarations(ROOT)
    shown = displayed_statements(text)
    drifted = 0
    for name, disp in shown.items():
        src = sigs.get(name)
        if src is None:
            continue
        for tok in set(re.findall(r"[A-Za-z_][A-Za-z0-9_.'\u2032]*", disp)):
            if tok == name or tok in ALLOW:
                continue
            if not (tok in decls or tok in suffixes):
                continue          # not a declaration of this development
            if tok not in src:
                failures.append(("stale", f"{name} displays `{tok}`, absent from its signature"))
                drifted += 1

    # check 4: displayed statements are faithful abridgements
    extracted = load_extracted(ROOT)
    checked = 0
    if extracted is not None:
        for name, disp in shown.items():
            srcs = extracted.get(name)
            if not srcs:
                continue
            checked += 1
            # a short name may occur in several namespaces; any match passes
            gaps = [subsequence_gap(tokens(disp), tokens(src)) for src in srcs]
            if all(g is not None for g in gaps):
                failures.append(("verbatim",
                                 f"{name} displays `{gaps[0]}`, which the source "
                                 f"does not have at that point"))

    print(f"{path.relative_to(ROOT)}: {len(have)} sections, "
          f"{len(seen)} distinct backticked tokens, {len(shown)} displayed "
          f"statements ({checked} compared verbatim)")
    for kind, item in failures:
        label = {"xref": "unresolved section", "ident": "unknown declaration",
                 "stale": "stale displayed statement", "banned": "banned phrase",
                 "secref": "unqualified section reference",
                 "unindexed": "displayed theorem unindexed"}.get(kind, "not verbatim")
        print(f"  FAIL {label}: {item}")
    if not failures:
        print("  ok")
    return len(failures)


def main(argv):
    tsv = ROOT / "docs/depgraph/deps.tsv"
    if not tsv.exists():
        sys.exit(f"missing {tsv}; see docs/depgraph/README.md to regenerate")
    decls = declarations(tsv.read_text()) | extracted_names(ROOT)
    suffixes = {n.split(".", 1)[1] for n in decls if "." in n}
    for n in list(suffixes):
        while "." in n:
            n = n.split(".", 1)[1]
            suffixes.add(n)

    if argv[1:]:
        paths, register_only = [pathlib.Path(a) for a in argv[1:]], []
    else:
        paths = [ROOT / "docs/report.md"]
        # The register check covers every document in `docs/` except
        # `style.md`, which quotes the banned phrases in order to ban
        # them. A new design record is covered the moment it is added.
        register_only = sorted(
            q for q in (ROOT / "docs").glob("*.md")
            if q.name not in ("report.md", "style.md"))
    bad = sum(audit(p, decls, suffixes) for p in paths)
    bad += sum(audit_register(q) for q in register_only)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main(sys.argv)
