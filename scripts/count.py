#!/usr/bin/env python3
"""Size of each proof version: non-whitespace characters and Lean tokens.

A token is an identifier (dotted names count once), a number, or an operator/
punctuation symbol (multi-character ASCII operators like `:=` or `<;>` count once).
Comments are included, as in the character count. Tests and Core are excluded.
"""
import pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent / "BfTuringComplete"
OPS = [":=", "<;>", "++", "::", "=>", "->", "<-", "<|", "|>.", "|>", "..", "≠", "/-!", "/--", "-/", "--"]
TOKEN = re.compile(
    "|".join(re.escape(o) for o in sorted(OPS, key=len, reverse=True))
    + r"|[\w'₀-₉ᵢ!?]+(?:\.[\w'₀-₉!?]+)*|\S"
)

def files(d):
    return [f for f in sorted((ROOT / d).rglob("*.lean")) if "Test" not in f.name]

print(f"{'version':<11} {'chars':>8} {'tokens':>8}")
for d in ["Reference", "Golf", "Exposition", "Elegant", "Binary"]:
    if not (ROOT / d).is_dir():
        continue
    text = "".join(f.read_text() for f in files(d))
    chars = len(re.sub(r"\s", "", text))
    toks = len(TOKEN.findall(text))
    print(f"{d:<11} {chars:>8} {toks:>8}")
