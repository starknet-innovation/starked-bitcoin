#!/usr/bin/env python3
"""Witness-uniqueness checks for starked-air-v1 AIRs with Z3 (roadmap FV-Z3).

Question asked, per preset: for any two assignments of the *witness cells* that satisfy every
constraint instantiated at the *anchor rows*, and that agree on all *input cells*, do they
agree on the *output cells*?  `unsat` = yes (outputs are determined by inputs).

This is an independent cross-check of the Lean soundness proofs: it reads the exported JSON
directly and does not trust the Lean semantics or proofs. A green result is about the chosen
window only; constraints at other rows are not included (their cells are inputs).

Encoding (a reviewer must agree with these):
1. Every cell is an integer in [0, p), p = 2^31 - 1. Constraints are exact integer
   polynomials discharged as `poly = p * k`, `k` a fresh integer bounded by interval analysis.
   No `mod`/`div` terms.
2. Bit columns (0..95, 108..123) are restricted to {0, 1} at every row. This is justified:
   the AIR's booleanity constraints hold on every row.
3. Preprocessed columns are evaluated concretely at the chosen rows (n = 2^log_size).
4. Public inputs are shared input variables in [0, p).
5. Cells outside the witness rows, and cells listed as inputs, are shared between the two
   copies; all other cells are per-copy witnesses.
6. Only the cone of influence of the outputs is kept: a constraint instance is included iff it
   is connected to an output cell through shared per-copy witness cells. The others mention
   only inputs or unrelated witnesses, and dropping them only adds models (see 7).
7. Presets may DROP constraints (e.g. SHA's unconditional per-row Σ/σ/Ch/Maj limb definitions,
   columns 96..107, which do not bear on the property). Dropping constraints only adds models,
   so `unsat` (unique) stays valid; `sat` may then be spurious and must be inspected.
With `--bv`, cells and constraints use 160-bit two's-complement bit-vectors instead of
integers; every constraint's interval bound is checked to be below 2^150, so no wrap-around
occurs and equality is exact. Products with a 0/1 operand are encoded as multiplexers.
8. Presets may ASSUME facts about cells (e.g. "this row is a retarget boundary"); the result
   then holds under that assumption only, which the preset documents.

Usage:
    .venv-fv/bin/python scripts/air_z3.py list
    .venv-fv/bin/python scripts/air_z3.py check <preset> [--timeout-ms N]
    .venv-fv/bin/python scripts/air_z3.py all [--timeout-ms N]
Exit code 0 iff every requested check is `unsat`.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

import z3
from z3 import z3util

P = 2**31 - 1
ROOT = Path(__file__).resolve().parent.parent
A, E, W, CA_LO = 0, 32, 64, 108


def is_bit_col(i: int) -> bool:
    return i < 96 or 108 <= i < 124


def precol(pc: dict, r: int, n: int) -> int:
    (kind, arg), = pc.items()
    if kind == "is_first":
        return 1 if r == 0 else 0
    if kind == "not_last":
        return 0 if r == n - 1 else 1
    if kind == "periodic":
        return arg[r % len(arg)] % P
    if kind == "row_lt":
        return 1 if r < arg else 0
    if kind == "row_ge_end":
        return 1 if r + arg >= n else 0
    raise ValueError(kind)


class Instance:
    """Constraints of an AIR instantiated at anchor rows, for two witness copies."""

    BV = 160

    def __init__(self, air: dict, log_size: int, witness_rows: set[int], input_cells: set[tuple[int, int]],
                 bv: bool = False):
        self.air, self.n, self.bv = air, 1 << log_size, bv
        self.witness_rows, self.input_cells = witness_rows, input_cells
        self.vars: dict[str, z3.ArithRef] = {}
        self.bounds: dict[str, tuple[int, int]] = {}
        self.facts: list[z3.BoolRef] = []

    def cell(self, idx: int, row: int, copy: int):
        shared = row not in self.witness_rows or (idx, row) in self.input_cells
        name = f"x_{idx}_{row}" if shared else f"x{copy}_{idx}_{row}"
        if name not in self.vars:
            hi = 1 if is_bit_col(idx) else P - 1
            if self.bv:
                v = z3.BitVec(name, self.BV)
                self.facts.append(z3.ULE(v, hi))
            else:
                v = z3.Int(name)
                self.facts.append(z3.And(v >= 0, v <= hi))
            self.vars[name] = v
            self.bounds[name] = (0, hi)
        return self.vars[name], self.bounds[name]

    def pub(self, i: int):
        name = f"pub_{i}"
        if name not in self.vars:
            if self.bv:
                v = z3.BitVec(name, self.BV)
                self.facts.append(z3.ULT(v, P))
            else:
                v = z3.Int(name)
                self.facts.append(z3.And(v >= 0, v < P))
            self.vars[name], self.bounds[name] = v, (0, P - 1)
        return self.vars[name], self.bounds[name]

    def build(self, node: int, r: int, copy: int, memo: dict):
        """Returns (value, (lo, hi)) where value is an int (constant) or a z3 term."""
        key = (node, r)
        if key in memo:
            return memo[key]
        e = self.air["exprs"][node]
        (op, arg), = e.items()
        if op == "constant":
            out = (arg % P, (arg % P, arg % P))
        elif op == "pub":
            out = self.pub(arg)
        elif op == "col":
            row = (r + arg["offset"]) % self.n
            if arg["tree"] == "preprocessed":
                v = precol(self.air["preprocessed"][arg["index"]], row, self.n)
                out = (v, (v, v))
            else:
                out = self.cell(arg["index"], row, copy)
        elif op == "neg":
            v, (lo, hi) = self.build(arg, r, copy, memo)
            out = (-v if isinstance(v, int) else -v, (-hi, -lo))
        else:
            (a, (alo, ahi)), (b, (blo, bhi)) = (self.build(x, r, copy, memo) for x in arg)
            if op == "add":
                val = a + b if not (isinstance(a, int) and a == 0) else b
                if isinstance(b, int) and b == 0:
                    val = a
                out = (val, (alo + blo, ahi + bhi))
            elif op == "sub":
                val = a - b if not (isinstance(b, int) and b == 0) else a
                out = (val, (alo - bhi, ahi - blo))
            elif op == "mul":
                if (isinstance(a, int) and a == 0) or (isinstance(b, int) and b == 0):
                    out = (0, (0, 0))
                elif isinstance(a, int) and a == 1:
                    out = (b, (blo, bhi))
                elif isinstance(b, int) and b == 1:
                    out = (a, (alo, ahi))
                else:
                    ps = [alo * blo, alo * bhi, ahi * blo, ahi * bhi]
                    if self.bv and (alo, ahi) == (0, 1) and not isinstance(a, int):
                        prod = z3.If(a == 1, self.lift(b), z3.BitVecVal(0, self.BV))
                    elif self.bv and (blo, bhi) == (0, 1) and not isinstance(b, int):
                        prod = z3.If(b == 1, self.lift(a), z3.BitVecVal(0, self.BV))
                    elif self.bv and isinstance(a, int):
                        prod = z3.BitVecVal(a, self.BV) * b
                    else:
                        prod = a * b
                    out = (prod, (min(ps), max(ps)))
            else:
                raise ValueError(op)
        memo[key] = out
        return out

    def lift(self, v):
        return z3.BitVecVal(v, self.BV) if (self.bv and isinstance(v, int)) else v

    def mentions(self, node: int, cols: range, memo: dict) -> bool:
        if node in memo:
            return memo[node]
        (op, arg), = self.air["exprs"][node].items()
        if op == "col":
            out = arg["tree"] == "main" and arg["index"] in cols
        elif op in ("add", "sub", "mul"):
            out = self.mentions(arg[0], cols, memo) or self.mentions(arg[1], cols, memo)
        elif op == "neg":
            out = self.mentions(arg, cols, memo)
        else:
            out = False
        memo[node] = out
        return out

    def instances(self, anchors: list[int], copy: int, drop_derived: bool) -> list:
        """(constraint, row, term, lo, hi) for every constraint not identically zero at the anchors."""
        out = []
        dmemo: dict = {}
        for r in anchors:
            memo: dict = {}
            for c in self.air["constraints"]:
                if drop_derived and self.mentions(c, range(96, 108), dmemo):
                    continue
                v, (lo, hi) = self.build(c, r, copy, memo)
                if isinstance(v, int):
                    if v % P != 0:
                        raise RuntimeError(f"constant constraint violated at row {r}")
                    continue
                out.append((c, r, v, lo, hi))
        return out

    def add(self, insts: list, copy: int) -> None:
        for c, r, v, lo, hi in insts:
            if self.bv:
                if max(abs(lo), abs(hi)) >= 2 ** (self.BV - 4):
                    raise RuntimeError(f"constraint {c} at row {r} exceeds the bit-vector width")
                k = z3.BitVec(f"k{copy}_{r}_{c}", self.BV)
                self.facts += [v == k * P, k >= lo // P, k <= -((-hi) // P)]  # signed compares
            else:
                k = z3.Int(f"k{copy}_{r}_{c}")
                self.facts += [v == P * k, k >= lo // P, k <= -((-hi) // P)]


PRESETS = {}


def preset(name: str, doc: str):
    def deco(f):
        PRESETS[name] = (doc, f)
        return f
    return deco


HB = 256  # header 1 (rows 256..511): no wrap-around, not the first or last header at log_size 16


@preset("mtp-slot", "MTP comparison flag b_i is determined by the window time T_i and own time t (row 229)")
def _mtp():
    r = HB + 229
    inputs = {(A + k, r) for k in range(32)} | {(W + k, r) for k in range(32)}
    return dict(anchors=[r], wrows={r}, inputs=inputs, outputs=[(CA_LO, r)], drop_derived=True)


@preset("state-flag", "Boundary flag, rem and q are determined by the height (rows 218-219)")
def _state():
    r = HB + 218
    inputs = {(A + k, r) for k in range(32)}
    outs = [(W, r)] + [(W + 1 + k, r) for k in range(11)] + [(A + k, r + 1) for k in range(20)]
    return dict(anchors=[r], wrows={r, r + 1}, inputs=inputs, outputs=outs, drop_derived=True)


@preset("rt-clamp", "At a retarget boundary (assumes rt = 1), the clamp flags and span are determined by the "
        "predecessor's time and pst (row 221)")
def _rt():
    r = HB + 221
    outs = [(W + 2, r), (W + 3, r), (W + 4, r)] + [(E + k, r) for k in range(23)]
    return dict(anchors=[r], wrows={r, r + 1}, inputs=set(), outputs=outs, drop_derived=True,
                assume=[(W + 0, r, 1)])


@preset("sha-round", "A SHA-256 round's new a and e are determined by the previous state and message word (row 10)")
def _sha():
    r = HB + 10
    inputs = {(W + k, r) for k in range(32)}
    outs = [(A + k, r) for k in range(32)] + [(E + k, r) for k in range(32)]
    return dict(anchors=[r], wrows={r}, inputs=inputs, outputs=outs, drop_derived=False)


@preset("pow-onehot", "The PoW exponent one-hot is determined by the header's nBits (row 216)")
def _pow():
    r = HB + 216
    return dict(anchors=[r], wrows={r, r + 1}, inputs=set(), outputs=[(A + k, r) for k in range(27)], drop_derived=True)


@preset("control-free", "CONTROL (must be NOT UNIQUE): carry column 110 at row 229 is unconstrained there")
def _control():
    r = HB + 229
    inputs = {(A + k, r) for k in range(32)} | {(W + k, r) for k in range(32)}
    return dict(anchors=[r], wrows={r}, inputs=inputs, outputs=[(CA_LO + 2, r)], drop_derived=True, expect="sat")


def run(name: str, air: dict, timeout_ms: int, bv: bool = False) -> str:
    ps = PRESETS[name][1]()
    outputs = ps["outputs"]
    # Pass 1 (integers): bounds and the cone of influence.
    probe = Instance(air, 16, ps["wrows"], ps["inputs"], False)
    allinst = probe.instances(ps["anchors"], 0, ps["drop_derived"])
    witness = lambda t: {str(x) for x in z3util.get_vars(t) if str(x).startswith("x0_")}
    cells = [witness(t) for (_, _, t, _, _) in allinst]
    cone = {f"x0_{i}_{r}" for i, r in outputs}
    keep: set[int] = set()
    grew = True
    while grew:
        grew = False
        for n_, cs in enumerate(cells):
            if n_ not in keep and cs & cone:
                keep.add(n_)
                cone |= cs
                grew = True
    chosen = {(allinst[n_][0], allinst[n_][1]) for n_ in keep}
    width = max([abs(lo) for (_, _, _, lo, _) in allinst] + [abs(hi) for (_, _, _, _, hi) in allinst] + [P]).bit_length()
    # Pass 2: the query.
    inst = Instance(air, 16, ps["wrows"], ps["inputs"], bv)
    inst.BV = width + 8
    for cp in (0, 1):
        sel = [x for x in inst.instances(ps["anchors"], cp, ps["drop_derived"]) if (x[0], x[1]) in chosen]
        inst.add(sel, cp)
    n0 = len(chosen)
    for idx, row, val in ps.get("assume", []):
        for cp in (0, 1):
            inst.facts.append(inst.cell(idx, row, cp)[0] == val)
    diff = []
    for idx, row in outputs:
        a, _ = inst.cell(idx, row, 0)
        b, _ = inst.cell(idx, row, 1)
        diff.append(a != b)
    s = z3.Solver()
    s.set("timeout", timeout_ms)
    s.add(*inst.facts)
    s.add(z3.Or(*diff))
    t0 = time.time()
    res = s.check()
    dt = time.time() - t0
    verdict = {"unsat": "UNIQUE (unsat)", "sat": "NOT UNIQUE (sat)"}.get(str(res), "UNKNOWN")
    print(f"{name:12s} {verdict:18s} constraints/copy={n0:4d} vars={len(inst.vars):5d} time={dt:6.1f}s  -- {PRESETS[name][0]}")
    if res == z3.sat:
        m = s.model()
        for idx, row in outputs:
            a, _ = inst.cell(idx, row, 0)
            b, _ = inst.cell(idx, row, 1)
            if m.eval(a, model_completion=True).as_long() != m.eval(b, model_completion=True).as_long():
                print(f"    differs: col {idx} row {row}: {m.eval(a)} vs {m.eval(b)}")
    return verdict


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("cmd", choices=["list", "check", "all"])
    ap.add_argument("preset", nargs="?")
    ap.add_argument("--air", default=str(ROOT / "airs" / "header_chain.json"))
    ap.add_argument("--timeout-ms", type=int, default=600_000)
    ap.add_argument("--bv", action="store_true", help="bit-vector encoding (see the docstring)")
    a = ap.parse_args()
    if a.cmd == "list":
        for k, (doc, _) in PRESETS.items():
            print(f"{k:12s} {doc}")
        return 0
    air = json.loads(Path(a.air).read_text())
    names = list(PRESETS) if a.cmd == "all" else [a.preset]
    ok = True
    for nm in names:
        v = run(nm, air, a.timeout_ms, a.bv)
        expect = PRESETS[nm][1]().get("expect", "unsat")
        ok &= v.startswith("UNIQUE") if expect == "unsat" else v.startswith("NOT UNIQUE")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
