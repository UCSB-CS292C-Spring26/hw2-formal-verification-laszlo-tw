"""
CS292C Homework 2 — Problem 2: Hoare Logic VCG for IMP (30 points)
===================================================================
Implement weakest-precondition-based verification condition generation
for a simple IMP language, using Z3 to discharge the VCs.

Part (a): Compute wp using your VCG and analyze preconditions with Z3.
          NOTE: Part (a) depends on Part (b). Implement Part (b) first, then come back to Part (a).
Part (b): Implement wp() and verify() below.
Part (c): Discover loop invariants for three programs.
Part (d): Find and fix a bug in a provided invariant.
"""

from z3 import *
from dataclasses import dataclass
from typing import Union

# ============================================================================
# IMP Abstract Syntax Tree
# ============================================================================

@dataclass
class IntConst:
    value: int

@dataclass
class Var:
    name: str

@dataclass
class BinOp:
    """op ∈ {'+', '-', '*'}"""
    op: str
    left: 'AExp'
    right: 'AExp'

AExp = Union[IntConst, Var, BinOp]

@dataclass
class BoolConst:
    value: bool

@dataclass
class Compare:
    """op ∈ {'<', '<=', '>', '>=', '==', '!='}"""
    op: str
    left: AExp
    right: AExp

@dataclass
class ImpNot:
    expr: 'BExp'

@dataclass
class ImpAnd:
    left: 'BExp'
    right: 'BExp'

@dataclass
class ImpOr:
    left: 'BExp'
    right: 'BExp'

BExp = Union[BoolConst, Compare, ImpNot, ImpAnd, ImpOr]

@dataclass
class Assign:
    var: str
    expr: AExp

@dataclass
class Seq:
    s1: 'Stmt'
    s2: 'Stmt'

@dataclass
class If:
    cond: BExp
    then_branch: 'Stmt'
    else_branch: 'Stmt'

@dataclass
class While:
    cond: BExp
    invariant: 'BExp'
    body: 'Stmt'

@dataclass
class Assert:
    cond: BExp

@dataclass
class Assume:
    cond: BExp

Stmt = Union[Assign, Seq, If, While, Assert, Assume]

# ============================================================================
# IMP AST → Z3 Translation
# ============================================================================

_z3_vars: dict[str, ArithRef] = {}

def z3_var(name: str) -> ArithRef:
    if name not in _z3_vars:
        _z3_vars[name] = Int(name)
    return _z3_vars[name]

def aexp_to_z3(e: AExp) -> ArithRef:
    match e:
        case IntConst(v):   return IntVal(v)
        case Var(name):     return z3_var(name)
        case BinOp('+', l, r): return aexp_to_z3(l) + aexp_to_z3(r)
        case BinOp('-', l, r): return aexp_to_z3(l) - aexp_to_z3(r)
        case BinOp('*', l, r): return aexp_to_z3(l) * aexp_to_z3(r)
        case _: raise ValueError(f"Unknown AExp: {e}")

def bexp_to_z3(e: BExp) -> BoolRef:
    match e:
        case BoolConst(v):   return BoolVal(v)
        case Compare(op, l, r):
            lz, rz = aexp_to_z3(l), aexp_to_z3(r)
            return {'<': lz < rz, '<=': lz <= rz, '>': lz > rz,
                    '>=': lz >= rz, '==': lz == rz, '!=': lz != rz}[op]
        case ImpNot(inner):  return z3.Not(bexp_to_z3(inner))
        case ImpAnd(l, r):   return z3.And(bexp_to_z3(l), bexp_to_z3(r))
        case ImpOr(l, r):    return z3.Or(bexp_to_z3(l), bexp_to_z3(r))
        case _: raise ValueError(f"Unknown BExp: {e}")

def z3_substitute_var(formula: ExprRef, var_name: str, replacement: ArithRef) -> ExprRef:
    """Replace every occurrence of z3 variable `var_name` with `replacement`."""
    return substitute(formula, (z3_var(var_name), replacement))


# ============================================================================
# Part (b): Weakest Precondition + VCG — 12 pts
# ============================================================================

side_vcs: list[tuple[str, BoolRef]] = []

def wp(stmt: Stmt, Q: BoolRef) -> BoolRef:
    """
    Compute the weakest precondition of `stmt` w.r.t. postcondition `Q`.
    For while loops, append side VCs to the global `side_vcs` list.

    Implement all six cases.
    """
    global side_vcs

    match stmt:
        case Assign(var, expr):
            # Q[var ↦ expr]
            return z3_substitute_var(Q, var, aexp_to_z3(expr))

        case Seq(s1, s2):
            # wp(s1; s2, Q) = wp(s1, wp(s2, Q))
            return wp(s1, wp(s2, Q))

        case If(cond, s1, s2):
            # wp(if b then s1 else s2, Q) = (b ⇒ wp(s1, Q)) ⋀ (b ⇒ wp(s2, Q))
            b = bexp_to_z3(cond)
            return And(Implies(b, wp(s1, Q)), Implies(Not(b), wp(s2, Q)))

        case While(cond, inv, body):
            # Return I. Generate two side VCs:
            #   preservation: I ∧ b → wp(body, I)
            #   postcondition: I ∧ ¬b → Q

            # for some reason initial VC is handled in verify and not here 
            # (step 3. check pre -> wp is valid)

            b = bexp_to_z3(cond)
            I = bexp_to_z3(inv)

            # preservation VC
            preservation = Implies(And(I, b), wp(body, I))
            side_vcs.append(("Preservation", preservation))

            # postcondition VC
            postcondition = Implies(And(I, Not(b)), Q)
            side_vcs.append(("Postcondition", postcondition))

            return I

        case Assert(cond):
            # wp(assert cond, Q) = cond ∧ Q
            return And(bexp_to_z3(cond), Q)

        case Assume(cond):
            # wp(assume cond, Q) = cond → Q
            return Implies(bexp_to_z3(cond), Q)

        case _:
            raise ValueError(f"Unknown statement: {stmt}")


def verify(pre: BExp, stmt: Stmt, post: BExp, label: str = "Program"):
    """
    Verify the Hoare triple {pre} stmt {post}.
    1. Clear side_vcs.  2. Compute wp.  3. Check pre → wp is valid.
    4. Check each side VC.  5. Print results.

    Implement this function.
    """
    # 1. clear side_vcs
    global side_vcs
    side_vcs = []

    pre_z3 = bexp_to_z3(pre)
    post_z3 = bexp_to_z3(post)

    print(f"=== {label} ===")

    # 2. compute wp
    wp_result = wp(stmt, post_z3)   # also populates side_vcs for any while loops encountered

    all_vcs_pass = True

    # 3. check pre -> wp is valid
    s = Solver()
    s.add(Not(Implies(pre_z3, wp_result)))
    result = s.check()
    if result == unsat:
        print("pre -> wp is valid")
    else:
        print(f"pre -> wp is not valid. counterexample: {s.model()}")
        all_vcs_pass = False

    # 4. check each side vc
    for (vc_name, vc_formula) in side_vcs:
        s2 = Solver()
        s2.add(Not(vc_formula))
        result = s2.check()
        if result == unsat:
            print(f"side vc \"{vc_name}\" is valid")
        else:
            print(f"side vc \"{vc_name}\" is not valid. counterexample: {s2.model()}")
            all_vcs_pass = False

    # 5. print results
    if all_vcs_pass:
        print(f"Verified: {label}")
    else:
        print(f"Failed: {label}")

    # print(f"=== {label} ===")
    print()


# ============================================================================
# Test Programs for Part (b) — verify your VCG works on these
# ============================================================================

def test_swap():
    """{ x == a ∧ y == b }  t:=x; x:=y; y:=t  { x == b ∧ y == a }"""
    pre = ImpAnd(Compare('==', Var('x'), Var('a')),
                 Compare('==', Var('y'), Var('b')))
    stmt = Seq(Assign('t', Var('x')),
               Seq(Assign('x', Var('y')), Assign('y', Var('t'))))
    post = ImpAnd(Compare('==', Var('x'), Var('b')),
                  Compare('==', Var('y'), Var('a')))
    verify(pre, stmt, post, "Swap")


def test_abs():
    """{ true }  if x<0 then r:=0-x else r:=x  { r >= 0 ∧ (r==x ∨ r==0-x) }"""
    pre = BoolConst(True)
    stmt = If(Compare('<', Var('x'), IntConst(0)),
              Assign('r', BinOp('-', IntConst(0), Var('x'))),
              Assign('r', Var('x')))
    post = ImpAnd(Compare('>=', Var('r'), IntConst(0)),
                  ImpOr(Compare('==', Var('r'), Var('x')),
                        Compare('==', Var('r'), BinOp('-', IntConst(0), Var('x')))))
    verify(pre, stmt, post, "Absolute Value")


# ============================================================================
# Part (c): Invariant Discovery — 8 pts
#
# For each program below, replace the `???` invariant with a correct one.
# [EXPLAIN] in a comment how you found each invariant and why it works.
# ============================================================================

def test_mult():
    """
    Program C1 — Multiplication by addition:
      { a >= 0 }
      i := 0; r := 0;
      while i < a  invariant ???  do
        r := r + b;  i := i + 1;
      { r == a * b }

    Replace the invariant below with a correct one.
    """
    # [EXPLAIN]: i <= a is a counter that ensures that loop index i stays within bounds
    # and r = i*b is an accumulator that captures the relationship between r, i, and b 
    # maintained through each iteration: after i iterations, r is b added i times.
    # init: when the loop starts, a >= 0, i = 0, and r = 0, and so it holds that i <= a and r = i*b
    # preservation: if i < a and i <= a and r = i*b at the beginning of an iteration, 
    #   then after the loop body, i <= a and r = i*b still hold
    # exit: if i >= a and i <= a and r = i*b when the loop exits, then r = a*b holds which is Q
    pre = Compare('>=', Var('a'), IntConst(0))
    inv = ImpAnd(Compare('<=', Var('i'), Var('a')), 
                 Compare('==', Var('r'), BinOp('*', Var('i'), Var('b'))))
    body = Seq(Assign('r', BinOp('+', Var('r'), Var('b'))),
               Assign('i', BinOp('+', Var('i'), IntConst(1))))
    stmt = Seq(Assign('i', IntConst(0)),
               Seq(Assign('r', IntConst(0)),
                   While(Compare('<', Var('i'), Var('a')), inv, body)))
    post = Compare('==', Var('r'), BinOp('*', Var('a'), Var('b')))
    verify(pre, stmt, post, "C1: Multiplication by Addition")

def test_add():
    """
    Program C2 — Addition by loop:
      { n >= 0 ∧ m >= 0 }
      i := 0; r := n;
      while i < m  invariant ???  do
        r := r + 1;  i := i + 1;
      { r == n + m }

    Replace the invariant below with a correct one.
    """
    # [EXPLAIN]: i <= m is a counter that ensures that loop index i stays within bounds
    # and r = n + i is an accumulator that captures the relationship between r, n, and i
    # maintained through each iteration: r starts at n and has been incremented i times after i iterations
    # init: when the loop starts, n >= 0, m >= 0, i = 0, and r = n, so it holds that i <= m and r = n + i
    # preservation: if i < m and i <= m and r = n + i at the beginning of an iteration,
    #   then after the loop body, i <= m and r = n + i still hold
    # exit: if i >= m and i <= m and r = n + i when the loop exits, then r = n + m holds which is Q
    pre = ImpAnd(Compare('>=', Var('n'), IntConst(0)),
                 Compare('>=', Var('m'), IntConst(0)))
    inv = ImpAnd(Compare('<=', Var('i'), Var('m')),
                 Compare('==', Var('r'), BinOp('+', Var('n'), Var('i'))))
    body = Seq(Assign('r', BinOp('+', Var('r'), IntConst(1))),
               Assign('i', BinOp('+', Var('i'), IntConst(1))))
    stmt = Seq(Assign('i', IntConst(0)),
               Seq(Assign('r', Var('n')),
                   While(Compare('<', Var('i'), Var('m')), inv, body)))
    post = Compare('==', Var('r'), BinOp('+', Var('n'), Var('m')))
    verify(pre, stmt, post, "C2: Addition by Loop")


def test_sum():
    """
    Program C3 — Sum of 1..n:
      { n >= 1 }
      i := 1; s := 0;
      while i <= n  invariant ???  do
        s := s + i;  i := i + 1;
      { 2 * s == n * (n + 1) }

    Replace the invariant below with a correct one.
    """
    # [EXPLAIN]: this was covered in lecture
    # i <= n + 1 is a counter that ensures that loop index i stays within bounds
    # and s = i*(i-1)/2 is an accumulator that captures the relationship between s and i
    # maintained through each iteration: at iteration i, s holds the sum 1 + 2 + ... + (i-1),
    # which is equal to i*(i-1)/2. However this is more easily represented as s*2 = i*(i-1) (similar to Q)
    # init: when the loop starts, n >= 1, i = 1, and s = 0, so it holds that i <= n + 1 and s = i*(i-1)/2
    # preservation: if i <= n and i <= n + 1 and s = i*(i-1)/2 at the beginning of an iteration,
    #   then after the loop body, i <= n + 1 and s = i*(i-1)/2 still hold
    # exit: if i > n and i <= n + 1 and s = i*(i-1)/2 when the loop exits, then 2 * s == n * (n + 1) holds which is Q
    pre = Compare('>=', Var('n'), IntConst(1))
    inv = ImpAnd(Compare('<=', Var('i'), BinOp('+', Var('n'), IntConst(1))),
                 Compare('==', BinOp('*', Var('s'), IntConst(2)), BinOp('*', Var('i'), BinOp('-', Var('i'), IntConst(1)))))
    body = Seq(Assign('s', BinOp('+', Var('s'), Var('i'))),
               Assign('i', BinOp('+', Var('i'), IntConst(1))))
    stmt = Seq(Assign('i', IntConst(1)),
               Seq(Assign('s', IntConst(0)),
                   While(Compare('<=', Var('i'), Var('n')), inv, body)))
    post = Compare('==', BinOp('*', IntConst(2), Var('s')),
                   BinOp('*', Var('n'), BinOp('+', Var('n'), IntConst(1))))
    verify(pre, stmt, post, "C3: Sum of 1..n")


# ============================================================================
# Part (d): Find the Bug — 4 pts
#
# The invariant below is WRONG (too weak). Your VCG should report failure.
# 1. Run it — which side VC fails?
# 2. [EXPLAIN] Give a concrete state where the invariant holds but the
#    postcondition does not.
# 3. Fix the invariant and re-verify.
# ============================================================================

def test_buggy_div():
    """
    Integer division with a BUGGY invariant.
      { x >= 0 ∧ y > 0 }
      q := 0; r := x;
      while r >= y  invariant (q * y + r == x)  do    ← TOO WEAK!
        r := r - y;  q := q + 1;
      { q * y + r == x ∧ 0 <= r ∧ r < y }

    The invariant q * y + r == x is correct but INCOMPLETE.
    It is missing a crucial conjunct. Find it.
    """
    pre = ImpAnd(Compare('>=', Var('x'), IntConst(0)),
                 Compare('>', Var('y'), IntConst(0)))

    # BUGGY invariant — intentionally too weak
    inv_buggy = Compare('==',
        BinOp('+', BinOp('*', Var('q'), Var('y')), Var('r')),
        Var('x'))

    body = Seq(Assign('r', BinOp('-', Var('r'), Var('y'))),
               Assign('q', BinOp('+', Var('q'), IntConst(1))))
    stmt = Seq(Assign('q', IntConst(0)),
               Seq(Assign('r', Var('x')),
                   While(Compare('>=', Var('r'), Var('y')),
                         inv_buggy, body)))
    post = ImpAnd(Compare('==',
                       BinOp('+', BinOp('*', Var('q'), Var('y')), Var('r')),
                       Var('x')),
                  ImpAnd(Compare('>=', Var('r'), IntConst(0)),
                         Compare('<', Var('r'), Var('y'))))

    verify(pre, stmt, post, "Buggy Division (should FAIL)")

    # [EXPLAIN]: Running the integer division with the buggy invariant, I got:
    # side vc "Postcondition" is not valid. counterexample: [x = -6, y = -4, r = -6, q = 0]
    # meaning that the postcondition VC failed. The counterexample identified shows 
    # a concrete state where q*y + r = x and r < y hold, but 0 <= r doesn't,
    # so the postcondition is not implied at loop exit. The counterexample hints that
    # the invariant should ensure that r should not be negative, so we add r >= 0 to address this.
    inv_fixed = ImpAnd(
        Compare('==', BinOp('+', BinOp('*', Var('q'), Var('y')), Var('r')), Var('x')),
        Compare('>=', Var('r'), IntConst(0))
    )
    stmt = Seq(Assign('q', IntConst(0)),
               Seq(Assign('r', Var('x')),
                   While(Compare('>=', Var('r'), Var('y')),
                         inv_fixed, body)))
    verify(pre, stmt, post, "FIXED: Verified")


# ============================================================================
# Part (a): WP Derivation via Z3 — 6 pts
#
# Build the following program as an IMP AST:
#   x := x + 1;
#   if x > 0 then y := x * 2 else y := 0 - x;
# Postcondition: { y > 0 }
#
# 1. Call wp() to get the weakest precondition. Print the Z3 formula.
# 2. Use Z3 to check whether each of the following is a valid precondition:
#    - { x >= 0 }
#    - { x >= -1 }
#    - { x == -1 }
#    For each, print whether it's valid and add a comment explaining why.
# ============================================================================

def test_wp_derivation():
    """
    Part (a): Use your VCG to compute wp, then check candidate preconditions.
    Implement after you finish Part (b).
    """
    print("=== Part (a): WP Derivation ===")

    # Build the IMP AST for the program above
    # stmt = Seq(Assign('x', ...), If(...))
    # post = Compare('>', Var('y'), IntConst(0))
    
    #   x := x + 1;
    #   if x > 0 then y := x * 2 else y := 0 - x;
    stmt = Seq(
        Assign('x', BinOp('+', Var('x'), IntConst(1))),
        If(Compare('>', Var('x'), IntConst(0)), Assign('y', BinOp('*', Var('x'), IntConst(2))), Assign('y', BinOp('-', IntConst(0), Var('x'))))
    )
    # Postcondition: { y > 0 }
    post = Compare('>', Var('y'), IntConst(0))

    # Compute wp(stmt, post_z3) and print it
    wp_result = wp(stmt, bexp_to_z3(post))
    print(f"  wp = {wp_result}")

    # For each candidate precondition, check if pre → wp is valid
    candidates = [
        ("x >= 0",  z3_var('x') >= 0),
        ("x >= -1", z3_var('x') >= -1),
        ("x == -1", z3_var('x') == -1),
    ]
    for name, pre in candidates:
        s = Solver()
        s.add(Not(Implies(pre, wp_result)))
        result = s.check()
        valid = (result == unsat)
        print(f"  {name}: {'VALID' if valid else 'INVALID'}")

    #     # [EXPLAIN] in a comment: why is this precondition valid or invalid?

    # [EXPLAIN]: upon running, the wp printed is:
    # wp = And(Implies(0 < x + 1, 0 < (x + 1)*2), Implies(Not(0 < x + 1), 0 < 0 - (x + 1)))
    # This means if x + 1 > 0 then (x + 1)*2 > 0, and if x <= -1 then x < -1
    # This simplifies to if x <= -1 then x < -1 (b/c the LHS is a tautology which cancels out with the identity law)
    # This is equivalent to x > -1 or x < -1 (from the definition of implication)
    # Which just means x != -1

    # [EXPLAIN]: x >= 0
    #   VALID: x >= 0 implies x != -1

    # [EXPLAIN]: x >= -1
    #   INVALID: x >= -1 does NOT imply x != -1, in the x == -1 case

    # [EXPLAIN]: x == -1
    #   INVALID: well obviously this is the exact negation of the wp so it is not valid

    print()


# ============================================================================
if __name__ == "__main__":
    print("=" * 60)
    print("Part (b): VCG Correctness Tests")
    print("=" * 60)
    test_swap()
    test_abs()

    print("=" * 60)
    print("Part (a): WP Derivation via Z3")
    print("=" * 60)
    test_wp_derivation()

    print("=" * 60)
    print("Part (c): Invariant Discovery")
    print("=" * 60)
    test_mult()
    test_add()
    test_sum()

    print("=" * 60)
    print("Part (d): Find the Bug")
    print("=" * 60)
    test_buggy_div()
