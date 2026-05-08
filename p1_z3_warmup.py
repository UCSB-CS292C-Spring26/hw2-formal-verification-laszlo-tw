"""
CS292C Homework 2 — Problem 1: Z3 Warm-Up + EUF Puzzle (15 points)
===================================================================
Complete each function below. Run this file to check your answers.
"""

from z3 import *


# ---------------------------------------------------------------------------
# Part (a) — 3 pts
# Find integers x, y, z such that x + 2y = z, z > 10, x > 0, y > 0.
# ---------------------------------------------------------------------------
def part_a():
    x, y, z = Ints('x y z')
    s = Solver()

    # s.add(...)
    s.add(x + 2*y == z)
    s.add(z > 10)
    s.add(x > 0)
    s.add(y > 0)

    print("=== Part (a) ===")
    if s.check() == sat:
        m = s.model()
        print(f"SAT: x={m[x]}, y={m[y]}, z={m[z]}")
    else:
        print("UNSAT (unexpected!)")
    print()


# ---------------------------------------------------------------------------
# Part (b) — 3 pts
# Prove validity of: ∀x. x > 5 → x > 3
# Hint: A formula F is valid iff ¬F is unsatisfiable.
# ---------------------------------------------------------------------------
def part_b():
    x = Int('x')
    s = Solver()

    # s.add(...)
    # negate the implication rule
    s.add(x > 5)
    s.add(Not(x > 3))

    print("=== Part (b) ===")
    result = s.check()
    if result == unsat:
        print("Valid! (negation is UNSAT)")
    else:
        print(f"Not valid — counterexample: {s.model()}")
    print()


# ---------------------------------------------------------------------------
# Part (c) — 5 pts: The EUF Puzzle
#
# Formula:  f(f(x)) = x  ∧  f(f(f(x))) = x  ∧  f(x) ≠ x
#
# STEP 1: Check satisfiability with Z3. (2 pts)
#
# STEP 2: Use Z3 to derive WHY the result holds. (3 pts)
#   Write a series of Z3 validity checks that demonstrate the key reasoning
#   steps. For example, from f(f(x)) = x, what can you derive about f(f(f(x)))?
#   Each check should print what it's testing and whether it holds.
#   Hint: Apply f to both sides of the first equation.
# ---------------------------------------------------------------------------
def part_c():
    S = DeclareSort('S')
    x = Const('x', S)
    f = Function('f', S, S)
    s = Solver()

    # s.add(...)
    s.add(f(f(x)) == x)
    s.add(f(f(f(x))) == x)
    s.add(f(x) != x)

    print("=== Part (c) ===")
    result = s.check()
    if result == sat:
        print(f"SAT: {s.model()}")
    else:
        print("UNSAT")

    # first of all, IF f(f(x)) = x, THEN f(f(f(x))) = f(x), but we already said f(f(f(x))) = x
    # separately, IF f(f(x)) = x AND f(f(f(x))) = x, THEN f(f(x)) = f(f(f(x))) SO x = f(x)
    
    # f(f(x)) = x  alone implies f(f(f(x))) = f(x)
    s1 = Solver()
    s1.add(f(f(x)) == x)            # given
    s1.add(f(f(f(x))) != f(x))      # negate my claim: 
                                    # if z3 can satisfy the negation, i'm wrong!
                                    # but if z3 returns unsat, then my claim is right!
    r1 = s1.check()
    if r1 == unsat:
        print("UNSAT: f(f(x)) == f(x) and not f(f(f(x))) == f(x)\n \
        (in other words, UNSAT: not (f(f(x) == f(x) implies f(f(f(x))) == f(x)))\n \
        therefore, f(f(x)) = x  alone implies f(f(f(x))) = f(x).\n \
        (however, we are also given that f(f(f(x))) = x.\n\
        therefore, by the transitive property, f(x) = x, contradicting the formula)")

    # f(f(x)) = x and f(f(f(x))) = x means f(f(x)) = f(f(f(x))), implying x = f(x) 
    s2 = Solver()
    s2.add(f(f(x)) == x)            # given
    s2.add(f(f(f(x))) == x)         # given
    s2.add(f(x) != x)               # negate my claim
    r2 = s2.check()
    if r2 == unsat:
        print("UNSAT: f(f(x)) == x and f(f(f(x))) == x and not f(x) == x\n\
        (in other words, UNSAT: not ((f(f(x)) == x and f(f(f(x))) == x) implies f(x) == x))\n\
        therefore, f(f(x)) = x and f(f(f(x))) = x together implies x = f(x).\n\
        (because f(f(x)) = f(f(f(x))), which simplifies to x = f(x))")

    print()


# ---------------------------------------------------------------------------
# Part (d) — 4 pts: Array Axioms
#
# Prove BOTH axioms (two separate solver checks):
#   (1) Read-over-write HIT:   i = j  →  Select(Store(a, i, v), j) = v
#   (2) Read-over-write MISS:  i ≠ j  →  Select(Store(a, i, v), j) = Select(a, j)
#
# [EXPLAIN] in a comment below: Why are these two axioms together sufficient
# to fully characterize Store/Select behavior? (2–3 sentences)
# ---------------------------------------------------------------------------
def part_d():
    a = Array('a', IntSort(), IntSort())
    i, j, v = Ints('i j v')

    print("=== Part (d) ===")

    # Axiom 1: Read-over-write HIT
    s1 = Solver()
    # s1.add(...)

    # axiom 1: i = j  →  Select(Store(a, i, v), j) = v
    # negation: i = j AND Select(Store(a, i, v), j) ≠ v
    s1.add(i == j)
    s1.add(Select(Store(a, i, v), j) != v)

    r1 = s1.check()
    print(f"Axiom 1 (hit):  {'Valid' if r1 == unsat else 'INVALID'}")

    # Axiom 2: Read-over-write MISS
    s2 = Solver()
    # s2.add(...)

    # axiom 1: i ≠ j  →  Select(Store(a, i, v), j) = Select(a, j)
    # negation: i ≠ j  and  Select(Store(a, i, v), j) ≠ Select(a, j)
    s2.add(i != j)
    s2.add(Select(Store(a, i, v), j) != Select(a, j))

    r2 = s2.check()
    print(f"Axiom 2 (miss): {'Valid' if r2 == unsat else 'INVALID'}")
    print()

    # [Explain]: Every read after write has exactly two cases. You're either reading 
    # the element you just wrote (in which case you should get the updated value, v), 
    # or you are reading a different element (in which case you should get the value 
    # held by that element prior to the write, unchanged). In other words, either
    # i == j or i != j. These are two distinct cases, covered by axioms 1 and 2 
    # respectively, and there are no other possible cases. Therefore, the two axioms
    # fully characterize Store/Select behavior.
    # (I had Claude explain this to me first because I didn't really understand it.)

# ---------------------------------------------------------------------------
if __name__ == "__main__":
    part_a()
    part_b()
    part_c()
    part_d()
