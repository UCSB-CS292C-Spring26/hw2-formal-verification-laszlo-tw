"""
CS292C Homework 2 — Problem 3: Agent Permission Policy Verification (25 points)
=================================================================================
Encode a realistic agent permission policy as SMT formulas and use Z3 to
analyze it for safety properties and privilege escalation vulnerabilities.
"""

from z3 import *

# ============================================================================
# Constants
# ============================================================================

FILE_READ = 0
FILE_WRITE = 1
SHELL_EXEC = 2
NETWORK_FETCH = 3

ADMIN = 0
DEVELOPER = 1
VIEWER = 2

# ============================================================================
# Sorts and Functions
#
# You will use these to build your policy encoding.
# Do NOT modify these declarations.
# ============================================================================

User = DeclareSort('User')
Resource = DeclareSort('Resource')

role         = Function('role', User, IntSort())          # 0=admin, 1=dev, 2=viewer
is_sensitive = Function('is_sensitive', Resource, BoolSort())
in_sandbox   = Function('in_sandbox', Resource, BoolSort())
owner        = Function('owner', Resource, User)

# The core predicate: is this (user, tool, resource) triple allowed?
allowed = Function('allowed', User, IntSort(), Resource, BoolSort())


# ============================================================================
# Part (a): Encode the Policy — 10 pts
#
# Encode rules R1–R5 from the README as Z3 constraints.
#
# You must design the encoding yourself. Consider:
# - Use ForAll to make rules apply to all users/resources.
# - Encode both what IS allowed and what is NOT allowed.
# - Rule R4 overrides R3 — handle this carefully.
#
# Return a list of Z3 constraints.
# ============================================================================

def make_policy():
    """
    Return a list of Z3 constraints encoding rules R1–R5.

    Implement this. You need to think about:
    1. How to express "viewers may ONLY do X" (everything else is denied).
    2. How R4 overrides R3 for admins.
    3. Whether you need a closed-world assumption (if not explicitly
       allowed, it's denied).
    """
    u = Const('u', User)
    r = Const('r', Resource)
    t = Int('t')

    constraints = []

    # Hint: Start with a default-deny rule, then add exceptions.

    constraints.append(ForAll([u, t, r], 
        allowed(u, t, r) == And(
            # R4: nobody can use shell_exec on sensitive resources (overrides everything especially R3)
            Not(And(t == SHELL_EXEC, is_sensitive(r))),
            Or(
                # R1: viewers can only file_read non-sensitive resources
                And(role(u) == VIEWER, t == FILE_READ, Not(is_sensitive(r))),
                # R2: developers may file_read anything...
                And(role(u) == DEVELOPER, t == FILE_READ),
                # R2: ... and file_write resources they own or that are in the sandbox.
                And(role(u) == DEVELOPER, t == FILE_WRITE, Or(owner(r) == u, in_sandbox(r))),
                # R3: admins can use any tool on any resource
                # R5: network_fetch is only allowed on sandbox resources
                And(role(u) == ADMIN, Not(And(t == NETWORK_FETCH, Not(in_sandbox(r)))))
            )
        )
    ))

    return constraints


# ============================================================================
# Part (b): Policy Queries — 8 pts
# ============================================================================

def query(description, policy, extra):
    """Helper: check if extra constraints are SAT under the policy."""
    s = Solver()
    s.add(policy)
    s.add(extra)
    result = s.check()
    print(f"  {description}")
    print(f"  → {result}")
    if result == sat:
        m = s.model()
        print(f"    Model: {m}")
    print()
    return result


def part_b():
    """
    Answer the four queries from the README.
    For query 4, also demonstrate what becomes possible without R4.

    Implement each query.
    """
    policy = make_policy()
    print("=== Part (b): Policy Queries ===\n")

    u = Const('u', User)
    r = Const('r', Resource)

    # Q1: Can a developer write to a sensitive file they don't own, in the sandbox?
    query("Q1: Can a developer write to a sensitive file they don't own, in the sandbox?", policy, [
        role(u) == DEVELOPER,
        is_sensitive(r),
        owner(r) != u,
        in_sandbox(r),
        allowed(u, FILE_WRITE, r)
    ])
    # [COMMENT]: should be SAT: R2 allows developers to file_write to any resources in the sandbox regardless of ownership/sensitivity

    # Q2: Can an admin network_fetch a resource outside the sandbox?
    query("Q2: Can an admin network_fetch a resource outside the sandbox?", policy, [
        role(u) == ADMIN,
        Not(in_sandbox(r)),
        allowed(u, NETWORK_FETCH, r)
    ])
    # [COMMENT]: should be UNSAT: R5 only allows network_fetch on resources in the sandbox regardless of role

    # Q3: Is there ANY role that can shell_exec on a sensitive resource?
    query("Q3: Is there ANY role that can shell_exec on a sensitive resource?", policy, [
        is_sensitive(r),
        allowed(u, SHELL_EXEC, r)
    ])
    # [COMMENT]: should be UNSAT: R4 denies shell_exec on sensitive resources for all roles

    # Q4: [EXPLAIN] in a comment Remove R4 — what dangerous action becomes possible?
    u2 = Const('u2', User)
    r2 = Const('r2', Resource)
    t2 = Int('t2')
    part_b_policy = [ForAll([u2, t2, r2], 
        allowed(u2, t2, r2) == Or(
            # R1: viewers can only file_read non-sensitive resources
            And(role(u2) == VIEWER, t2 == FILE_READ, Not(is_sensitive(r2))),
            # R2: developers may file_read anything...
            And(role(u2) == DEVELOPER, t2 == FILE_READ),
            # R2: ... and file_write resources they own or that are in the sandbox.
            And(role(u2) == DEVELOPER, t2 == FILE_WRITE, Or(owner(r2) == u2, in_sandbox(r2))),
            # R3: admins can use any tool on any resource
            # R5: network_fetch is only allowed on sandbox resources
            And(role(u2) == ADMIN, Not(And(t2 == NETWORK_FETCH, Not(in_sandbox(r2)))))
        )
    )]
    query("Q4: What dangerous action becomes possible?", part_b_policy, [
        role(u) == ADMIN,
        is_sensitive(r),
        allowed(u, SHELL_EXEC, r)
    ])
    # [EXPLAIN]: should be SAT: After removing R4, nothing prevents admins from using shell_exec on sensitive resources,
    # which creates a critical vulnerability because it exposes sensitive files to arbitrary code execution.

# ============================================================================
# Part (c): Privilege Escalation — 7 pts
#
# New rule R6: Developers may shell_exec on non-sensitive sandbox resources.
#
# Attack scenario: A developer uses shell_exec on a non-sensitive sandbox
# resource to change ANOTHER resource's sensitivity flag (e.g., modifying
# a config file that controls access). This makes a previously sensitive
# resource become non-sensitive, bypassing R4 on the next step.
#
# Model this as a 2-step trace where a resource's sensitivity changes
# between steps.
# ============================================================================

def part_c():
    """
    1. Add rule R6 to the policy.
    2. Model a 2-step trace:
       - Step 1: developer calls shell_exec on resource r1
         (r1 is non-sensitive and in sandbox — allowed by R6)
         Side-effect: this command changes resource r2 from sensitive to
         non-sensitive (e.g., modifying an access-control config)
       - Step 2: developer calls shell_exec on resource r2
         (r2 is NOW non-sensitive — was it allowed before? is it allowed now?)
    3. The twist: r2's sensitivity changes BETWEEN steps. Encode this by
       using two copies of is_sensitive (before and after).
    4. Check if the developer can effectively access a previously-sensitive resource.
    5. [EXPLAIN] in a comment: Propose and implement a fix.
    """
    print("=== Part (c): Privilege Escalation ===\n")

    # Hint: Use is_sensitive_before and is_sensitive_after as two separate
    # functions, or use a time-indexed model.

    # [ATTRIBUTION]: I workshopped this part with Claude because I was very confused at first 
    
    def make_part_c_policy(sensitivity):
        u_c = Const('u_c', User)
        r_c = Const('r_c', Resource)
        t_c = Int('t_c')

        return [ForAll([u_c, t_c, r_c], 
            allowed(u_c, t_c, r_c) == And(
                # R4: nobody can use shell_exec on sensitive resources (overrides everything especially R3)
                Not(And(t_c == SHELL_EXEC, sensitivity(r_c))),
                Or(
                    # R1: viewers can only file_read non-sensitive resources
                    And(role(u_c) == VIEWER, t_c == FILE_READ, Not(sensitivity(r_c))),
                    # R2: developers may file_read anything...
                    And(role(u_c) == DEVELOPER, t_c == FILE_READ),
                    # R2: ... and file_write resources they own or that are in the sandbox.
                    And(role(u_c) == DEVELOPER, t_c == FILE_WRITE, Or(owner(r_c) == u_c, in_sandbox(r_c))),
                    # R3: admins can use any tool on any resource
                    # R5: network_fetch is only allowed on sandbox resources
                    And(role(u_c) == ADMIN, Not(And(t_c == NETWORK_FETCH, Not(in_sandbox(r_c))))),
                    # R6: developers may shell_exec on non-sensitive sandbox resources
                    And(role(u_c) == DEVELOPER, t_c == SHELL_EXEC, in_sandbox(r_c), Not(sensitivity(r_c)))
                )
            )
        )]
    
    u  = Const('u',  User)
    r1 = Const('r1', Resource)  # resource developer will shell_exec on (the "lever")
    r2 = Const('r2', Resource)  # resource developer wants to access (the "target")

    is_sensitive_before = Function('is_sensitive_before', Resource, BoolSort())
    is_sensitive_after  = Function('is_sensitive_after',  Resource, BoolSort())

    setup_constraints = [
        # user is a developer
        role(u) == DEVELOPER,

        # r1 is in sandbox
        in_sandbox(r1),
        # r1 is non-sensitive and in sandbox
        Not(is_sensitive_before(r1)),

        # r2 is in sandbox
        in_sandbox(r2),
        # r2 is sensitive before step 1
        is_sensitive_before(r2),
        # r2 is non-sensitive after step 1
        Not(is_sensitive_after(r2)),

        # r1 and r2 are different resources
        r1 != r2
    ]

    # step 1: developer shell_execs r1
    query("Step 1: Can developer use shell_exec r1 to flip r2's sensitivity?", make_part_c_policy(is_sensitive_before), setup_constraints + [allowed(u, SHELL_EXEC, r1)])
    # SAT: allowed by R6 because r1 is non-sensitive and in sandbox

    # step 2: developer shell_execs r2, which was made non-sensitive by step 1
    query("Step 2: Can developer shell_exec r2 after sensitivity flip?", make_part_c_policy(is_sensitive_after), setup_constraints + [allowed(u, SHELL_EXEC, r2)])
    # SAT: also allowed by R6, because r2 is in sandbox and now non-sensitive
    # Developer has effectively bypassed R4 by using R6 to access a previously-sensitive resource

    # 5.
    # fix: sensitivity labels are immutable
    every_resource = Const('every_resource', Resource)
    immutability_constraint = ForAll([every_resource], is_sensitive_before(every_resource) == is_sensitive_after(every_resource))

    query("Step 1 after fix", make_part_c_policy(is_sensitive_before), setup_constraints + [allowed(u, SHELL_EXEC, r1), immutability_constraint])

    result = query("Step 2 after fix", make_part_c_policy(is_sensitive_after), setup_constraints + [allowed(u, SHELL_EXEC, r2), immutability_constraint])
    if result == unsat:
        print("  ESCALATION BLOCKED")
    
    # [EXPLAIN]: my fix is to prevent any operation from changing the sensitivity labels of the resources
    # I tried creating a new policy that reflected this but it was nontrivial and really overcomplicated things 
    # so instead I simulated this by adding an additional constraint requiring that for all resources
    # is_sensitive_before must be equivalent to is_sensitive_after. This foils the attack scenario 
    # because the attacker can no longer flip r2 from sensitive to non-sensitive.
    

    print()


# ============================================================================
if __name__ == "__main__":
    part_b()
    part_c()
