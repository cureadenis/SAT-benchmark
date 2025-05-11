import time
from copy import deepcopy
from typing import List, Set

# Type alias
Clause = List[int]
CNF = List[Clause]

def parse_dimacs(filename: str) -> CNF:
    cnf = []
    with open(filename, 'r') as f:
        for line in f:
            if line.startswith('c') or line.startswith('p'):
                continue
            clause = list(map(int, line.strip().split()))
            if clause and clause[-1] == 0:
                clause.pop()
            cnf.append(clause)
    return cnf

# ---------------- RESOLUTION ------------------

def resolution(cnf: CNF) -> bool:
    clauses = set(frozenset(clause) for clause in cnf)
    new = set()
    resolved_pairs = set()
    step = 0
    iteration = 0

    while True:
        clause_list = list(clauses)
        total_pairs = len(clause_list) * (len(clause_list) - 1) // 2
        print(f"[Resolution] Iteration {iteration} - Clauses: {len(clauses)}", flush=True)
        new_this_round = 0

        for i in range(len(clause_list)):
            for j in range(i + 1, len(clause_list)):
                ci, cj = clause_list[i], clause_list[j]
                pair_key = (ci, cj)
                if pair_key in resolved_pairs:
                    continue
                resolved_pairs.add(pair_key)

                step += 1
                if step % 1000 == 0:
                    print(f"[Resolution] Checked {step} pairs", end='\r')

                resolvents = resolve(ci, cj)
                if frozenset() in resolvents:
                    print()
                    return False
                for r in resolvents:
                    if r not in clauses:
                        new.add(r)
                        new_this_round += 1

        if not new:
            print()
            return True

        print(f"[Resolution] New clauses this round: {new_this_round}", flush=True)
        clauses.update(new)
        new.clear()
        iteration += 1


def resolve(ci: Set[int], cj: Set[int]) -> Set[Set[int]]:
    resolvents = set()
    for l in ci:
        if -l in cj:
            resolvent = (ci - {l}) | (cj - {-l})
            resolvents.add(frozenset(resolvent))
    return resolvents

# ---------------- DAVIS–PUTNAM ------------------

def dp(cnf: CNF) -> bool:
    cnf = deepcopy(cnf)
    variables = {abs(lit) for clause in cnf for lit in clause}
    return dp_solve(cnf, variables)

def dp_solve(cnf: CNF, variables: Set[int], depth=0) -> bool:
    print(f"[DP] Recursion depth: {depth}", end='\r')
    literals = [lit for clause in cnf for lit in clause]
    pure_literals = {lit for lit in literals if -lit not in literals}
    for lit in pure_literals:
        cnf = [clause for clause in cnf if lit not in clause]
        variables.discard(abs(lit))

    if not cnf:
        return True
    if any(clause == [] for clause in cnf):
        return False

    var = next(iter(variables))
    cnf_pos = simplify(cnf, var)
    cnf_neg = simplify(cnf, -var)
    variables.remove(var)

    return dp_solve(cnf_pos, variables.copy(), depth+1) or dp_solve(cnf_neg, variables.copy(), depth+1)

def simplify(cnf: CNF, literal: int) -> CNF:
    simplified = []
    for clause in cnf:
        if literal in clause:
            continue
        new_clause = [l for l in clause if l != -literal]
        simplified.append(new_clause)
    return simplified

# ---------------- DPLL ------------------

def dpll(cnf: CNF, assignment: dict = {}, depth=0) -> bool:
    print(f"[DPLL] Recursion depth: {depth}", end='\r')
    cnf = unit_propagate(cnf, assignment)
    if cnf is None:
        return False
    if not cnf:
        return True

    # Find first unassigned variable
    unassigned_vars = {abs(lit) for clause in cnf for lit in clause if abs(lit) not in assignment}
    if not unassigned_vars:
        return False  # No unassigned vars left, but CNF not empty

    var = next(iter(unassigned_vars))

    for value in [True, False]:
        new_assignment = assignment.copy()
        new_assignment[var] = value
        new_cnf = assign(deepcopy(cnf), var, value)
        if dpll(new_cnf, new_assignment, depth+1):
            return True
    return False


def unit_propagate(cnf: CNF, assignment: dict) -> CNF:
    changed = True
    while changed:
        changed = False
        unit_clauses = [clause for clause in cnf if len(clause) == 1]
        for clause in unit_clauses:
            lit = clause[0]
            var, val = abs(lit), lit > 0
            if var in assignment and assignment[var] != val:
                return None
            assignment[var] = val
            cnf = assign(cnf, var, val)
            changed = True
    return cnf

def assign(cnf: CNF, var: int, value: bool) -> CNF:
    literal = var if value else -var
    new_cnf = []
    for clause in cnf:
        if literal in clause:
            continue
        new_clause = [l for l in clause if l != -literal]
        if new_clause == []:
            new_cnf.append([])
        else:
            new_cnf.append(new_clause)
    return new_cnf

# ---------------- MAIN ------------------

def benchmark(cnf: CNF):
    # methods = [ ("DPLL", dpll), ("DP", dp), ("Resolution", resolution)]
    methods = [ ("DPLL", dpll), ("DP", dp)]
    for name, method in methods:
        print(f"Running {name}...")
        start_time = time.time()
        result = method(cnf)
        end_time = time.time()

        elapsed_time_ms = (end_time - start_time) * 1000
        optional_time = True

        if elapsed_time_ms > 60000:
            elapsed_time = f"{elapsed_time_ms / 60000:.2f} minutes"
        elif elapsed_time_ms > 1000:
            elapsed_time = f"{elapsed_time_ms / 1000:.2f} seconds"
        else:
            elapsed_time = f"{elapsed_time_ms:.2f} milliseconds"
            optional_time = False

        if optional_time:
            print(f"{name} | {elapsed_time_ms:.2f} ms | {elapsed_time} \n")
        else:
            print(f"{name} | {elapsed_time_ms:.2f} ms \n")


if __name__ == '__main__':
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("cnf_file", help="Path to DIMACS CNF file")
    args = parser.parse_args()

    formula = parse_dimacs(args.cnf_file)

    benchmark(formula)