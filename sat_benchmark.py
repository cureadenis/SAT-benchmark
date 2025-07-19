import time
import os
from copy import deepcopy
from typing import List, Set, Tuple

# Type aliases
Clause = List[int]
CNF = List[Clause]

def parse_dimacs(filename: str) -> CNF:
    """
    Parses a DIMACS CNF file into a list of clauses.
    Each clause is a list of integers (literals), terminated by 0 in the file.
    Handles comment lines, problem lines, and the common '%' end-of-file marker.
    """
    cnf = []
    with open(filename, 'r') as f:
        for line in f:
            line = line.strip() # Remove leading/trailing whitespace
            
            if not line: # Skip empty lines
                continue
            if line.startswith('c'): # Skip comment lines
                continue
            if line.startswith('p'): # Skip problem line (we get num_vars/clauses from data)
                continue
            if line.startswith('%'): # NEW: Handle common end-of-file marker
                break # Stop processing lines after '%'
            
            # This line should now only contain integers for clauses
            clause = list(map(int, line.split()))
            
            if clause and clause[-1] == 0:
                clause.pop() # Remove the trailing 0
            
            if clause: # Only add non-empty clauses to CNF
                cnf.append(clause)
    return cnf
# ---------------- RESOLUTION ------------------

def resolve(ci: frozenset[int], cj: frozenset[int]) -> Set[frozenset[int]]:
    """
    Computes all possible resolvents between two clauses ci and cj.
    Returns a set of frozensets, where each frozenset is a resolvent.
    """
    resolvents = set()
    
    # Find common variables with opposite signs for resolution
    pivot_literals = {l for l in ci if -l in cj}

    for l in pivot_literals:
        # Create the resolvent by combining clauses and removing the pivot literal pair
        resolvent_set = (ci - {l}) | (cj - {-l})
        
        # Check for tautology: if a literal and its negation are both in the resolvent, it's a tautology
        is_tautology = False
        for lit_in_res in resolvent_set:
            if -lit_in_res in resolvent_set:
                is_tautology = True
                break
        
        if not is_tautology:
            resolvents.add(frozenset(resolvent_set))
    return resolvents

def simplify_clauses(clauses: Set[frozenset[int]]) -> Set[frozenset[int]]:
    """
    Removes tautologies and subsumed clauses from the set of clauses.
    """
    # 1. Remove tautologies (clauses containing both a literal and its negation)
    #    and convert to a mutable set for modification.
    temp_set = set()
    for clause in clauses:
        is_tautology = False
        for lit in clause:
            if -lit in clause:
                is_tautology = True
                break
        if not is_tautology:
            temp_set.add(clause)
    
    # 2. Remove subsumed clauses
    # This is an O(N^2) operation, potentially very slow for large numbers of clauses.
    # Creating a list to iterate allows safe modification of the set being built.
    simplified_set = set(temp_set)
    list_of_clauses = list(temp_set) # Iterate over a static copy
    
    for i in range(len(list_of_clauses)):
        c1 = list_of_clauses[i]
        if c1 not in simplified_set: # c1 might have been subsumed by an earlier clause
            continue
        for j in range(len(list_of_clauses)):
            c2 = list_of_clauses[j]
            if c1 == c2:
                continue
            if c2 in simplified_set and c1.issubset(c2): # If c1 subsumes c2
                simplified_set.discard(c2) # Remove c2 from the result set
    
    return simplified_set


def resolution(cnf: CNF) -> bool:
    """
    Implements the Resolution principle to check for unsatisfiability.
    Returns False if the CNF is unsatisfiable (empty clause derived), True otherwise.
    """
    clauses = set(frozenset(clause) for clause in cnf)
    
    # Initial simplification
    clauses = simplify_clauses(clauses)
    if frozenset() in clauses: # Check for initial empty clause
        return False # Immediately unsatisfiable

    new_clauses_this_round = set()
    iteration = 0

    while True:
        # Optimization: Only resolve new clauses with existing clauses to avoid redundant work
        # This is a common strategy in resolution:
        # R_i = R_{i-1} U {resolve(c_old, c_new) for c_old in clauses, c_new in new_clauses_from_prev_round}
        
        # For simplicity and to ensure all pairs are considered in a "naive" way,
        # we still iterate over all pairs in `clauses`.
        # However, `processed_pairs` helps ensure each pair is only resolved once.

        clause_list = list(clauses) # Convert to list once per iteration for indexing
        total_pairs = len(clause_list) * (len(clause_list) - 1) // 2
        processed_pairs = set() # Stores canonical tuples of frozensets (clause1, clause2)

        print(f"[Resolution] Iteration: {iteration} | Clauses: {len(clauses)} | Current Total Pairs: {total_pairs}             ", end='\r')
        
        new_this_round_count = 0
        
        for i in range(len(clause_list)):
            for j in range(i + 1, len(clause_list)):
                ci, cj = clause_list[i], clause_list[j]
                
                # Create a canonical key for the pair to ensure we don't process it twice
                # Sorting by hash provides a consistent order for frozensets
                pair_key = tuple(sorted((ci, cj), key=lambda x: hash(x)))
                
                if pair_key in processed_pairs:
                    continue
                processed_pairs.add(pair_key)


                resolvents = resolve(ci, cj)
                
                if frozenset() in resolvents: # Empty clause found -> Unsatisfiable
                    print(f"\n[Resolution] Empty clause found at Iteration {iteration}. UNSAT.")
                    return False
                
                for r in resolvents:
                    # Only add truly new and non-tautological clauses
                    if r not in clauses and r not in new_clauses_this_round:
                        new_clauses_this_round.add(r)
                        new_this_round_count += 1
        
        if not new_clauses_this_round: # No new clauses generated, done
            return True # If no empty clause found and no new clauses, it's satisfiable.
        
        # Add all truly new clauses to the main set
        clauses.update(new_clauses_this_round)
        
        # Apply simplification (tautology and subsumption) to the updated clause set
        clauses = simplify_clauses(clauses)
        if frozenset() in clauses: # Check for empty clause after simplification
            return False

        new_clauses_this_round.clear() # Reset for the next iteration
        iteration += 1

# ---------------- DAVIS–PUTNAM (DP) ------------------

def dp(cnf: CNF) -> bool:
    """
    Entry point for the Davis-Putnam algorithm.
    Initializes variables and calls the recursive solver.
    """
    cnf_copy = deepcopy(cnf) # Make a single deepcopy at the start
    variables = {abs(lit) for clause in cnf_copy for lit in clause}
    return dp_solve(cnf_copy, variables)

def dp_solve(cnf: CNF, variables: Set[int], depth=0) -> bool:
    """
    Recursive core of the Davis-Putnam algorithm.
    Applies pure literal elimination and then branches.
    """
    
    # --- Propagation Loop (Pure Literal Elimination) ---
    # In pure DP, only pure literal elimination is done as propagation.
    # Unit propagation is the key addition for DPLL.
    
    # Keep looping as long as pure literals are found and removed
    changed_by_pure_literal = True
    while changed_by_pure_literal:
        changed_by_pure_literal = False

        # Recalculate literals from the current CNF state
        current_literals = {lit for clause in cnf for lit in clause}
        pure_literals = {lit for lit in current_literals if -lit not in current_literals}
        
        if pure_literals:
            # Note the length before simplification to detect changes
            old_len_cnf = len(cnf) 
            for lit in pure_literals:
                # Remove clauses containing pure literals
                cnf = [clause for clause in cnf if lit not in clause]
                # Remove the variable from consideration
                variables.discard(abs(lit))
            
            if len(cnf) < old_len_cnf: # If clauses were actually removed
                changed_by_pure_literal = True
            
            # Check base cases immediately after simplification
            if not cnf:
                return True # All clauses satisfied
            if any(clause == [] for clause in cnf):
                return False # Empty clause means contradiction
        
        # If no pure literals found in this iteration of the while loop, break
        if not changed_by_pure_literal:
            break

    # --- Print Progress (less often for deep recursion) ---
    if depth % 100 == 0 or depth < 5:
        # The `\r` (carriage return) makes the line update in place.
        # For capturing output to a file, you might want to remove `end='\r'`.
        print(f"[DP] Depth: {depth} | Clauses: {len(cnf)} | Vars left: {len(variables)} | Pure: {len(pure_literals)}", end='\r')

    # --- Base Cases after Propagation ---
    if not cnf: # All clauses satisfied (empty CNF)
        return True
    if any(clause == [] for clause in cnf): # Found an empty clause (contradiction)
        return False
    if not variables: # No variables left to assign, but CNF is not empty or contradictory
        # This means the current partial assignment leads to an unsatisfiable subproblem.
        return False

    # --- Decision Phase (Branching) ---
    # Choose a variable to branch on.
    # Simple heuristic: pick the variable with the highest literal count (most-occurring variable).
    literal_counts = {}
    for clause in cnf:
        for lit in clause:
            abs_lit = abs(lit)
            if abs_lit in variables: # Only count unassigned variables
                literal_counts[abs_lit] = literal_counts.get(abs_lit, 0) + 1
    
    # If no literals in clauses (e.g., all clauses were satisfied by pure literals leaving an empty set of literals)
    # but the CNF itself is not empty (e.g., [[]] was implicitly added, but caught by base case)
    # This scenario is mostly a safeguard.
    if not literal_counts:
        return False

    # Select the variable with the maximum count
    var_to_branch = max(literal_counts, key=literal_counts.get)
    
    # --- Recursive Calls ---
    # Create copies of variables for each branch to maintain isolation
    variables_for_pos_branch = variables.copy()
    variables_for_pos_branch.discard(var_to_branch) 

    variables_for_neg_branch = variables.copy()
    variables_for_neg_branch.discard(var_to_branch) 

    # Try assigning True to the variable (literal 'var_to_branch')
    # `_simplify_cnf` creates a new CNF and removes the variable from the set.
    cnf_pos = _simplify_cnf_dp(cnf, var_to_branch)
    if dp_solve(cnf_pos, variables_for_pos_branch, depth + 1):
        return True

    # Try assigning False to the variable (literal '-var_to_branch')
    cnf_neg = _simplify_cnf_dp(cnf, -var_to_branch)
    return dp_solve(cnf_neg, variables_for_neg_branch, depth + 1)

def _simplify_cnf_dp(cnf: CNF, literal: int) -> CNF:
    """
    Simplifies the CNF based on the assignment of 'literal'.
    This function creates and returns a new CNF.
    """
    simplified = []
    for clause in cnf:
        if literal in clause:
            # Clause is satisfied, skip it
            continue
        # Remove the negation of the literal from the clause
        new_clause = [l for l in clause if l != -literal]
        simplified.append(new_clause)
    return simplified

# ---------------- DPLL ------------------

def dpll(cnf: CNF, assignment: dict = None, depth=0) -> bool:
    """
    Implements the Davis-Putnam-Logemann-Loveland (DPLL) algorithm.
    Includes Unit Propagation and Pure Literal Elimination.
    """
    if assignment is None:
        assignment = {}
    
    # --- Propagation Phase ---
    # Repeatedly apply Unit Propagation and Pure Literal Elimination until a fixed point
    # (no more changes) or a conflict/solution is found.
    
    propagated_cnf = deepcopy(cnf) # Start with a copy of the CNF for this recursive call
    current_assignment = assignment.copy() # Work with a copy of the assignment for this path

    changed_in_propagation_loop = True
    while changed_in_propagation_loop:
        changed_in_propagation_loop = False

        # 1. Unit Propagation
        # Returns (new_cnf, new_assignment) or (None, {}) on conflict
        result_unit_prop = _unit_propagate_dpll(propagated_cnf, current_assignment)
        
        if result_unit_prop is None: # Conflict during unit propagation
            return False
        
        new_propagated_cnf, new_assignment_from_prop = result_unit_prop
        
        # Check if unit propagation actually changed anything
        if len(new_propagated_cnf) < len(propagated_cnf) or len(new_assignment_from_prop) > len(current_assignment):
            changed_in_propagation_loop = True
        
        propagated_cnf = new_propagated_cnf
        current_assignment = new_assignment_from_prop
        
        # Immediate checks after unit propagation
        if not propagated_cnf: # All clauses satisfied
            print(f"\n[DPLL] Solution found (after propagation) at depth {depth}")
            return True
        if any(clause == [] for clause in propagated_cnf): # Empty clause means conflict
            return False

        # 2. Pure Literal Elimination
        # Recalculate literals from the current state of propagated_cnf
        current_literals = {lit for clause in propagated_cnf for lit in clause}
        pure_literals = {lit for lit in current_literals if -lit not in current_literals}
        
        if pure_literals:
            old_len_prop_cnf = len(propagated_cnf)
            for lit in pure_literals:
                # Remove clauses containing pure literals. The variable doesn't need to be explicitly
                # removed from `current_assignment` as it wasn't a branching decision.
                propagated_cnf = [clause for clause in propagated_cnf if lit not in clause]
            
            if len(propagated_cnf) < old_len_prop_cnf:
                changed_in_propagation_loop = True
            
            # Immediate checks after pure literal elimination
            if not propagated_cnf:
                print(f"\n[DPLL] Solution found (after pure literal) at depth {depth}")
                return True
            if any(clause == [] for clause in propagated_cnf):
                return False
                
    # --- Print Progress (less frequent for deep recursion) ---
    all_literals_in_cnf = {abs(lit) for clause in propagated_cnf for lit in clause}
    unassigned_vars = {v for v in all_literals_in_cnf if v not in current_assignment}

    if depth % 100 == 0 or depth < 5:
        print(f"[DPLL] Depth: {depth} | Clauses: {len(propagated_cnf)} | Vars left: {len(unassigned_vars)} | Assigned: {len(current_assignment)}     ", end='\r')

    # --- Base Cases after Full Propagation ---
    if not propagated_cnf: # All clauses satisfied
        print(f"\n[DPLL] Solution found at depth {depth}")
        return True
    if any(clause == [] for clause in propagated_cnf): # Empty clause found
        return False
    if not unassigned_vars: # No unassigned vars left, but CNF not empty -> Unsatisfiable
        return False

    # --- Decision Phase (Branching) ---
    # Heuristic: Pick the variable with the highest literal count (most-occurring variable)
    literal_counts = {}
    for clause in propagated_cnf:
        for lit in clause:
            abs_lit = abs(lit)
            if abs_lit in unassigned_vars:
                literal_counts[abs_lit] = literal_counts.get(abs_lit, 0) + 1
    
    # If `unassigned_vars` is not empty but `literal_counts` is (e.g. variables exist but
    # are not present in any remaining clauses). This is a rare edge case for satisfiable.
    if not literal_counts:
        return False

    # Choose the variable with the maximum count for branching
    var_to_branch = max(literal_counts, key=literal_counts.get)

    # Try assigning True to the variable (positive literal)
    new_assignment_true = current_assignment.copy()
    new_assignment_true[var_to_branch] = True
    
    # _assign_dpll simplifies the CNF based on the decision
    cnf_after_branch_true = _assign_dpll(deepcopy(propagated_cnf), var_to_branch, True)
    
    if dpll(cnf_after_branch_true, new_assignment_true, depth + 1):
        return True

    # Try assigning False to the variable (negative literal)
    new_assignment_false = current_assignment.copy()
    new_assignment_false[var_to_branch] = False
    
    cnf_after_branch_false = _assign_dpll(deepcopy(propagated_cnf), var_to_branch, False)
    
    return dpll(cnf_after_branch_false, new_assignment_false, depth + 1)

def _unit_propagate_dpll(cnf: CNF, current_assignment: dict) -> Tuple[CNF, dict] | None:
    """
    Applies unit propagation repeatedly until no more unit clauses are found
    or a conflict/satisfaction is detected.
    Returns (simplified_cnf, updated_assignment) or None if a conflict occurs.
    """
    new_cnf = deepcopy(cnf) # Work on a new copy for this propagation step
    new_assignment = current_assignment.copy()
    
    while True:
        unit_literal_found = False
        literal_to_propagate = None

        # Find a unit clause
        for clause in new_cnf:
            if len(clause) == 1:
                literal_to_propagate = clause[0]
                unit_literal_found = True
                break # Found one, process it

        if not unit_literal_found:
            break # No more unit clauses, exit propagation loop

        var, val = abs(literal_to_propagate), literal_to_propagate > 0

        # Check for consistency with existing assignments
        if var in new_assignment:
            if new_assignment[var] != val:
                return None # Conflict: trying to assign variable inconsistently
            # If consistent, do nothing (already assigned correctly), just let propagation continue
        else:
            # New assignment, add it
            new_assignment[var] = val
        
        # Apply the assignment to the CNF
        temp_cnf = []
        for clause in new_cnf:
            if literal_to_propagate in clause: # Clause satisfied by the literal
                continue
            # Remove the negation of the literal from the clause
            reduced_clause = [l for l in clause if l != -literal_to_propagate]
            if not reduced_clause: # Clause becomes empty, means contradiction
                return None # Conflict: empty clause created
            temp_cnf.append(reduced_clause)
        new_cnf = temp_cnf
        
        # After propagating a literal, check if CNF is now empty (satisfied)
        if not new_cnf:
            return new_cnf, new_assignment

    return new_cnf, new_assignment

def _assign_dpll(cnf: CNF, var: int, value: bool) -> CNF:
    """
    Simplifies a CNF by assigning a variable a specific boolean value.
    Returns a new CNF (does not modify in-place).
    If assigning leads to an empty clause, returns a CNF containing just `[]` to signal conflict.
    """
    literal = var if value else -var
    new_cnf = []
    for clause in cnf:
        if literal in clause:
            continue # Clause is satisfied, skip it
        
        # Remove the negation of the literal from the clause
        reduced_clause = [l for l in clause if l != -literal]
        if not reduced_clause: # Clause becomes empty (contradiction)
            return [[]] # Return a CNF with an empty clause to signal conflict
        new_cnf.append(reduced_clause)
    return new_cnf

# ---------------- MAIN BENCHMARKING ------------------

def benchmark(cnf: CNF, input_path: str):
    results = []
    # methods = [("DPLL", dpll), ("DP", dp), ("Resolution", resolution)]
    methods = [("DPLL", dpll), ("DP", dp)] # Often good for quick comparison

    for name, method in methods:
        # Provide clean line before each solver starts, helpful if previous
        # solver used `end='\r'` for progress updates.
        print(f"\n--- Running {name} for {os.path.basename(input_path)} ---") 
        
        # Each method modifies the CNF, so pass a fresh deepcopy for each run.
        cnf_copy_for_method = deepcopy(cnf) 

        start_time = time.time()
        # DPLL needs an initial empty assignment dictionary
        if name == "DPLL":
            result = method(cnf_copy_for_method, {})
        else: 
            result = method(cnf_copy_for_method)
        end_time = time.time()

        elapsed_time_s = end_time - start_time
        elapsed_time_ms = elapsed_time_s * 1000

        # Format time for readability
        if elapsed_time_s < 1e-6:
            elapsed_time_str = f"{elapsed_time_s * 1e9:.2f} nanoseconds"
        elif elapsed_time_s < 1e-3:
            elapsed_time_str = f"{elapsed_time_s * 1e6:.2f} microseconds"
        elif elapsed_time_s < 1:
            elapsed_time_str = f"{elapsed_time_s * 1e3:.2f} milliseconds"
        elif elapsed_time_s < 60:
            elapsed_time_str = f"{elapsed_time_s:.2f} seconds"
        else:
            elapsed_time_str = f"{elapsed_time_s / 60:.2f} minutes"

        # Print final result, ensuring the progress line is overwritten/cleared
        print(f"\r{name} | Result: {'Satisfiable' if result else 'Unsatisfiable'} | Time: {elapsed_time_ms:.2f} ms ({elapsed_time_str})")
        results.append(f"{name} | Result: {'Satisfiable' if result else 'Unsatisfiable'} | Time: {elapsed_time_ms:.2f} ms ({elapsed_time_str})")

    # Determine output filename and path
    base_name = os.path.basename(input_path)
    name_no_ext = os.path.splitext(base_name)[0]
    out_dir = "results" # Standardized folder name
    out_path = os.path.join(out_dir, name_no_ext + ".txt")

    # Ensure the results directory exists
    os.makedirs(out_dir, exist_ok=True)

    # Write results to file
    with open(out_path, "w") as f:
        f.write(f"Benchmark Results for {input_path}:\n\n")
        for line in results:
            f.write(line + "\n")
    print(f"\nResults saved to {out_path}")

if __name__ == '__main__':
    import argparse

    # Set up argument parsing for the CNF file
    parser = argparse.ArgumentParser(description="Benchmark SAT solvers on DIMACS CNF files.")
    parser.add_argument("cnf_file", help="Path to DIMACS CNF file")
    args = parser.parse_args()

    # Parse the CNF file
    formula = parse_dimacs(args.cnf_file)
    print(f"Loaded CNF: {args.cnf_file} with {len(formula)} clauses.")

    # Run the benchmarks
    benchmark(formula, args.cnf_file)