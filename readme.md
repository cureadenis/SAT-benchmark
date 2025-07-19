# SAT Solver

This repository contains a simple SAT benchmarking script written in Python.
It tests:
- Resolution
- DP
- DPLL

## Usage

To run the benchmark, use the following command:

```bash
python sat_benchmark.py example.cnf
```

Currently Resolution is disabled due to the long time it takes to execute, if you want it enabled uncomment line 484 and comment out 485.
### Arguments
- `example.cnf`: The input file in DIMACS CNF format. This file contains the SAT problem definition.

### Example

1. Prepare a `.cnf` file (e.g. that matches `bench1.cnf`) with the SAT problem in DIMACS format:
    ```
    p cnf 20  91 

    4 -18 19 0
    3 18 -5 0
    ```

2. Run the solver:
    ```bash
    python sat_solver.py example.cnf
    ```

3. The output will show how long each method takes to solve the problem.

## Notes

- The script assumes the input file is correctly formatted.
- For more details on the DIMACS CNF format, refer to [DIMACS CNF Format Documentation](https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/satformat.ps).