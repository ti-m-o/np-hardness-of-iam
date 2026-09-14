# NP-hardness of IAM

A Lean 4 library for developing the proof across separate modules.

- `IAM/CNF.lean`: CNF formulas over string-named variables and their
  satisfiability.
- `IAM.lean`: policy identifiers, allow/deny permissions for the target action
  and attaching or detaching policies from the implicit user, configurations,
  and the reachability predicate `PE`.
- `IAM-NP.lean`: the library entry point; imports the available proof modules.

Build the `IAM-NP` library target with `lake build` or `lake build IAM-NP`.
The project currently uses only Lean's core library.
