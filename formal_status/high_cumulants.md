# High cumulants

Owned source: `ExactHoeffding/HighCumulants.lean`.

The module contains explicit actual-mass raw moments through degree six,
the fifth and sixth moment--cumulant recursions, and totalized factorial
closed forms for every legal population size.  It also defines the inverse
population continuation, proves its equality with actual factorial moments,
and states the fifth/sixth balanced limiting values and the leading fifth
cumulant derivative.

Verification completed: `lean -j 1` returned exit code zero with the pinned
Lean 4.33.0 toolchain.  The build used the shared `flock` and a 600-second
limit inside the lock. The only diagnostics are two tactic-style warnings.

Evidence: `/data/hoeffding_full_20261015/evidence/high_cumulants11.log`;
`compile_started=2026-10-15T13:31:11+00:00`, `lean_exit_code=0`.

Checked scope:

- Actual raw moments through degree six equal their Stirling transformations.
- Fifth and sixth actual finite-law cumulants satisfy the standard recursion.
- Both actual hypergeometric cumulants equal totalized factorial closed forms,
  including population sizes below six and all degenerate legal parameters.
- The inverse-population factorial continuation agrees with actual moments at
  `ε=1/N` for every positive legal population with imbalance `N-2k=s`.
- Its fifth/sixth cumulants have balanced limits `0` and `m/4`, including
  limits along any sequence of legal population parameters with fixed `m,s`.
- The fifth cumulant has derivative `-m*s/2` at zero, hence expansion
  `κ5(ε) = -m*s*ε/2 + o(ε)`.

No `sorry`, `admit`, extra axiom or `native_decide` occurs in this module.
Transitive axiom auditing belongs to the root integration audit.

The sharper manuscript remainders `κ5(ε)=-m*s*ε/2+O(ε²)` and
`κ6(ε)=m/4+O(ε)` are not claimed by these limit and first-derivative statements.

The full optimized fourth-order sharp-proxy expansion, its optimizer, and
all fixed-sample extremizer statements are outside this module.
