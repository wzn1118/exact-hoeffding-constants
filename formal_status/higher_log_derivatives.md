# Actual fifth and sixth log-MGF derivatives

`ExactHoeffding/HigherLogMGFDerivatives.lean` extends the kernel-checked finite
MGF derivative chain through orders five and six.  For every finite weighted law
with nonnegative weights summing to one, the fifth and sixth iterated derivatives
at zero of `Real.log (finiteMGF s w x)` are exactly `finiteCumulant5` and
`finiteCumulant6`, respectively.  The proof differentiates the normalized
finite tilted raw moments recursively and checks the full fifth- and sixth-order
polynomial identities in the Lean kernel.

The hypergeometric specializations
`hypergeom_logMGF_deriv5_zero` and `hypergeom_logMGF_deriv6_zero` identify the
actual derivatives of `Real.log (hypergeomMGF N k m)` with
`hypergeomCumulant5 N k m` and `hypergeomCumulant6 N k m` for all legal
`k ≤ N` and `m ≤ N`, including degenerate cases.

Compilation evidence:

- `/data/hoeffding_full_20261015/evidence/higher_log_derivatives10.log`

The compilation used the shared lock, `timeout 600`, and `lean -j1`; it reports
`lean_exit_code=0`.  The module imports the already compiled
`MGFDerivatives` and `HighCumulants` interfaces and does not modify their
sources or the root import entry.
