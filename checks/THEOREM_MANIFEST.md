# Inspected theorem manifest

After `lake build ExactHoeffding`, run from the repository root (or an extracted complete reproducibility archive):

```sh
python3 checks/export_theorem_manifest.py
python3 checks/check_theorem_manifest.py
```

The default output is `submission/current/theorem_lean_manifest.json`. The
exporter imports `ExactHoeffding` and asks Lean's checked environment for each
unique declaration listed in `checks/manuscript_lean_map.json`. Definitions,
missing declarations, incorrect module/source bindings, and nonapproved axiom
dependencies make the command fail. The helper reads actual `ConstantInfo.thmInfo`
types and proof expressions, not source comments or descriptions of the result.

Each theorem contains its fully qualified name, source module, pretty-printed
Lean type, a SHA-256 of its structural type representation, direct proof-expression
and type-expression constants, transitive axioms, and source/declaration hashes.
Direct dependencies are syntactic constants in the checked expression; they are
not a claim that every dependency is mathematically indispensable. A 64-bit Lean
expression hash is an additional audit fingerprint, not a cryptographic hash.

The freeze check verifies the whole manuscript hash, each theorem-environment
statement hash and line span, the mapping hash, whole Lean-source hashes, dependency-manifest and exporter hashes, per-declaration
metadata checksums, and available Lean declaration ranges. Imported artifacts that do not expose source
ranges are explicitly marked; in that case the declaration signature anchor and
whole-source hash are retained instead of inventing a range. Supplementary claims
bind the map's explicit source line and the whole manuscript; the program does
not infer an unprovided formula range.

For an independent live reinspection, run the exporter with `--check-live`
under the same compilation lock. This compares actual types, expression
fingerprints, dependencies and axioms with the frozen manifest. The cheaper
`--check` mode checks file bindings and stored metadata only; it does not execute
Lean and does not constitute a fresh kernel audit. Kernel verification remains
provided by the clean project build and its axiom audit.

A small test before the umbrella build is available with `--name NAME` and
`--import-module ExactHoeffding.MODULE`. Its output is visibly marked
`selected-test`; the freeze checker rejects it as full-manuscript evidence.

Inspected Lean types do not automatically prove that a paper statement and its
formal statement are semantically equivalent. That correspondence still requires
mathematical review, including parameters, strictness, endpoints, and equality.

Display coverage is tracked separately. For the current paper, check the full inventory and mathematical review binding with:

```sh
python3 checks/manuscript_display_inventory.py --check
python3 checks/check_display_formula_review_binding.py
```

This freezes all 240 display blocks, including unlabelled formulas, and links
them to independent scope reviews. The current 49-row concordance gives every
mapped theorem-class and supplementary result an explicit typed contract and
`Complete` status. Domain qualifications are recorded in the current contracts
and their scope reports; the manifest checker verifies the bindings, types,
source hashes and kernel-audit records.
