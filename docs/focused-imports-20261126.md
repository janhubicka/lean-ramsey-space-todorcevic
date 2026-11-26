# Focused Ramsey-space imports — 26 November 2026

The approximation-system and Souslin-operation files use elementary sets,
finite lists and tactics. Their `import Mathlib` declarations loaded the
entire umbrella into downstream clients. They now import `Mathlib.Tactic`;
`TopologyBridge` explicitly imports `Mathlib.Topology.Baire.BaireMeasurable`,
which supplies the Baire-measurable-set interface it actually uses.

Every non-import source line in the three changed files is byte-for-byte
unchanged from `e5ff4776217508e752fd215760678644a908a15f`. No theorem
statement, proof, definition, assumption or dependency pin is changed here.

## Local verification

The default `lake build` and a build naming every one of the 54 source
modules under `RamseySpace/` passed with Lean 4.35.0-rc3 and Mathlib
`5bd58ac291422a21f412ae354c91e7d172255a2c`. All six existing audit scripts
passed: 6 first-application reports, 9 published-Ellentuck reports, 13
abstract-Ramsey reports, 3 finite-colouring reports, 16 equivalence-transport
reports and 3 proper-prefix-transport reports.

Both the repository parser and the strict name-by-name parser from `lean-kk`
accepted all 50 reports. Every reported axiom is `propext`, `Classical.choice`
or `Quot.sound`; the source scan found no admitted declaration or custom
axiom. Import narrowing can expose accidental transitive dependencies in
clients; the downstream `lean-kk` integration is checked separately.

[Exact source hashes, commands and named reports](audits/2026-11-26-focused-imports.json)
identify this local checkpoint. Hosted CI is separate evidence.
