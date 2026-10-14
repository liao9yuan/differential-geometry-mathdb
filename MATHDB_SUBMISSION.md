# Poincare submission preparation on DifferentialGeometry v0.1.3

This branch uses the exact MathDB-pinned Lean v4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. It starts from upstream commit `7a48598d35109aa99d1cc678e2724c213cdf4ff3` and adds a backport of the homotopy-sphere compactness bridge.

`Submission.lean` now states the exact frozen goal `Submission.solution : Problem.Target`, imported from `FtpEvalBench.YPoincare_poincare_conjecture`. It derives compactness and simple connectivity from the given homotopy equivalence and applies the upstream Poincare theorem. The proof credit belongs to the upstream DifferentialGeometry and Mathlib contributors; original licenses and source headers are retained.

## Paper and attribution

See [PAPER_REFERENCE.md](PAPER_REFERENCE.md) for the original paper, four authors, equal-contribution note, and release pin: https://arxiv.org/html/2609.33842v1 .

## Verified components

- The complete backported compactness bridge compiles from source on Lean/Mathlib v4.33.1.
- A combined import of full Mathlib, the compactness bridge, and the simply connected sphere theorem passes. Both endpoint axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
- The genuine, unmodified MathDB frozen target and its 229-module support closure compile in the same environment. The target source SHA-256 is `9609b79bd21353e74225bf0e87777ec0a5da6ba3448846fd0ee07b531a596d91`.
- Upstream CI also built the original v0.1.3 source: https://github.com/qinz1yang/differential-geometry/actions/runs/36305635235 .

## Current status

The original Poincare dependency closure has compiled successfully from source (22,902 Lake jobs). The complete native `Submission.solution : Problem.Target` adapter also compiled against the genuine frozen target. Its exact axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`. A complete merged audit inspected 237,126 constants across all 14,234 project modules; the nine names overlapping the frozen environment have exactly identical types, values, and universe parameters. Evidence is saved under `verification/native-*`.

A separate packaging pass is moving helpers and their declarations into MathDB's required `Submission/` layout and `Submission` namespace. This checked native-source branch still uses DifferentialGeometry imports. The final upload layout and MathDB automated acceptance remain pending. No MathDB solution has been published.

## Backport provenance

The new topology bridge is derived from DifferentialGeometry v0.1.4 commit `788efe97894474c032de6dfb1289d515f613d15a`. The compatibility files in `DifferentialGeometry/MathlibCompat/` adapt selected Mathlib definitions and theorems from commit `c55e6e786f49471c72fbddbec5415808896aec1e` to the fixed old API. Changes include relative simplicial homology support, old simplex-coordinate APIs, and older extensionality/connectedness interfaces. The simplex compatibility API is in a unique project namespace to avoid collisions with full Mathlib. No new axioms or incomplete proofs are introduced.

Problem: https://mathdb.com/p/316224/poincare-conjecture

Frozen target: https://github.com/mathdb-lean/problems/blob/26876961225fa83db241aa0d8b96f920cbc1c780/problems/millennium-poincare/YPoincare_poincare_conjecture.lean

The final local check must use the official frozen-target compiled support path in addition to this project's `lake env` paths. MathDB itself supplies that target module to the submission checker.
