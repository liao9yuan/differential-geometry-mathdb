# MathDB Poincare preparation — v0.1.4

`Submission.lean` proves the full homotopy-sphere formulation in the native v0.1.4 environment. It is **not compatible with MathDB's current pinned verifier**.

## Provenance

- Upstream: https://github.com/qinz1yang/differential-geometry/releases/tag/v0.1.4
- Immutable source commit: `788efe97894474c032de6dfb1289d515f613d15a`.
- Lean and Mathlib: `v4.35.0-rc3`.
- Mathematical proof: DifferentialGeometry contributors; the upstream LICENSE and NOTICE are retained. The new wrapper derives compactness from the homotopy-sphere hypothesis, transfers simple connectivity, and applies the upstream three-dimensional Poincare theorem.

## Local validation

`lake env lean Submission.lean` exited 0 without warnings. `#print axioms Submission.solution` returned exactly:

```text
'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Validation used the SHA-256-checked upstream release cache, not a complete local source rebuild. Release cache: https://github.com/qinz1yang/differential-geometry/releases/download/v0.1.4/dg-v0.1.4-cache.tar
SHA-256: `079f4aede15006211037c82c5b2a5141c9d9fb9f07dcd4b99a28197e5507ae53`.

`MathDBNativeTargetCheck.lean` separately contains the verbatim MathDB target definitions and its exact Euclidean-space notation, with the unavailable MathDBUtil import replaced by native DG imports. Its theorem `Submission.solution : Problem.Target` also compiled with exactly the same three axioms. This confirms the mathematical target matches in Lean v4.35.0-rc3. It is a local compatibility check, not a replacement for the site's frozen statement or proof of MathDB acceptance.

To check from source on this branch:

```sh
lake build DifferentialGeometry.Topology.ThreeManifold.Poincare DifferentialGeometry.Topology.Homology.Spheres.HomotopySphereCompactness DifferentialGeometry.Topology.Sphere.SphereSimplyConnected
lake env lean Submission.lean
lake env lean MathDBNativeTargetCheck.lean
```

## MathDB status

Problem: https://mathdb.com/p/316224/poincare-conjecture
Saved target: https://mathdb.com/api/posts/b93562c3-e505-49ec-9853-07cffa7a24c3/lean-formalizations

MathDB pins Lean v4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. It does not execute repository Lake configuration and does not currently list DifferentialGeometry as an allowed external dependency. To use its automated checker, a compatible source port into its permitted Submission/ namespace or verifier support for the native dependency is still required. No automatic verification has been attempted, and no MathDB solution has been posted.

The sibling branch `mathdb-poincare-v0.1.3` matches MathDB's exact Lean/Mathlib pins but provides only the native compact/simply-connected wrapper; it still needs the homotopy-sphere compactness bridge and permitted dependency packaging.
