# MathDB Poincare preparation — v0.1.3

This branch provides a native `Submission.lean` wrapper around the upstream Poincare theorem. It is **not yet an accepted MathDB verifier submission**.

## Provenance

- Upstream: https://github.com/qinz1yang/differential-geometry
- Release: v0.1.3; source commit `7a48598d35109aa99d1cc678e2724c213cdf4ff3`.
- Lean: `leanprover/lean4:v4.33.1`.
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
- The mathematical proof is the work of the upstream DifferentialGeometry contributors. Their LICENSE and NOTICE are retained. This branch only adds a wrapper and submission notes.

## Verification status

Upstream CI https://github.com/qinz1yang/differential-geometry/actions/runs/36305635235 built the exact tagged source with `lake --no-cache build DifferentialGeometry` and completed successfully (26262 jobs). The new wrapper has not been compiled locally in v0.1.3; this release has no downloadable build cache.

To check from this branch:

```sh
lake build DifferentialGeometry.Topology.ThreeManifold.Poincare
lake env lean Submission.lean
```

## Remaining MathDB requirements

MathDB problem: https://mathdb.com/p/316224/poincare-conjecture

Its saved formalization is https://mathdb.com/api/posts/b93562c3-e505-49ec-9853-07cffa7a24c3/lean-formalizations (formalization ID `e635de84-f181-4c67-a7e9-d43a90afad09`). It requires `Submission.solution : Problem.Target`, imported from `FtpEvalBench.YPoincare_poincare_conjecture`.

The Lean version and exact Mathlib revision above match MathDB's saved environment. However:

1. The native theorem assumes compactness and simple connectivity. The frozen target assumes a homotopy equivalence with the three-sphere, so compactness must be proved, not added as an assumption. The needed general homotopy-sphere compactness lemma is available in v0.1.4, but was not found in v0.1.3.
2. MathDB does not execute submitted Lake configurations, and DifferentialGeometry is not among the saved release's permitted external imports. Its rules allow supporting sources under `Submission/` with declarations in namespace `Submission`. The v0.1.3 Poincare closure has 14,197 DifferentialGeometry modules, 204,832,268 source bytes, and 4,021,103 lines. Renaming root declarations, references and imports consistently, recompiling them, and confirming the verifier's resource limits remain necessary.

Do not upload this branch into the automatic proof-verification field as though these requirements were resolved. An ordinary solution post can instead link this source as credited repository evidence and explicitly distinguish upstream/native verification from MathDB verification.

The sibling branch `mathdb-poincare-v0.1.4` contains a locally checked wrapper for the full homotopy-sphere statement in the v0.1.4 environment. Its newer Lean version is incompatible with the current MathDB pin.

## Attempted bridge backport

A separate isolated test copied the v0.1.4 compactness bridge's 31-module closure (30 new files, about 337 kB) into the exact Lean 4.33.1 / Mathlib 0df444a environment. A namespace-aware text scan found no candidate declaration collisions, but that is not a combined kernel check.

The actual build failed with missing Mathlib modules:

- `Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative`
- `Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex`

The new sphere simply-connectivity file compiled in the old environment, but the compactness bridge requires additional Mathlib backport work. No failing bridge files were added to this branch. The successful v0.1.4 wrapper remains the validated full homotopy-sphere result.
