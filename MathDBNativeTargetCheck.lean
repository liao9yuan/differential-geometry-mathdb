/-
Copyright 2025 The Formal Conjectures Authors.
Copyright 2026 The mathdb-lean Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import DifferentialGeometry.Topology.ThreeManifold.Poincare
import DifferentialGeometry.Topology.Homology.Spheres.HomotopySphereCompactness
import DifferentialGeometry.Topology.Sphere.SphereSimplyConnected


/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: YPoincare_poincare_conjecture
- collection: millennium
- question_id: millennium:Poincare
- source: formal-conjectures
- source_locator: FormalConjectures/Millennium/Poincare.lean#poincare_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The Millennium Problem, solved by Grigori Perelman in 2003: the Poincaré Conjecture holds.
- notes: Millennium Prize problem Poincare -- https://www.claymath.org/wp-content/uploads/2022/06/poincare.pdf
- track: solved
- answer_shape: proof
- source_stem: Poincare
- source_namespace: PoincareConjecture
- source_theorem: poincare_conjecture
- source_category: research solved
- source_ams: 54 57
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

scoped[EuclideanGeometry] notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)

universe u

namespace Problem

open scoped Manifold ContDiff EuclideanGeometry ContinuousMap

local macro:max "𝕊" noWs n:superscript(term) : term =>
  `(Metric.sphere (0 : EuclideanSpace ℝ (Fin ($(⟨n.raw[0]⟩) + 1))) 1)

/-- The predicate that the generalized Poincaré conjecture holds in dimension $n$, i.e. that
any $n$-dimensional manifold that is homotopy equivalent to the sphere is in fact homeomorphic
to the sphere. -/
def ConjectureFor (n : ℕ) : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (ℝ^n) M], M ≃ₕ 𝕊ⁿ → Nonempty (M ≃ₜ 𝕊ⁿ)

/-- The predicate that the smooth Poincaré conjecture holds in dimension $n$, i.e. that any
smooth $n$-dimensional manifold that is homotopy equivalent to the sphere is in fact diffeomorphic
to the sphere. As in `ConjectureFor`, the manifold must be Hausdorff: `ChartedSpace` and
`IsManifold` do not imply this, and in every positive dimension there is a non-Hausdorff smooth
manifold that is homotopy equivalent to the sphere. -/
def SmoothConjectureFor (n : ℕ) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [ChartedSpace (ℝ^n) M]
    [IsManifold (𝓡 n) ∞ M], M ≃ₕ 𝕊ⁿ → Nonempty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ 𝕊ⁿ)

/-- The values at which the smooth version of the conjecture is known to hold. -/
def SmoothTrueValues : Set ℕ := {1, 2, 3, 5, 6, 12, 56, 61}

abbrev Target : Prop :=
    ConjectureFor 3

end Problem

namespace Submission

theorem solution : Problem.Target := by
  intro M _ _ _ h
  let : CompactSpace M :=
    DifferentialGeometry.Topology.compactSpace_of_homotopyEquiv_sphere h
  let : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
    DifferentialGeometry.Topology.simplyConnectedSpace_sphere_of_two_le (by decide : 2 ≤ 3)
  let : SimplyConnectedSpace M := h.simplyConnectedSpace
  exact DifferentialGeometry.Topology.poincare_conjecture M

end Submission

#print axioms Submission.solution
