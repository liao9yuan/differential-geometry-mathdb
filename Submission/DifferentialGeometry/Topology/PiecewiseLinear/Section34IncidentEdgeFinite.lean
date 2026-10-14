/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34BoundaryDiskFamilies
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteSplittingDisks

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ : Type u} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}

open _root_.Classical in
theorem section34_incident_edges_finite
    (hends : ∀ e, (e.1 : Set Ea) =
      ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea))
    (w : Section34VertexIndex 𝒦 𝒦') :
    Finite {e : Section34EdgeIndex 𝒦 𝒦' //
      w = (ends e).1 ∨ w = (ends e).2} := by
  classical
  let C := {s : 𝒦'.complex.faces // w.1 ⊆ (s.1 : Finset Ea)}
  have hC : Finite C := (𝒦'.cofaces_finite w.2.1).to_subtype
  let f : {e : Section34EdgeIndex 𝒦 𝒦' //
      w = (ends e).1 ∨ w = (ends e).2} → C := fun i =>
    ⟨⟨i.1.1, i.1.2.1⟩, by
      apply Finset.coe_subset.mp
      rw [hends i.1]
      rcases i.2 with hw | hw
      · exact (congrArg (fun z : Section34VertexIndex 𝒦 𝒦' => (z.1 : Set Ea)) hw).le.trans
          Set.subset_union_left
      · exact (congrArg (fun z : Section34VertexIndex 𝒦 𝒦' => (z.1 : Set Ea)) hw).le.trans
          Set.subset_union_right⟩
  exact Finite.of_injective f (by
    intro i j hij
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : C => (q.1.1 : Finset Ea)) hij)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34_incident_edges_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34_incident_edges_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34_incident_edges_finite ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34_incident_edges_finite

end DifferentialGeometry.Topology.PiecewiseLinear
