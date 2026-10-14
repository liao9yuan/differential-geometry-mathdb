import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.AssemblyReduction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology
namespace ConnectedSumQuotient

variable {M : Type} [TopologicalSpace M] [ChartedSpace csModel M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M]
variable {N : Type} [TopologicalSpace N] [ChartedSpace csModel N]
  [IsManifold (𝓡 3) ∞ N] [T2Space N]
variable (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
variable (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)

omit [IsManifold (𝓡 3) ∞ M] [T2Space M] in
theorem boundaryMap_mem_chart_closedBall (z : csSphere) :
    ((c.boundaryMap z : c.Punctured) : M) ∈ c.chart '' Metric.closedBall 0 1 :=
  ⟨(z : csModel), by simp [Metric.mem_closedBall], rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.boundaryMap_mem_chart_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.boundaryMap_mem_chart_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.boundaryMap_mem_chart_closedBall ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.boundaryMap_mem_chart_closedBall

omit [IsManifold (𝓡 3) ∞ M] in
theorem interiorToPunctured_not_mem_chart_closedBall (u : c.interior) :
    ((c.interiorToPunctured u : c.Punctured) : M) ∉ c.chart '' Metric.closedBall 0 1 := by
  rw [← BallChart.mem_interior]
  exact u.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.interiorToPunctured_not_mem_chart_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.interiorToPunctured_not_mem_chart_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.interiorToPunctured_not_mem_chart_closedBall ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.interiorToPunctured_not_mem_chart_closedBall

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem interiorLeft_ne_interiorRight (u : c.interior) (v : d.interior) :
    interiorLeft c d aD u ≠ interiorRight c d aD v := by
  intro h
  obtain ⟨z, hz, -⟩ :=
    (inl_eq_inr_iff c d aD.toHomeomorph (c.interiorToPunctured u) (d.interiorToPunctured v)).mp h
  have h1 : ((c.boundaryMap z : c.Punctured) : M)
      = ((c.interiorToPunctured u : c.Punctured) : M) :=
    congrArg Subtype.val hz
  exact interiorToPunctured_not_mem_chart_closedBall c u
    (h1 ▸ boundaryMap_mem_chart_closedBall c z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.interiorLeft_ne_interiorRight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.interiorLeft_ne_interiorRight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.interiorLeft_ne_interiorRight ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.interiorLeft_ne_interiorRight

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem mem_SeamShell_of_norm_one (z : csSphere) :
    (z : csModel) ∈ SeamShell := by
  rw [SeamShell]
  have h := norm_coe_sphere z
  constructor <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.mem_SeamShell_of_norm_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.mem_SeamShell_of_norm_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.mem_SeamShell_of_norm_one ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.mem_SeamShell_of_norm_one

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [T2Space N] in
theorem seamMap_of_unit (z : csSphere) :
    ∃ w : Seam, seamMap c d aD.toHomeomorph w = inl c d aD.toHomeomorph (c.boundaryMap z) := by
  refine ⟨⟨(z : csModel), mem_SeamShell_of_norm_one z⟩, ?_⟩
  have hnorm : ‖((⟨(z : csModel), mem_SeamShell_of_norm_one z⟩ : Seam) : csModel)‖ = 1 :=
    norm_coe_sphere z
  rw [seamMap_of_one_le c d aD.toHomeomorph _ (le_of_eq hnorm.symm),
    seamLeft_eq_of_one_le c d aD.toHomeomorph _ (le_of_eq hnorm.symm)]
  refine congrArg (inl c d aD.toHomeomorph) (Subtype.ext ?_)
  rw [radialMap_seamDir_coe c
      (⟨(z : csModel), mem_SeamShell_of_norm_one z⟩ : Seam) (le_of_eq hnorm.symm),
    BallChart.boundaryMap_val]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.seamMap_of_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.seamMap_of_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.seamMap_of_unit ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.seamMap_of_unit

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem interior_seam_cover (x : ConnectedSumQuotient c d aD.toHomeomorph) :
    (∃ u, interiorLeft c d aD u = x) ∨ (∃ v, interiorRight c d aD v = x) ∨
      (∃ w : Seam, seamMap c d aD.toHomeomorph w = x) := by
  obtain ⟨y, rfl⟩ | ⟨y, rfl⟩ := jointly_surjective c d aD.toHomeomorph x
  · obtain ⟨z, rfl⟩ | ⟨z, rfl⟩ := c.interior_boundary_cover y
    · exact Or.inl ⟨z, rfl⟩
    · exact Or.inr (Or.inr (seamMap_of_unit c d aD z))
  · obtain ⟨z, rfl⟩ | ⟨z, rfl⟩ := d.interior_boundary_cover y
    · exact Or.inr (Or.inl ⟨z, rfl⟩)
    · refine Or.inr (Or.inr ?_)
      obtain ⟨w, hw⟩ := seamMap_of_unit c d aD (aD.symm z)
      refine ⟨w, ?_⟩
      rw [hw, boundary_eq c d aD.toHomeomorph (aD.symm z)]
      simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedSumQuotient.interior_seam_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedSumQuotient.interior_seam_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedSumQuotient.interior_seam_cover ``Submission.DifferentialGeometry.Topology.ConnectedSumQuotient.interior_seam_cover

end ConnectedSumQuotient
end DifferentialGeometry.Topology
