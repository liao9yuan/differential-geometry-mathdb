import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.AssemblyReduction
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientationPrelude
import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationComposition
import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.TopologicalSpace _root_.Metric _root_.Submission.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace OrientationAssembly
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Topology.ConnectedSumQuotient

universe u v

variable {M : ClosedOrientedManifold.{u} 3} {N : ClosedOrientedManifold.{v} 3}
variable (c : OrientedBallChart M) (d : OrientedBallChart N)
  (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)

variable [ChartedSpace csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)]
variable [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)]

theorem isOpen_range_interiorLeft
    (hL : ∀ (f : OpenPartialHomeomorph M.Carrier csModel), f ∈ atlas csModel M.Carrier →
      (leftChart c.toBallChart d.toBallChart aD.toHomeomorph hn3 f).symm ∈
        atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)) :
    IsOpen (Set.range (interiorLeft c.toBallChart d.toBallChart aD)) :=
  (interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hL).isOpen_range

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.isOpen_range_interiorLeft then
    throwError "Refusing to shadow existing declaration OrientationAssembly.isOpen_range_interiorLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.isOpen_range_interiorLeft ``Submission.OrientationAssembly.isOpen_range_interiorLeft

theorem isOpen_range_interiorRight
    (hR : ∀ (g : OpenPartialHomeomorph N.Carrier csModel), g ∈ atlas csModel N.Carrier →
      (rightChart c.toBallChart d.toBallChart aD.toHomeomorph hn3 g).symm ∈
        atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)) :
    IsOpen (Set.range (interiorRight c.toBallChart d.toBallChart aD)) :=
  (interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hR).isOpen_range

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.isOpen_range_interiorRight then
    throwError "Refusing to shadow existing declaration OrientationAssembly.isOpen_range_interiorRight"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.isOpen_range_interiorRight ``Submission.OrientationAssembly.isOpen_range_interiorRight

omit [ChartedSpace csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)]
  [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)] in
theorem range_interiorLeft_disjoint_range_interiorRight :
    Disjoint (Set.range (interiorLeft c.toBallChart d.toBallChart aD))
      (Set.range (interiorRight c.toBallChart d.toBallChart aD)) := by
  rw [Set.disjoint_left]
  rintro x ⟨u, rfl⟩ ⟨v, hv⟩
  obtain ⟨z, hz, -⟩ := (inl_eq_inr_iff c.toBallChart d.toBallChart aD.toHomeomorph
    (c.toBallChart.interiorToPunctured u) (d.toBallChart.interiorToPunctured v)).mp hv.symm
  have h1 : ((c.toBallChart.boundaryMap z : c.toBallChart.Punctured) : M.Carrier) =
      ((c.toBallChart.interiorToPunctured u : c.toBallChart.Punctured) : M.Carrier) :=
    congrArg Subtype.val hz
  have hnot : ((c.toBallChart.interiorToPunctured u : c.toBallChart.Punctured) : M.Carrier) ∉
      c.toBallChart.chart '' Metric.closedBall 0 1 := by
    rw [← BallChart.mem_interior]
    exact u.2
  have hmem : ((c.toBallChart.boundaryMap z : c.toBallChart.Punctured) : M.Carrier) ∈
      c.toBallChart.chart '' Metric.closedBall 0 1 :=
    ⟨(z : csModel), by simp [Metric.mem_closedBall], rfl⟩
  exact hnot (h1 ▸ hmem)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.range_interiorLeft_disjoint_range_interiorRight then
    throwError "Refusing to shadow existing declaration OrientationAssembly.range_interiorLeft_disjoint_range_interiorRight"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.range_interiorLeft_disjoint_range_interiorRight ``Submission.OrientationAssembly.range_interiorLeft_disjoint_range_interiorRight

theorem mem_seamShell_of_norm_one (z : csSphere) :
    (z : csModel) ∈ SeamShell := by
  rw [SeamShell]
  have h := norm_coe_sphere z
  constructor <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.mem_seamShell_of_norm_one then
    throwError "Refusing to shadow existing declaration OrientationAssembly.mem_seamShell_of_norm_one"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.mem_seamShell_of_norm_one ``Submission.OrientationAssembly.mem_seamShell_of_norm_one

omit [ChartedSpace csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)]
  [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)] in
theorem seamMap_of_unit (z : csSphere) :
    ∃ w : Seam, seamMap c.toBallChart d.toBallChart aD.toHomeomorph w =
      inl c.toBallChart d.toBallChart aD.toHomeomorph (c.toBallChart.boundaryMap z) := by
  refine ⟨⟨(z : csModel), mem_seamShell_of_norm_one z⟩, ?_⟩
  have hnorm : ‖((⟨(z : csModel), mem_seamShell_of_norm_one z⟩ : Seam) : csModel)‖ = 1 :=
    norm_coe_sphere z
  rw [seamMap_of_one_le c.toBallChart d.toBallChart aD.toHomeomorph _ (le_of_eq hnorm.symm),
    seamLeft_eq_of_one_le c.toBallChart d.toBallChart aD.toHomeomorph _ (le_of_eq hnorm.symm)]
  refine congrArg (inl c.toBallChart d.toBallChart aD.toHomeomorph) (Subtype.ext ?_)
  rw [radialMap_seamDir_coe c.toBallChart
      (⟨(z : csModel), mem_seamShell_of_norm_one z⟩ : Seam) (le_of_eq hnorm.symm),
    BallChart.boundaryMap_val]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.seamMap_of_unit then
    throwError "Refusing to shadow existing declaration OrientationAssembly.seamMap_of_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.seamMap_of_unit ``Submission.OrientationAssembly.seamMap_of_unit

omit [ChartedSpace csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)]
  [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)] in
theorem range_interior_left_right_union_seamChartX_source :
    Set.range (interiorLeft c.toBallChart d.toBallChart aD) ∪
        Set.range (interiorRight c.toBallChart d.toBallChart aD) ∪
        (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph).source = Set.univ := by
  rw [seamChartX_source]
  ext x
  simp only [_root_.Set.mem_union, _root_.Set.mem_range, _root_.Set.mem_univ, iff_true]
  obtain ⟨y, rfl⟩ | ⟨y, rfl⟩ := jointly_surjective c.toBallChart d.toBallChart aD.toHomeomorph x
  · obtain ⟨z, rfl⟩ | ⟨z, rfl⟩ := c.toBallChart.interior_boundary_cover y
    · exact Or.inl (Or.inl ⟨z, rfl⟩)
    · exact Or.inr (seamMap_of_unit c d aD z)
  · obtain ⟨z, rfl⟩ | ⟨z, rfl⟩ := d.toBallChart.interior_boundary_cover y
    · exact Or.inl (Or.inr ⟨z, rfl⟩)
    · refine Or.inr ?_
      obtain ⟨w, hw⟩ := seamMap_of_unit c d aD (aD.symm z)
      refine ⟨w, ?_⟩
      rw [hw, boundary_eq c.toBallChart d.toBallChart aD.toHomeomorph (aD.symm z)]
      simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.range_interior_left_right_union_seamChartX_source then
    throwError "Refusing to shadow existing declaration OrientationAssembly.range_interior_left_right_union_seamChartX_source"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.range_interior_left_right_union_seamChartX_source ``Submission.OrientationAssembly.range_interior_left_right_union_seamChartX_source

end OrientationAssembly
