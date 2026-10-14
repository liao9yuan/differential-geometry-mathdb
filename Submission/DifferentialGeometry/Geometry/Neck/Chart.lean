import Submission.DifferentialGeometry.Geometry.Curvature.RicciPullback
import Submission.DifferentialGeometry.Geometry.Curvature.RicciRestriction
import Submission.DifferentialGeometry.Geometry.Curvature.AmbientNeckChartLeastRicci

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Metric
open _root_.Submission.DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Neck

private instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealEuclideanSpaceFinOfNatHAdd_differentialGeometry target :: scope.openDecls } }

variable {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] (J : ModelWithCorners ℝ F H)
  [TopologicalSpace M] [ChartedSpace H M]

structure cylindricalChart where
  domain : TopologicalSpace.Opens (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)
  target : TopologicalSpace.Opens M
  chart : domain ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), J⟯ target
  scale : ℝ
  scale_pos : 0 < scale

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.cylindricalChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.cylindricalChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.cylindricalChart ``Submission.DifferentialGeometry.Geometry.Neck.cylindricalChart

variable {J}

def cylindricalChart.region (C : cylindricalChart J (M := M)) (U : Set C.domain) : Set M :=
  Subtype.val '' (C.chart '' U)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Geometry.Neck.cylindricalChart
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.cylindricalChart.region then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.cylindricalChart.region"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.cylindricalChart.region ``Submission.DifferentialGeometry.Geometry.Neck.cylindricalChart.region

theorem cylindricalChart.isOpen_region (C : cylindricalChart J (M := M))
    {U : Set C.domain} (hU : IsOpen U) : IsOpen (C.region U) :=
  C.target.isOpenEmbedding'.isOpenMap _ (C.chart.toHomeomorph.isOpenMap _ hU)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.cylindricalChart.isOpen_region then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.cylindricalChart.isOpen_region"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.cylindricalChart.isOpen_region ``Submission.DifferentialGeometry.Geometry.Neck.cylindricalChart.isOpen_region

def cylindricalChart.axial (C : cylindricalChart J (M := M)) : M → ℝ :=
  Subtype.val.extend
    (fun y : C.target ↦ (Real.sqrt C.scale)⁻¹ *
      (C.chart.symm y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ).2)
    (fun _ ↦ 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.cylindricalChart.axial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.cylindricalChart.axial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.cylindricalChart.axial ``Submission.DifferentialGeometry.Geometry.Neck.cylindricalChart.axial

variable [FiniteDimensional ℝ F] [IsManifold J ∞ M] [T2Space M]

def cylindricalChart.metricCloseOn (C : cylindricalChart J (M := M))
    (g : SmoothRiemannianMetric J M) (ε : ℝ) (U : Set C.domain) : Prop :=
  ∀ x ∈ U, ∀ k : ℕ, k ≤ 2 →
    metricDerivNorm k
      (Diffeomorph.pullbackMetricCross (scaleMetric C.scale C.scale_pos (g.restrictOpen C.target)) C.chart)
      ((roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).restrictOpen C.domain)
      ((roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).restrictOpen C.domain) x ≤ ε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.cylindricalChart.metricCloseOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.cylindricalChart.metricCloseOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.cylindricalChart.metricCloseOn ``Submission.DifferentialGeometry.Geometry.Neck.cylindricalChart.metricCloseOn

theorem cylindricalChart.exists_least_ricci_field_close_to_gradient [BoundarylessManifold J M]
    (C : cylindricalChart J (M := M)) (g : SmoothRiemannianMetric J M)
    {U : Set C.domain} (hU : IsOpen U) (ε : ℝ) (hε : ε < 1 / 200000)
    (hsmall : C.metricCloseOn g ε U) :
    ∃ (ν : M → ℝ) (Y : ∀ y : M, TangentSpace J y),
      ContMDiffOn J 𝓘(ℝ) ∞ C.axial C.target ∧
      ContMDiffOn J 𝓘(ℝ) ∞ ν (C.region U) ∧
      ContMDiffOn J J.tangent ∞ (fun y ↦ (⟨y, Y y⟩ : TangentBundle J M)) (C.region U) ∧
      ∀ y ∈ C.region U, g.inner y (Y y) (Y y) = 1 ∧
        ricciSharp g y (Y y) = ν y • Y y ∧
        (∀ z : TangentSpace J y, g.inner y z z = 1 → ν y ≤ ricciTensor g y z z) ∧
        |ν y| ≤ 5772 * C.scale * ε ∧
        Module.End.eigenspace (ricciSharp g y).toLinearMap (ν y) = Submodule.span ℝ {Y y} ∧
        0 < mvfderiv J C.axial y (Y y) ∧ |mvfderiv J C.axial y (Y y) - 1| ≤ 92354 * ε ∧
        Real.sqrt (g.inner y (Y y - gradFun g C.axial y)
          (Y y - gradFun g C.axial y)) ≤ 184712 * ε :=
  DifferentialGeometry.Geometry.Curvature.exists_ambient_least_ricci_field_close_to_gradient_from_neck_chart
    C.domain C.target g C.chart C.scale C.scale_pos hU ε hε hsmall

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.cylindricalChart.exists_least_ricci_field_close_to_gradient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.cylindricalChart.exists_least_ricci_field_close_to_gradient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.cylindricalChart.exists_least_ricci_field_close_to_gradient ``Submission.DifferentialGeometry.Geometry.Neck.cylindricalChart.exists_least_ricci_field_close_to_gradient

theorem cylindricalChart.exists_least_ricci_field [BoundarylessManifold J M]
    (C : cylindricalChart J (M := M)) (g : SmoothRiemannianMetric J M)
    {U : Set C.domain} (hU : IsOpen U) (ε : ℝ) (hε : ε < 1 / 200000)
    (hsmall : C.metricCloseOn g ε U) :
    ∃ (ν : M → ℝ) (Y : ∀ y : M, TangentSpace J y),
      ContMDiffOn J 𝓘(ℝ) ∞ C.axial C.target ∧
      ContMDiffOn J 𝓘(ℝ) ∞ ν (C.region U) ∧
      ContMDiffOn J J.tangent ∞ (fun y ↦ (⟨y, Y y⟩ : TangentBundle J M)) (C.region U) ∧
      ∀ y ∈ C.region U, g.inner y (Y y) (Y y) = 1 ∧
        ricciSharp g y (Y y) = ν y • Y y ∧
        (∀ z : TangentSpace J y, g.inner y z z = 1 → ν y ≤ ricciTensor g y z z) ∧
        |ν y| ≤ 5772 * C.scale * ε ∧
        Module.End.eigenspace (ricciSharp g y).toLinearMap (ν y) = Submodule.span ℝ {Y y} ∧
        0 < mvfderiv J C.axial y (Y y) ∧ |mvfderiv J C.axial y (Y y) - 1| ≤ 92354 * ε := by
  obtain ⟨ν, Y, hu, hν, hY, hprop⟩ := C.exists_least_ricci_field_close_to_gradient g hU ε hε hsmall
  refine ⟨ν, Y, hu, hν, hY, ?_⟩
  intro y hy
  obtain ⟨hn, he, hm, hb, hs, hp, hd, _⟩ := hprop y hy
  exact ⟨hn, he, hm, hb, hs, hp, hd⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.cylindricalChart.exists_least_ricci_field then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.cylindricalChart.exists_least_ricci_field"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.cylindricalChart.exists_least_ricci_field ``Submission.DifferentialGeometry.Geometry.Neck.cylindricalChart.exists_least_ricci_field

theorem cylindricalChart.not_mem_region_of_ricci_lower_bound [BoundarylessManifold J M]
    (C : cylindricalChart J (M := M)) (g : SmoothRiemannianMetric J M)
    {U : Set C.domain} {ε κ : ℝ} (hε : ε ≤ 1 / 2)
    (hsmall : C.metricCloseOn g ε U) {x : M}
    (hRic : ∀ v : TangentSpace J x, κ * g.inner x v v ≤ ricciTensor g x v v)
    (hκ : 5772 * C.scale * ε < κ) : x ∉ C.region U := by
  rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
  let G := Diffeomorph.pullbackMetricCross
    (scaleMetric C.scale C.scale_pos (g.restrictOpen C.target)) C.chart
  obtain ⟨v, hunit, hupper⟩ :=
    exists_unit_ricciTensor_bound_of_small_metric_derivatives_on_restricted_roundCylinder
      C.domain G z hε (hsmall z hz)
  let w := mfderiv ((𝓡 2).prod 𝓘(ℝ)) J C.chart z v
  have hRicEq : ricciTensor G z v v = ricciTensor g (C.chart z).val w w := by
    rw [ricciTensor_pullbackMetricCross, ricciTensor_scaleMetric,
      DifferentialGeometry.Geometry.Curvature.ricciTensor_restrictOpen,
      mfderiv_subtype_val_apply]
  have hunit' : C.scale * g.inner (C.chart z).val w w = 1 := by
    exact hunit
  have hlow := mul_le_mul_of_nonneg_left (hRic w) C.scale_pos.le
  have hmul := mul_le_mul_of_nonneg_left
    ((le_abs_self _).trans hupper) C.scale_pos.le
  rw [hRicEq] at hmul
  have heq : C.scale * (κ * g.inner (C.chart z).val w w) = κ := by
    rw [mul_left_comm, hunit', mul_one]
  rw [heq] at hlow
  exact (not_lt_of_ge ((hlow.trans hmul).trans_eq (by ring))) hκ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.cylindricalChart.not_mem_region_of_ricci_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.cylindricalChart.not_mem_region_of_ricci_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.cylindricalChart.not_mem_region_of_ricci_lower_bound ``Submission.DifferentialGeometry.Geometry.Neck.cylindricalChart.not_mem_region_of_ricci_lower_bound

end DifferentialGeometry.Geometry.Neck
