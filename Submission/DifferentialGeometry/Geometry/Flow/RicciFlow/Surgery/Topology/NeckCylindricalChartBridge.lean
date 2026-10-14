import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckMarkSideBridge
import Submission.DifferentialGeometry.Geometry.Neck.Chart
import Submission.DifferentialGeometry.Topology.Manifold.OpenEmbedding
import Submission.DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Function
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Metric
open _root_.Submission.DifferentialGeometry.Topology.Manifold
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat target :: scope.openDecls } }

section

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {h : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.exists_cylindricalChart (N : NormalizedNeck h δ k) :
    ∃ (V : TopologicalSpace.Opens M)
      (Φ : neckBuffer δ ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ V),
      (V : Set M) = Set.range (N.chart : neckBuffer δ → M) ∧
      (∀ x, (Φ x : M) = N.chart x) ∧
      (∀ y : V, N.chart (Φ.symm y) = (y : M)) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
      Module.finrank ℝ ThreeSpace := by
    simp [ThreeSpace]
  have hinj : ∀ y : neckBuffer δ,
      Injective (mfderiv NeckCylinderModel ThreeModel (N.chart : neckBuffer δ → M) y) :=
    fun y => injective_mfderiv_of_isImmersionAt NeckCylinderModel ThreeModel
      (N.chart : neckBuffer δ → M) y (N.chart_smooth.isImmersion.isImmersionAt y)
  exact exists_diffeomorph_onto_range_of_injective_immersion (I := NeckCylinderModel)
    (J := ThreeModel) (N.chart : neckBuffer δ → M) N.chart_smooth.contMDiff
    N.chart_smooth.isEmbedding.injective hinj hdim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.exists_cylindricalChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.exists_cylindricalChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.exists_cylindricalChart ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.exists_cylindricalChart

noncomputable def NormalizedNeck.cylindricalChart (N : NormalizedNeck h δ k) :
    DifferentialGeometry.Geometry.Neck.cylindricalChart ThreeModel (M := M) :=
  let V : TopologicalSpace.Opens M := Classical.choose N.exists_cylindricalChart
  let Φ : neckBuffer δ ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ V :=
    Classical.choose (Classical.choose_spec N.exists_cylindricalChart)
  { domain := neckBuffer δ
    target := V
    chart := Φ
    scale := N.scale
    scale_pos := N.scale_pos }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart

omit [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem NormalizedNeck.cylindricalChart_domain (N : NormalizedNeck h δ k) :
    N.cylindricalChart.domain = neckBuffer δ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_domain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_domain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_domain ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_domain

omit [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem NormalizedNeck.cylindricalChart_scale (N : NormalizedNeck h δ k) :
    N.cylindricalChart.scale = N.scale := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_scale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_scale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_scale ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_scale

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.cylindricalChart_target (N : NormalizedNeck h δ k) :
    (N.cylindricalChart.target : Set M) = Set.range (N.chart : neckBuffer δ → M) := by
  simp only [NormalizedNeck.cylindricalChart]
  exact (Classical.choose_spec (Classical.choose_spec N.exists_cylindricalChart)).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_target ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_target

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.cylindricalChart_chart_apply (N : NormalizedNeck h δ k)
    (x : neckBuffer δ) :
    ((N.cylindricalChart.chart x : N.cylindricalChart.target) : M) = N.chart x := by
  simp only [NormalizedNeck.cylindricalChart]
  exact (Classical.choose_spec (Classical.choose_spec N.exists_cylindricalChart)).2.1 x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_chart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_chart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_chart_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_chart_apply

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.cylindricalChart_center (N : NormalizedNeck h δ k) :
    ((N.cylindricalChart.chart ⟨(N.sphereMark, 0), by
        have := inv_pos.mpr N.delta_pos
        constructor <;> linarith⟩ : N.cylindricalChart.target) : M) = N.center :=
  (N.cylindricalChart_chart_apply _).trans N.marked

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_center then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_center"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_center ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_center

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.cylindricalChart_chart_symm_apply (N : NormalizedNeck h δ k)
    (y : N.cylindricalChart.target) :
    N.chart (N.cylindricalChart.chart.symm y) = (y : M) := by
  simp only [NormalizedNeck.cylindricalChart]
  exact (Classical.choose_spec (Classical.choose_spec N.exists_cylindricalChart)).2.2 y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_chart_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_chart_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_chart_symm_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_chart_symm_apply

omit [SigmaCompactSpace M] in
theorem NormalizedNeck.cylindricalChart_pullbackMetricCross (N : NormalizedNeck h δ k) :
    Diffeomorph.pullbackMetricCross
        (scaleMetric N.cylindricalChart.scale N.cylindricalChart.scale_pos
          (h.restrictOpen N.cylindricalChart.target))
        N.cylindricalChart.chart = N.normalizedMetric := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
      Module.finrank ℝ ThreeSpace := by
    simp [ThreeSpace]
  have hinj : ∀ y : neckBuffer δ,
      Injective (mfderiv NeckCylinderModel ThreeModel (N.chart : neckBuffer δ → M) y) :=
    fun y => injective_mfderiv_of_isImmersionAt NeckCylinderModel ThreeModel
      (N.chart : neckBuffer δ → M) y (N.chart_smooth.isImmersion.isImmersionAt y)
  have hlocal : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞
      (N.chart : neckBuffer δ → M) :=
    isLocalDiffeomorph_of_injective_mfderiv (N.chart : neckBuffer δ → M)
      N.chart_smooth.contMDiff hinj hdim
  have hEq : N.normalizedMetric =
      pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric N.scale N.scale_pos h)
        (N.chart : neckBuffer δ → M) hlocal N.chart_smooth.isEmbedding.injective := by
    apply SmoothRiemannianMetric.ext_inner
    intro y V W
    rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner, scaleMetric_inner, N.normalized_inner]
  rw [hEq]
  exact (pullbackMetricOfInjectiveLocalDiffeomorph_scale_eq_chart h (N.chart : neckBuffer δ → M)
    hlocal N.chart_smooth.isEmbedding.injective N.scale N.scale_pos
    N.cylindricalChart.target N.cylindricalChart.chart
    (fun x => N.cylindricalChart_chart_apply x)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_pullbackMetricCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_pullbackMetricCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_pullbackMetricCross ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_pullbackMetricCross

omit [SigmaCompactSpace M] in
theorem NormalizedNeck.cylindricalChart_metricCloseOn (N : NormalizedNeck h δ k)
    (hk : 2 ≤ k) : N.cylindricalChart.metricCloseOn h δ (neckClosedTest δ) := by
  intro x hx j hj
  have hcl := N.closeness
  rw [roundCylinderMetric_eq_geometry] at hcl
  rw [N.cylindricalChart_pullbackMetricCross]
  exact (metricDerivNorm_lt_of_sup_lt (isCompact_neckClosedTest δ) (hj.trans hk)
    N.normalizedMetric _ _ hcl hx).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_metricCloseOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_metricCloseOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_metricCloseOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_metricCloseOn

omit [T2Space M] [SigmaCompactSpace M] in
theorem isOpen_neckCentralDomain (δ : ℝ) : IsOpen (neckCentralDomain δ) := by
  change IsOpen {x : neckBuffer δ | -δ⁻¹ < x.1.2 ∧ x.1.2 < δ⁻¹}
  have hc : Continuous fun x : neckBuffer δ => x.1.2 := continuous_subtype_val.snd
  exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isOpen_neckCentralDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isOpen_neckCentralDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isOpen_neckCentralDomain ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isOpen_neckCentralDomain

omit [T2Space M] [SigmaCompactSpace M] in
theorem neckCentralDomain_subset_neckClosedTest (δ : ℝ) :
    neckCentralDomain δ ⊆ neckClosedTest δ :=
  fun _ hx => ⟨hx.1.le, hx.2.le⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckCentralDomain_subset_neckClosedTest then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckCentralDomain_subset_neckClosedTest"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckCentralDomain_subset_neckClosedTest ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckCentralDomain_subset_neckClosedTest

omit [SigmaCompactSpace M] in
theorem NormalizedNeck.cylindricalChart_metricCloseOn_neckCentralDomain
    (N : NormalizedNeck h δ k) (hk : 2 ≤ k) :
    N.cylindricalChart.metricCloseOn h δ (neckCentralDomain δ) :=
  fun x hx j hj =>
    N.cylindricalChart_metricCloseOn hk x (neckCentralDomain_subset_neckClosedTest δ hx) j hj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_metricCloseOn_neckCentralDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_metricCloseOn_neckCentralDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_metricCloseOn_neckCentralDomain ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.cylindricalChart_metricCloseOn_neckCentralDomain

omit [SigmaCompactSpace M] in
theorem NormalizedNeck.exists_least_ricci_field (N : NormalizedNeck h δ k) (hk : 2 ≤ k)
    (hδ : δ < 1 / 200000) :
    ∃ (ν : M → ℝ) (Y : ∀ y : M, TangentSpace ThreeModel y),
      ContMDiffOn ThreeModel 𝓘(ℝ) ∞ N.cylindricalChart.axial N.cylindricalChart.target ∧
      ContMDiffOn ThreeModel 𝓘(ℝ) ∞ ν
        (N.cylindricalChart.region (neckCentralDomain δ)) ∧
      ContMDiffOn ThreeModel ThreeModel.tangent ∞
        (fun y ↦ (⟨y, Y y⟩ : TangentBundle ThreeModel M))
        (N.cylindricalChart.region (neckCentralDomain δ)) ∧
      ∀ y ∈ N.cylindricalChart.region (neckCentralDomain δ),
        h.inner y (Y y) (Y y) = 1 ∧
        ricciSharp h y (Y y) = ν y • Y y ∧
        (∀ z : TangentSpace ThreeModel y, h.inner y z z = 1 → ν y ≤ ricciTensor h y z z) ∧
        |ν y| ≤ 5772 * N.cylindricalChart.scale * δ ∧
        Module.End.eigenspace (ricciSharp h y).toLinearMap (ν y) = Submodule.span ℝ {Y y} ∧
        0 < mvfderiv ThreeModel N.cylindricalChart.axial y (Y y) ∧
        |mvfderiv ThreeModel N.cylindricalChart.axial y (Y y) - 1| ≤ 92354 * δ :=
  N.cylindricalChart.exists_least_ricci_field h (isOpen_neckCentralDomain δ) δ hδ
    (N.cylindricalChart_metricCloseOn_neckCentralDomain hk)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.exists_least_ricci_field then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.exists_least_ricci_field"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.exists_least_ricci_field ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.exists_least_ricci_field

end

theorem endNeckNormalizedNeck_cylindricalChart_target
    (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (y : Sphere 2) :
    ((endNeckNormalizedNeck r δ hδ hδ1 hr k y).cylindricalChart.target : Set ThreeSpace) =
      Set.range fun z : neckBuffer δ => endNeckMap r δ z := by
  rw [NormalizedNeck.cylindricalChart_target, endNeckNormalizedNeck_chart]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_cylindricalChart_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_cylindricalChart_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_cylindricalChart_target ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_cylindricalChart_target

theorem endNeckNormalizedNeck_cylindricalChart_metricCloseOn
    (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (y : Sphere 2) (hk : 2 ≤ k) :
    (endNeckNormalizedNeck r δ hδ hδ1 hr k y).cylindricalChart.metricCloseOn metric δ
      (neckClosedTest δ) :=
  (endNeckNormalizedNeck r δ hδ hδ1 hr k y).cylindricalChart_metricCloseOn hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_cylindricalChart_metricCloseOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_cylindricalChart_metricCloseOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_cylindricalChart_metricCloseOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_cylindricalChart_metricCloseOn

theorem endNeckNormalizedNeck_cylindricalChart_metricCloseOn_zero
    (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (y : Sphere 2) :
    (endNeckNormalizedNeck r δ hδ hδ1 hr k y).cylindricalChart.metricCloseOn metric 0
      (neckClosedTest δ) := by
  intro x hx j hj
  rw [NormalizedNeck.cylindricalChart_pullbackMetricCross]
  have hK : (endNeckNormalizedNeck r δ hδ hδ1 hr k y).normalizedMetric =
      (Geometry.Metric.roundCylinderMetric (E := ThreeSpace) (n := 2)).restrictOpen
        (endNeckNormalizedNeck r δ hδ hδ1 hr k y).cylindricalChart.domain := by
    rw [endNeckNormalizedNeck_normalizedMetric, referenceMetric_eq_roundCylinderMetric_neckBuffer,
      roundCylinderMetric_eq_geometry]
    rfl
  rw [hK, metricDerivNorm_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_cylindricalChart_metricCloseOn_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_cylindricalChart_metricCloseOn_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_cylindricalChart_metricCloseOn_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_cylindricalChart_metricCloseOn_zero

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
