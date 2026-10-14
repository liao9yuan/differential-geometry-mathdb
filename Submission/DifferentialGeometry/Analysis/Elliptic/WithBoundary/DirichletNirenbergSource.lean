import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletNirenbergIntegration
import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.SourceBounds
import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletNirenbergOperator

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Metric _root_.Filter
open scoped _root_.ENNReal _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev (diffQuot)
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]
local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry target :: scope.openDecls } }

private theorem abs_integral_mul_nirenbergTestFunction_chart_le
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (v : H1ComplDirichlet q) {f η : EuStd → ℝ}
    (hf : _root_.MeasureTheory.MemLp f 2 (volume.restrict Ω))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηb : ∀ x, |η x| ≤ 1) (k : Fin (Module.finrank ℝ EuN)) {N : ℝ}
    (hηd : ∀ x, |fderiv ℝ η x (EuclideanSpace.single k 1)| ≤ N)
    {ε : ℝ} (hε : 0 < ε) (h : ℝ) (hroom : _root_.Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    let U := fun z => H1ComplDirichletToLp q v
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    |∫ z in Ω, f z * nirenbergTestFunction k h η U z| ≤
      ε * (∫ z, (η z * diffQuot k h (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k v) z)^2) +
      (2 * ε)⁻¹ * (∫ z in Ω, (f z)^2) +
      4 * ε * N^2 * (∫ z in tsupport η, (diffQuot k h U z)^2) := by
  exact abs_integral_mul_nirenbergTestFunction_le_local hΩ
    (memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs v).memLp
    (Lp.memLp (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k v)) hf k
    (hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k v)
    hη hηc hηb hηd hε h hroom

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.abs_integral_mul_nirenbergTestFunction_chart_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.abs_integral_mul_nirenbergTestFunction_chart_le target :: scope.openDecls } }

theorem abs_integral_mul_dirichletNirenbergTest_le
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (v : H1ComplDirichlet q) {f η : EuStd → ℝ}
    (hf : _root_.MeasureTheory.MemLp f 2 (volume.restrict Ω))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηb : ∀ x, |η x| ≤ 1) (k : Fin (Module.finrank ℝ EuN)) {N : ℝ}
    (hηd : ∀ x, |fderiv ℝ η x (EuclideanSpace.single k 1)| ≤ N)
    {ε : ℝ} (hε : 0 < ε) (h : ℝ) (hroom : _root_.Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    let x := fun z => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
    let U := fun z => H1ComplDirichletToLp q v (x z)
    |∫ z in Ω, f z * H1ComplDirichletToLp q
        (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroom v) (x z)| ≤
      ε * (∫ z, (η z * diffQuot k h (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k v) z)^2) +
      (2 * ε)⁻¹ * (∫ z in Ω, (f z)^2) +
      4 * ε * N^2 * (∫ z in tsupport η, (diffQuot k h U z)^2) := by
  intro x U
  have heq : (∫ z in Ω, f z * H1ComplDirichletToLp q
        (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroom v) (x z)) =
      ∫ z in Ω, f z * nirenbergTestFunction k h η U z := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [dirichletNirenbergTest_chartInverse_coeFn q α hΩ hΩc hΩs v hη hηc k h hroom] with z hz
    exact congrArg (fun r => f z * r) hz
  rw [heq]
  exact abs_integral_mul_nirenbergTestFunction_chart_le q α hΩ hΩc hΩs v hf hη hηc hηb k hηd hε h hroom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.abs_integral_mul_dirichletNirenbergTest_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.abs_integral_mul_dirichletNirenbergTest_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.abs_integral_mul_dirichletNirenbergTest_le ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.abs_integral_mul_dirichletNirenbergTest_le

theorem abs_integral_mul_smoothMul_dirichletNirenbergTest_le_of_mul_chartDensity
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, chartDensity (I := I_hs) q α
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) *
        φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) = 1)
    (f : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q))
    (v : H1ComplDirichlet q) {η : EuStd → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηb : ∀ x, |η x| ≤ 1) (k : Fin (Module.finrank ℝ EuN)) {N : ℝ}
    (hηd : ∀ x, |fderiv ℝ η x (EuclideanSpace.single k 1)| ≤ N)
    {ε : ℝ} (hε : 0 < ε) (h : ℝ) (hroom : Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    let x := fun z => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
    let U := fun z => H1ComplDirichletToLp q v (x z)
    |∫ y, f y * H1ComplDirichletToLp q (smoothMulH1ComplDirichlet q φ
        (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroom v)) y
        ∂riemannianVolumeMeasure (I := I_hs) (M := M) q| ≤
      ε * (∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k v) z)^2) +
      (2 * ε)⁻¹ * (∫ z in Ω, (f (x z))^2) +
      4 * ε * N^2 * (∫ z in tsupport η,
        (DifferentialGeometry.Analysis.Sobolev.diffQuot k h U z)^2) := by
  intro x U
  let Ntest := nirenbergTestFunction k h η U
  have hNsupport : tsupport Ntest ⊆ Ω :=
    (nirenbergTestFunction_tsupport_subset_cthickening k h η U).trans hroom
  have heq : (∫ y, f y * H1ComplDirichletToLp q (smoothMulH1ComplDirichlet q φ
        (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroom v)) y
        ∂riemannianVolumeMeasure (I := I_hs) (M := M) q) =
      ∫ z in Ω, f (x z) * H1ComplDirichletToLp q
        (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroom v) (x z) := by
    rw [integral_mul_smoothMul_dirichletNirenbergTest_eq_integral_chart q α hΩ hΩc hΩs
      hη hηc φ k h hroom f (Lp.stronglyMeasurable f).measurable v]
    change (∫ z, chartDensity q α (x z) * f (x z) * φ (x z) * Ntest z) = _
    have hr : (∫ z in Ω, chartDensity q α (x z) * f (x z) * φ (x z) * Ntest z) =
        ∫ z, chartDensity q α (x z) * f (x z) * φ (x z) * Ntest z := by
      apply _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      have hNz : Ntest z = 0 := image_eq_zero_of_notMem_tsupport (fun hzs => hz (hNsupport hzs))
      rw [hNz, _root_.MulZeroClass.mul_zero]
    rw [← hr]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem hΩ.measurableSet,
      dirichletNirenbergTest_chartInverse_coeFn q α hΩ hΩc hΩs v hη hηc k h hroom]
      with z hz hNz
    change H1ComplDirichletToLp q _ (x z) = Ntest z at hNz
    rw [hNz]
    calc
      _ = (chartDensity q α (x z) * φ (x z)) * (f (x z) * Ntest z) := by ring
      _ = _ := by rw [hφ z hz, one_mul]
  rw [heq]
  have hf : _root_.MeasureTheory.MemLp (fun z => f (x z)) 2 (volume.restrict Ω) :=
    (_root_.MeasureTheory.memLp_congr_ae (chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc
      (hΩs.trans (_root_.Set.image_mono interior_subset)) 2 f)).mp (Lp.memLp _)
  exact abs_integral_mul_dirichletNirenbergTest_le q α hΩ hΩc hΩs v hf
    hη hηc hηb k hηd hε h hroom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.abs_integral_mul_smoothMul_dirichletNirenbergTest_le_of_mul_chartDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.abs_integral_mul_smoothMul_dirichletNirenbergTest_le_of_mul_chartDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.abs_integral_mul_smoothMul_dirichletNirenbergTest_le_of_mul_chartDensity ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.abs_integral_mul_smoothMul_dirichletNirenbergTest_le_of_mul_chartDensity

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
