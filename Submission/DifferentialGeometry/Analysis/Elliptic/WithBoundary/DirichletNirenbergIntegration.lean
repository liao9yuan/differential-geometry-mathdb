import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletNirenbergOperator
import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.Integration
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.ChartDensityCutoff
import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSmoothMul

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
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

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart


theorem integral_mul_smoothMul_dirichletNirenbergTest_eq_integral_chart
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (k : Fin (Module.finrank ℝ EuN)) (h : ℝ)
    (hηs : Metric.cthickening |h| (tsupport η) ⊆ Ω)
    (u : M → ℝ) (hu : Measurable u) (v : H1ComplDirichlet q) :
    let e := toEuclidean (E := EuN)
    let x := fun z => (extChartAt I_hs α).symm (e.symm z)
    (∫ y, u y *
      H1ComplDirichletToLp q (smoothMulH1ComplDirichlet q φ
        (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hηs v)) y
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) q)) =
      ∫ z, chartDensity (I := I_hs) q α (x z) * u (x z) * φ (x z) *
        nirenbergTestFunction k h η (fun z => H1ComplDirichletToLp q v (x z)) z := by
  intro e x
  let R := chartRestrictionLp q α hΩ.measurableSet hΩc
    (hΩs.trans (_root_.Set.image_mono interior_subset)) 2 (H1ComplDirichletToLp q v)
  let f := nirenbergTestFunction k h η (R : EuStd → ℝ)
  have hf : Measurable f :=
    DifferentialGeometry.Analysis.Sobolev.measurable_diffQuot k (-h)
      ((hη.continuous.measurable.pow_const 2).mul
        (DifferentialGeometry.Analysis.Sobolev.measurable_diffQuot k h (Lp.stronglyMeasurable R).measurable))
  have hfs : Function.support f ⊆ chartTargetEuclid (I := I_hs) α :=
    (subset_tsupport f).trans ((nirenbergTestFunction_tsupport_subset_cthickening k h η R).trans
      (hηs.trans (subset_closure.trans (hΩs.trans (_root_.Set.image_mono interior_subset)))))
  have htest : f =ᵐ[_root_.MeasureTheory.MeasureSpace.volume]
      nirenbergTestFunction k h η (fun z => H1ComplDirichletToLp q v (x z)) :=
    nirenbergTestFunction_congr_ae_local hΩ.measurableSet k h η hηs
      (chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc
        (hΩs.trans (_root_.Set.image_mono interior_subset)) 2 (H1ComplDirichletToLp q v))
  have hvalue : (H1ComplDirichletToLp q
      (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hηs v) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I_hs) (M := M) q] chartPullback I_hs α f :=
    (dirichletNirenbergTest_coeFn q α hΩ hΩc hΩs hη hηc k h hηs v).trans
      (chartPullback_ae_eq_of_ae_eq q α htest.symm)
  rw [H1ComplDirichletToLp_smoothMulH1ComplDirichlet]
  calc
    _ = ∫ y, (u y * φ y) * chartPullback I_hs α f y
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) q) := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [hvalue, smoothMulLp_apply_coeFn q φ (H1ComplDirichletToLp q
        (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hηs v))] with y hy hm
      rw [hm, hy]
      ring
    _ = ∫ z, chartDensity (I := I_hs) q α (x z) * (u (x z) * φ (x z)) * f z :=
      integral_mul_chartPullback_eq_integral_euclidean q α
        (hu.mul φ.contMDiff.continuous.measurable) hf hfs
    _ = _ := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [htest] with z hz
      rw [hz]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integral_mul_smoothMul_dirichletNirenbergTest_eq_integral_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integral_mul_smoothMul_dirichletNirenbergTest_eq_integral_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integral_mul_smoothMul_dirichletNirenbergTest_eq_integral_chart ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integral_mul_smoothMul_dirichletNirenbergTest_eq_integral_chart

theorem integral_mul_dirichletNirenbergTest_eq_integral_chart
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ EuN)) (h : ℝ)
    (hηs : Metric.cthickening |h| (tsupport η) ⊆ Ω)
    (u : M → ℝ) (hu : Measurable u) (v : H1ComplDirichlet q) :
    let e := toEuclidean (E := EuN)
    let x := fun z => (extChartAt I_hs α).symm (e.symm z)
    (∫ y, u y *
      H1ComplDirichletToLp q (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hηs v) y
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) q)) =
      ∫ z, chartDensity (I := I_hs) q α (x z) * u (x z) *
        nirenbergTestFunction k h η (fun z => H1ComplDirichletToLp q v (x z)) z := by
  simpa only [smoothMulH1ComplDirichlet_one, ContinuousLinearMap.id_apply,
    ContMDiffMap.coe_one, Pi.one_apply, mul_one] using
    integral_mul_smoothMul_dirichletNirenbergTest_eq_integral_chart q α hΩ hΩc hΩs
      hη hηc 1 k h hηs u hu v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integral_mul_dirichletNirenbergTest_eq_integral_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integral_mul_dirichletNirenbergTest_eq_integral_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integral_mul_dirichletNirenbergTest_eq_integral_chart ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integral_mul_dirichletNirenbergTest_eq_integral_chart

theorem integral_mul_smoothMul_dirichletNirenbergTest_eq_of_mul_chartDensity
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (φ : C^∞⟮I_hs, M; ℝ⟯) (k : Fin (Module.finrank ℝ EuN)) (h : ℝ)
    (hηs : Metric.cthickening |h| (tsupport η) ⊆ Ω)
    (hφ : ∀ z ∈ Metric.cthickening |h| (tsupport η),
      chartDensity (I := I_hs) q α ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) *
        φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) = 1)
    (u v : H1ComplDirichlet q) :
    let x := fun z => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
    (∫ y, H1ComplDirichletToLp q u y * H1ComplDirichletToLp q
      (smoothMulH1ComplDirichlet q φ
        (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hηs v)) y
      ∂(riemannianVolumeMeasure (I := I_hs) (M := M) q)) =
      -∫ z, DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun z => H1ComplDirichletToLp q u (x z)) z *
        (η z ^ 2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun z => H1ComplDirichletToLp q v (x z)) z) := by
  intro x
  let U := fun z => H1ComplDirichletToLp q u (x z)
  let V := fun z => H1ComplDirichletToLp q v (x z)
  let F := nirenbergTestFunction k h η V
  have hFs : tsupport F ⊆ Metric.cthickening |h| (tsupport η) :=
    nirenbergTestFunction_tsupport_subset_cthickening k h η V
  rw [integral_mul_smoothMul_dirichletNirenbergTest_eq_integral_chart q α hΩ hΩc hΩs
    hη hηc φ k h hηs (H1ComplDirichletToLp q u)
      (Lp.stronglyMeasurable _).measurable v]
  calc
    _ = ∫ z, U z * F z := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards with z
      by_cases hz : F z = 0
      · change _ * F z = U z * F z
        rw [hz, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.mul_zero]
      · have hφz := hφ z (hFs (subset_tsupport F hz))
        change chartDensity q α (x z) * U z * φ (x z) * F z = U z * F z
        calc
          _ = (chartDensity q α (x z) * φ (x z)) * (U z * F z) := by ring
          _ = _ := by rw [hφz, one_mul]
    _ = ∫ z in Ω, U z * F z := by
      symm
      apply _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      rw [image_eq_zero_of_notMem_tsupport (fun hs => hz (hηs (hFs hs))), _root_.MulZeroClass.mul_zero]
    _ = _ := integral_mul_nirenbergTestFunction_eq_local hΩ.measurableSet
      (memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs u).memLp
      (memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs v).memLp
      hη.continuous hηc k h hηs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integral_mul_smoothMul_dirichletNirenbergTest_eq_of_mul_chartDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integral_mul_smoothMul_dirichletNirenbergTest_eq_of_mul_chartDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integral_mul_smoothMul_dirichletNirenbergTest_eq_of_mul_chartDensity ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integral_mul_smoothMul_dirichletNirenbergTest_eq_of_mul_chartDensity

theorem exists_smoothMap_integral_mul_dirichletNirenbergTest_eq
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (r : ℝ) (hηs : Metric.cthickening r (tsupport η) ⊆ Ω) :
    ∃ φ : C^∞⟮I_hs, M; ℝ⟯, ∀ (k : Fin (Module.finrank ℝ EuN)) (h : ℝ)
      (hh : |h| ≤ r) (u v : H1ComplDirichlet q),
      let x := fun z => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
      (∫ y, H1ComplDirichletToLp q u y * H1ComplDirichletToLp q
        (smoothMulH1ComplDirichlet q φ
          (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h
            ((Metric.cthickening_mono hh _).trans hηs) v)) y
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) q)) =
        -∫ z, DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun z => H1ComplDirichletToLp q u (x z)) z *
          (η z ^ 2 * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (fun z => H1ComplDirichletToLp q v (x z)) z) := by
  obtain ⟨φ, _, hφ⟩ := exists_smoothMap_mul_chartDensity_eq_one q α hΩ
    (subset_closure.trans hΩs) (hηc.cthickening (r := r)) hηs
  refine ⟨φ, ?_⟩
  intro k h hh u v
  exact integral_mul_smoothMul_dirichletNirenbergTest_eq_of_mul_chartDensity
    q α hΩ hΩc hΩs hη hηc φ k h ((Metric.cthickening_mono hh _).trans hηs)
    (fun z hz => hφ z (Metric.cthickening_mono hh _ hz)) u v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_smoothMap_integral_mul_dirichletNirenbergTest_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_smoothMap_integral_mul_dirichletNirenbergTest_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_smoothMap_integral_mul_dirichletNirenbergTest_eq ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_smoothMap_integral_mul_dirichletNirenbergTest_eq

theorem dirichletNirenbergTest_symmetric_nonpos_of_mul_chartDensity
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (φ : C^∞⟮I_hs, M; ℝ⟯) (k : Fin (Module.finrank ℝ EuN)) (h : ℝ)
    (hηs : Metric.cthickening |h| (tsupport η) ⊆ Ω)
    (hφ : ∀ z ∈ Metric.cthickening |h| (tsupport η),
      chartDensity (I := I_hs) q α ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) *
        φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) = 1) :
      let L := (smoothMulH1ComplDirichlet q φ).comp
        (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hηs)
      let B := -(innerSL ℝ).bilinearComp (H1ComplDirichletToLp q)
        ((H1ComplDirichletToLp q).comp L)
      B.flip = B ∧ (∀ u, 0 ≤ B u u) ∧
        (∀ u v,
          let x := fun z => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
          B u v = ∫ z, η z ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun z => H1ComplDirichletToLp q u (x z)) z *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun z => H1ComplDirichletToLp q v (x z)) z) := by
  let L := (smoothMulH1ComplDirichlet q φ).comp
    (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h
      hηs)
  let B := -(innerSL ℝ).bilinearComp (H1ComplDirichletToLp q)
    ((H1ComplDirichletToLp q).comp L)
  let x := fun z => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
  have hpair (u v : H1ComplDirichlet q) :
      B u v = ∫ z, η z ^ 2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun z => H1ComplDirichletToLp q u (x z)) z *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h
          (fun z => H1ComplDirichletToLp q v (x z)) z := by
    change -_root_.Inner.inner ℝ (H1ComplDirichletToLp q u) (H1ComplDirichletToLp q (L v)) = _
    rw [L2.inner_def]
    simp only [Real.inner_apply]
    dsimp only [L, ContinuousLinearMap.comp_apply]
    rw [integral_mul_smoothMul_dirichletNirenbergTest_eq_of_mul_chartDensity
      q α hΩ hΩc hΩs hη hηc φ k h hηs hφ u v, neg_neg]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [] with z
    ring
  change B.flip = B ∧ _
  refine ⟨?_, ?_, hpair⟩
  · ext u v
    change B v u = B u v
    rw [hpair, hpair]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [] with z
    ring
  · intro u
    rw [hpair]
    apply _root_.MeasureTheory.integral_nonneg
    intro z
    change 0 ≤ η z ^ 2 *
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun z => H1ComplDirichletToLp q u (x z)) z *
      DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun z => H1ComplDirichletToLp q u (x z)) z
    rw [mul_assoc, ← sq]
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletNirenbergTest_symmetric_nonpos_of_mul_chartDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletNirenbergTest_symmetric_nonpos_of_mul_chartDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletNirenbergTest_symmetric_nonpos_of_mul_chartDensity ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.dirichletNirenbergTest_symmetric_nonpos_of_mul_chartDensity


theorem exists_smoothMap_dirichletNirenbergTest_symmetric_nonpos
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (r : ℝ) (hηs : Metric.cthickening r (tsupport η) ⊆ Ω) :
    ∃ φ : C^∞⟮I_hs, M; ℝ⟯, ∀ (k : Fin (Module.finrank ℝ EuN)) (h : ℝ)
      (hh : |h| ≤ r),
      let L := (smoothMulH1ComplDirichlet q φ).comp
        (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h
          ((Metric.cthickening_mono hh _).trans hηs))
      let B := -(innerSL ℝ).bilinearComp (H1ComplDirichletToLp q)
        ((H1ComplDirichletToLp q).comp L)
      B.flip = B ∧ (∀ u, 0 ≤ B u u) ∧
        (∀ u v,
          let x := fun z => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
          B u v = ∫ z, η z ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun z => H1ComplDirichletToLp q u (x z)) z *
            DifferentialGeometry.Analysis.Sobolev.diffQuot k h
              (fun z => H1ComplDirichletToLp q v (x z)) z) := by
  obtain ⟨φ, _, hφ⟩ := exists_smoothMap_mul_chartDensity_eq_one q α hΩ
    (subset_closure.trans hΩs) (hηc.cthickening (r := r)) hηs
  refine ⟨φ, ?_⟩
  intro k h hh
  exact dirichletNirenbergTest_symmetric_nonpos_of_mul_chartDensity q α hΩ hΩc hΩs hη hηc
    φ k h ((Metric.cthickening_mono hh _).trans hηs)
    (fun z hz => hφ z (Metric.cthickening_mono hh _ hz))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_smoothMap_dirichletNirenbergTest_symmetric_nonpos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_smoothMap_dirichletNirenbergTest_symmetric_nonpos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_smoothMap_dirichletNirenbergTest_symmetric_nonpos ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_smoothMap_dirichletNirenbergTest_symmetric_nonpos


end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
