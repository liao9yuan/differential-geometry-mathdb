import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletNirenbergSource
import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSmoothMul
import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.RestrictedDiffQuotLp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.ENNReal

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

section

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem integrable_smul_and_norm_integral_le_of_bound
    {s : X → E} {G ζ : X → ℝ}
    (hs : _root_.MeasureTheory.AEStronglyMeasurable s μ) (hG : _root_.MeasureTheory.Integrable G μ)
    (hpoint : ∀ᵐ t ∂μ, ‖s t‖ ≤ G t)
    (hζ : _root_.MeasureTheory.MemLp ζ ∞ μ) (hζpos : ∀ᵐ t ∂μ, 0 ≤ ζ t) :
    _root_.MeasureTheory.Integrable (fun t => ζ t • s t) μ ∧
      ‖∫ t, ζ t • s t ∂μ‖ ≤ ∫ t, ζ t * G t ∂μ := by
  have hsint : _root_.MeasureTheory.Integrable s μ := hG.mono' hs hpoint
  refine ⟨hsint.smul_of_top_right hζ, ?_⟩
  apply _root_.MeasureTheory.norm_integral_le_of_norm_le (hG.mul_of_top_right hζ)
  filter_upwards [hpoint, hζpos] with t ht hζt
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hζt]
  exact mul_le_mul_of_nonneg_left ht hζt

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integrable_smul_and_norm_integral_le_of_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integrable_smul_and_norm_integral_le_of_bound target :: scope.openDecls } }

private theorem integrable_mul_and_abs_integral_le_of_bound
    {s A F B ζ : X → ℝ} (ε c d : ℝ)
    (hs : _root_.MeasureTheory.AEStronglyMeasurable s μ)
    (hA : _root_.MeasureTheory.Integrable A μ) (hF : _root_.MeasureTheory.Integrable F μ) (hB : _root_.MeasureTheory.Integrable B μ)
    (hpoint : ∀ᵐ t ∂μ, |s t| ≤ ε * A t + c * F t + d * B t)
    (hζ : _root_.MeasureTheory.MemLp ζ ∞ μ) (hζpos : ∀ᵐ t ∂μ, 0 ≤ ζ t) :
    _root_.MeasureTheory.Integrable (fun t => ζ t * s t) μ ∧
      |∫ t, ζ t * s t ∂μ| ≤
        ε * (∫ t, ζ t * A t ∂μ) + c * (∫ t, ζ t * F t ∂μ) +
          d * (∫ t, ζ t * B t ∂μ) := by
  have hG : _root_.MeasureTheory.Integrable (fun t => ε * A t + c * F t + d * B t) μ :=
    ((hA.const_mul ε).add (hF.const_mul c)).add (hB.const_mul d)
  have hpoint' : ∀ᵐ t ∂μ, ‖s t‖ ≤ ε * A t + c * F t + d * B t := by
    simpa only [Real.norm_eq_abs] using hpoint
  obtain ⟨hInt, hbound⟩ := integrable_smul_and_norm_integral_le_of_bound
    hs hG hpoint' hζ hζpos
  simp only [smul_eq_mul, Real.norm_eq_abs] at hInt hbound
  refine ⟨hInt, hbound.trans_eq ?_⟩
  have hεA : _root_.MeasureTheory.Integrable (fun t => ε * (ζ t * A t)) μ :=
    (hA.mul_of_top_right hζ).const_mul ε
  have hcF : _root_.MeasureTheory.Integrable (fun t => c * (ζ t * F t)) μ :=
    (hF.mul_of_top_right hζ).const_mul c
  have hdB : _root_.MeasureTheory.Integrable (fun t => d * (ζ t * B t)) μ :=
    (hB.mul_of_top_right hζ).const_mul d
  have hadd : _root_.MeasureTheory.Integrable (fun t => ε * (ζ t * A t) + c * (ζ t * F t)) μ :=
    hεA.add hcF
  calc
    (∫ t, ζ t * (ε * A t + c * F t + d * B t) ∂μ) =
        ∫ t, ε * (ζ t * A t) + c * (ζ t * F t) + d * (ζ t * B t) ∂μ := by
      apply _root_.MeasureTheory.integral_congr_ae
      exact Eventually.of_forall fun t => by ring
    _ = _ := by
      rw [_root_.MeasureTheory.integral_add hadd hdB, _root_.MeasureTheory.integral_add hεA hcF,
        _root_.MeasureTheory.integral_const_mul, _root_.MeasureTheory.integral_const_mul, _root_.MeasureTheory.integral_const_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integrable_mul_and_abs_integral_le_of_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integrable_mul_and_abs_integral_le_of_bound target :: scope.openDecls } }

end

open _root_.Manifold _root_.Set _root_.Metric
open scoped _root_.ContDiff _root_.Manifold

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev (diffQuot)
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

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem (scalarOnE_contDiffOn)

theorem abs_integral_mul_smoothMul_dirichletNirenbergTest_le
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯) (v : H1ComplDirichlet q) {f η : EuStd → ℝ}
    (hf : _root_.MeasureTheory.MemLp f 2 (volume.restrict Ω))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηb : ∀ x, |η x| ≤ 1) (k : Fin (Module.finrank ℝ EuN)) {N : ℝ}
    (hηd : ∀ x, |fderiv ℝ η x (EuclideanSpace.single k 1)| ≤ N)
    {ε : ℝ} (hε : 0 < ε) (h : ℝ) (hroom : _root_.Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    let x := fun z => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
    let U := fun z => H1ComplDirichletToLp q v (x z)
    |∫ z in Ω, f z * H1ComplDirichletToLp q (smoothMulH1ComplDirichlet q φ
        (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroom v)) (x z)| ≤
      ε * (∫ z, (η z * diffQuot k h (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k v) z)^2) +
      (2 * ε)⁻¹ * (phiSupBound q φ)^2 * (∫ z in Ω, (f z)^2) +
      4 * ε * N^2 * (∫ z in tsupport η, (diffQuot k h U z)^2) := by
  intro x U
  let P := fun z => φ (x z)
  have hP : ContinuousOn P Ω := by
    apply ((scalarOnE_contDiffOn α φ.contMDiff).comp
      (toEuclidean (E := EuN)).symm.contDiff.contDiffOn ?_).continuousOn
    intro z hz
    obtain ⟨y, hy, hyz⟩ := hΩs (subset_closure hz)
    rw [← hyz, ContinuousLinearEquiv.symm_apply_apply]
    exact interior_subset hy
  have hfP : _root_.MeasureTheory.MemLp (fun z => f z * P z) 2 (volume.restrict Ω) := by
    apply hf.of_le_mul (c := phiSupBound q φ)
      (hf.aestronglyMeasurable.mul (hP.aestronglyMeasurable hΩ.measurableSet))
    filter_upwards with z
    change ‖f z * P z‖ ≤ phiSupBound q φ * ‖f z‖
    rw [norm_mul, mul_comm, Real.norm_eq_abs (P z)]
    exact mul_le_mul_of_nonneg_right (abs_phi_le_phiSupBound q φ (x z)) (norm_nonneg _)
  have hsquare : (∫ z in Ω, (f z * P z)^2) ≤
      (phiSupBound q φ)^2 * ∫ z in Ω, (f z)^2 := by
    rw [← _root_.MeasureTheory.integral_const_mul]
    apply _root_.MeasureTheory.integral_mono_ae hfP.integrable_sq (hf.integrable_sq.const_mul _)
    filter_upwards with z
    rw [mul_pow, mul_comm]
    apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    calc
      (P z)^2 = |P z|^2 := (sq_abs _).symm
      _ ≤ (phiSupBound q φ)^2 :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_phi_le_phiSupBound q φ (x z)) 2
  have heq : (∫ z in Ω, f z * H1ComplDirichletToLp q (smoothMulH1ComplDirichlet q φ
        (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroom v)) (x z)) =
      ∫ z in Ω, (f z * P z) * H1ComplDirichletToLp q
        (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroom v) (x z) := by
    rw [H1ComplDirichletToLp_smoothMulH1ComplDirichlet]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [ae_chartInverse_of_ae q α hΩ.measurableSet hΩc
      (hΩs.trans (_root_.Set.image_mono interior_subset)) (smoothMulLp_apply_coeFn q φ
        (H1ComplDirichletToLp q
          (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroom v)))] with z hz
    change smoothMulLp q φ _ (x z) = _ at hz
    rw [hz]
    exact (mul_assoc _ _ _).symm
  rw [heq]
  have hb := abs_integral_mul_dirichletNirenbergTest_le q α hΩ hΩc hΩs v hfP
    hη hηc hηb k hηd hε h hroom
  have hs := mul_le_mul_of_nonneg_left hsquare (show 0 ≤ (2 * ε)⁻¹ by positivity)
  dsimp only at hb
  nlinarith only [hb, hs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.abs_integral_mul_smoothMul_dirichletNirenbergTest_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.abs_integral_mul_smoothMul_dirichletNirenbergTest_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.abs_integral_mul_smoothMul_dirichletNirenbergTest_le ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.abs_integral_mul_smoothMul_dirichletNirenbergTest_le

private theorem integrable_integral_mul_chartValue
    {Z : Type*} [MeasurableSpace Z] {μ : _root_.MeasureTheory.Measure Z}
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (f : _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (v : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ) :
    _root_.MeasureTheory.Integrable (fun t => ∫ z in Ω, f (t, z) * H1ComplDirichletToLp q (v t)
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) μ := by
  let J : H1ComplDirichlet q →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (volume.restrict Ω) :=
    (chartRestrictionLp q α hΩ.measurableSet hΩc
      (hΩs.trans (_root_.Set.image_mono interior_subset)) 2).comp (H1ComplDirichletToLp q)
  let V := Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (J.compLpL 2 μ v)
  have hI := ((Lp.memLp f).integrable_mul (Lp.memLp V)).integral_prod_left
  apply hI.congr
  filter_upwards [Lp.uncurry_compLpL_coeFn (𝕜 := ℝ)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) J v] with t ht
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [ht, chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc
    (hΩs.trans (_root_.Set.image_mono interior_subset)) 2 (H1ComplDirichletToLp q (v t))]
      with z hz hc
  change V (t, z) = J (v t) z at hz
  change J (v t) z = _ at hc
  change f (t, z) * V (t, z) = _
  rw [hz, hc]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integrable_integral_mul_chartValue
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integrable_integral_mul_chartValue target :: scope.openDecls } }

private theorem integrable_integral_mul_chartValue_comp
    {Z : Type*} [MeasurableSpace Z] {μ : _root_.MeasureTheory.Measure Z}
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (f : _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (v : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ)
    (L : H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q) :
    _root_.MeasureTheory.Integrable (fun t => ∫ z in Ω, f (t, z) * H1ComplDirichletToLp q (L (v t))
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) μ := by
  apply (integrable_integral_mul_chartValue q α hΩ hΩc hΩs f
    (L.compLpL 2 μ v)).congr
  filter_upwards [L.coeFn_compLpL v] with t ht
  rw [ht]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integrable_integral_mul_chartValue_comp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integrable_integral_mul_chartValue_comp target :: scope.openDecls } }

private theorem integrable_integral_sq_diffQuot_chartInverse_on
    {Z : Type*} [MeasurableSpace Z] {μ : _root_.MeasureTheory.Measure Z}
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω K : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hK : MeasurableSet K) (k : Fin (Module.finrank ℝ EuN)) (h : ℝ)
    (hroom : _root_.Metric.cthickening |h| K ⊆ Ω)
    {v : Z → H1ComplDirichlet q} (hv : _root_.MeasureTheory.MemLp v 2 μ) :
    let x := fun z => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
    _root_.MeasureTheory.Integrable (fun t => ∫ z in K,
      (diffQuot k h (fun z => H1ComplDirichletToLp q (v t) (x z)) z)^2) μ := by
  intro x
  let A := (chartRestrictionLp q α hΩ.measurableSet hΩc
    (hΩs.trans (_root_.Set.image_mono interior_subset)) 2).comp (H1ComplDirichletToLp q)
  have hint := DifferentialGeometry.Analysis.Sobolev.integrable_integral_sq_diffQuot_on_comp hΩ.measurableSet hK k h hroom A hv
  apply hint.congr
  filter_upwards [] with t
  apply _root_.MeasureTheory.integral_congr_ae
  apply (DifferentialGeometry.Analysis.Sobolev.diffQuot_congr_ae_on
    hΩ.measurableSet hK k h hroom (chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc
      (hΩs.trans (_root_.Set.image_mono interior_subset)) 2 (H1ComplDirichletToLp q (v t)))).fun_comp (· ^ 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integrable_integral_sq_diffQuot_chartInverse_on
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.integrable_integral_sq_diffQuot_chartInverse_on target :: scope.openDecls } }

theorem abs_integral_mul_integral_mul_smoothMul_dirichletNirenbergTest_le
    {Z : Type*} [MeasurableSpace Z] {μ : _root_.MeasureTheory.Measure Z}
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯) (v : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ)
    (f : _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω))) {η : EuStd → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηb : ∀ x, |η x| ≤ 1) (k : Fin (Module.finrank ℝ EuN)) {N : ℝ}
    (hηd : ∀ x, |fderiv ℝ η x (EuclideanSpace.single k 1)| ≤ N)
    {ε : ℝ} (hε : 0 < ε) (h : ℝ) (hroom : _root_.Metric.cthickening |h| (tsupport η) ⊆ Ω)
    {ζ : Z → ℝ} (hζ : _root_.MeasureTheory.MemLp ζ ∞ μ) (hζpos : ∀ᵐ t ∂μ, 0 ≤ ζ t) :
    let x := fun z => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
    let U := fun t z => H1ComplDirichletToLp q (v t) (x z)
    |∫ t, ζ t * (∫ z in Ω, f (t, z) * H1ComplDirichletToLp q
        (smoothMulH1ComplDirichlet q φ
          (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroom (v t))) (x z)) ∂μ| ≤
      ε * (∫ t, ζ t * (∫ z, (η z * diffQuot k h
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (v t)) z)^2) ∂μ) +
      (2 * ε)⁻¹ * (phiSupBound q φ)^2 * (∫ t, ζ t * (∫ z in Ω, (f (t, z))^2) ∂μ) +
      4 * ε * N^2 * (∫ t, ζ t * (∫ z in tsupport η, (diffQuot k h (U t) z)^2) ∂μ) := by
  intro x U
  let L := (smoothMulH1ComplDirichlet q φ).comp
    (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroom)
  have hS := integrable_integral_mul_chartValue_comp q α hΩ hΩc hΩs f v L
  have hA := DifferentialGeometry.Analysis.Sobolev.integrable_integral_sq_cutoff_diffQuot_comp
    hΩ.measurableSet (hη.continuous.memLp_of_hasCompactSupport hηc) k h hroom
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k) (Lp.memLp v)
  have hF := (Lp.memLp f).integrable_sq.integral_prod_left
  have hB := integrable_integral_sq_diffQuot_chartInverse_on q α hΩ hΩc hΩs
    (isClosed_tsupport η).measurableSet k h hroom (Lp.memLp v)
  apply (integrable_mul_and_abs_integral_le_of_bound ε
    ((2 * ε)⁻¹ * (phiSupBound q φ)^2) (4 * ε * N^2)
    hS.aestronglyMeasurable hA hF hB ?_ hζ hζpos).2
  filter_upwards [(Lp.memLp f).prodMk_left (by norm_num)] with t ht
  exact abs_integral_mul_smoothMul_dirichletNirenbergTest_le q α hΩ hΩc hΩs
    φ (v t) ht hη hηc hηb k hηd hε h hroom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.abs_integral_mul_integral_mul_smoothMul_dirichletNirenbergTest_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.abs_integral_mul_integral_mul_smoothMul_dirichletNirenbergTest_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.abs_integral_mul_integral_mul_smoothMul_dirichletNirenbergTest_le ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.abs_integral_mul_integral_mul_smoothMul_dirichletNirenbergTest_le

theorem abs_integral_mul_integral_mul_smoothMul_dirichletNirenbergTest_le_of_mul_chartDensity
    {Z : Type*} [MeasurableSpace Z] {μ : _root_.MeasureTheory.Measure Z}
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, chartDensity (I := I_hs) q α
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) *
        φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) = 1)
    (v : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ)
    (f : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)) 2 μ)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηb : ∀ x, |η x| ≤ 1) (k : Fin (Module.finrank ℝ EuN)) {N : ℝ}
    (hηd : ∀ x, |fderiv ℝ η x (EuclideanSpace.single k 1)| ≤ N)
    {ε : ℝ} (hε : 0 < ε) (h : ℝ) (hroom : Metric.cthickening |h| (tsupport η) ⊆ Ω)
    {ζ : Z → ℝ} (hζ : _root_.MeasureTheory.MemLp ζ ∞ μ) (hζpos : ∀ᵐ t ∂μ, 0 ≤ ζ t) :
    let x := fun z => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
    let U := fun t z => H1ComplDirichletToLp q (v t) (x z)
    |∫ t, ζ t * (∫ y, f t y * H1ComplDirichletToLp q (smoothMulH1ComplDirichlet q φ
        (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroom (v t))) y
        ∂riemannianVolumeMeasure (I := I_hs) (M := M) q) ∂μ| ≤
      ε * (∫ t, ζ t * (∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (v t)) z)^2) ∂μ) +
      (2 * ε)⁻¹ * (∫ t, ζ t * (∫ z in Ω, (f t (x z))^2) ∂μ) +
      4 * ε * N^2 * (∫ t, ζ t * (∫ z in tsupport η,
        (DifferentialGeometry.Analysis.Sobolev.diffQuot k h (U t) z)^2) ∂μ) := by
  intro x U
  let L := (H1ComplDirichletToLp q).comp ((smoothMulH1ComplDirichlet q φ).comp
    (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroom))
  have hS : _root_.MeasureTheory.Integrable (fun t => ∫ y, f t y * L (v t) y
      ∂riemannianVolumeMeasure (I := I_hs) (M := M) q) μ := by
    have hi := L2.integrable_inner (𝕜 := ℝ) f (L.compLpL 2 μ v)
    apply hi.congr
    filter_upwards [L.coeFn_compLpL v] with t ht
    rw [ht, L2.inner_def]
    apply _root_.MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by simp only [Real.inner_apply]
  let R := chartRestrictionLp q α hΩ.measurableSet hΩc
    (hΩs.trans (_root_.Set.image_mono interior_subset)) 2
  let F := Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (R.compLpL 2 μ f)
  have hFc : ∀ᵐ t ∂μ, (fun z => F (t, z)) =ᵐ[volume.restrict Ω] fun z => f t (x z) := by
    filter_upwards [Lp.uncurry_compLpL_coeFn (𝕜 := ℝ) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) R f]
      with t ht
    exact ht.trans (chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc
      (hΩs.trans (_root_.Set.image_mono interior_subset)) 2 (f t))
  have hF : _root_.MeasureTheory.Integrable (fun t => ∫ z in Ω, (f t (x z))^2) μ := by
    apply (Lp.memLp F).integrable_sq.integral_prod_left.congr
    filter_upwards [hFc] with t ht
    exact _root_.MeasureTheory.integral_congr_ae (ht.mono fun z hz => congrArg (fun r : ℝ => r ^ 2) hz)
  have hA := DifferentialGeometry.Analysis.Sobolev.integrable_integral_sq_cutoff_diffQuot_comp
    hΩ.measurableSet (hη.continuous.memLp_of_hasCompactSupport hηc) k h hroom
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k) (Lp.memLp v)
  have hB := integrable_integral_sq_diffQuot_chartInverse_on q α hΩ hΩc hΩs
    (isClosed_tsupport η).measurableSet k h hroom (Lp.memLp v)
  apply (integrable_mul_and_abs_integral_le_of_bound ε ((2 * ε)⁻¹) (4 * ε * N^2)
    hS.aestronglyMeasurable hA hF hB ?_ hζ hζpos).2
  exact Filter.Eventually.of_forall fun t =>
    abs_integral_mul_smoothMul_dirichletNirenbergTest_le_of_mul_chartDensity
      q α hΩ hΩc hΩs φ hφ (f t) (v t) hη hηc hηb k hηd hε h hroom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.abs_integral_mul_integral_mul_smoothMul_dirichletNirenbergTest_le_of_mul_chartDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.abs_integral_mul_integral_mul_smoothMul_dirichletNirenbergTest_le_of_mul_chartDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.abs_integral_mul_integral_mul_smoothMul_dirichletNirenbergTest_le_of_mul_chartDensity ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.abs_integral_mul_integral_mul_smoothMul_dirichletNirenbergTest_le_of_mul_chartDensity

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
