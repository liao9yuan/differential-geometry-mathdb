import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.Spectral.SmoothRepresentativeRealization
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.L2
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable (g : SmoothRiemannianMetric I M)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma norm_finiteEigenComboHs_self_le (σ : ℝ)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (W : TensorHs (I := I) (M := M) g 0 2 σ) :
    ‖finiteEigenComboHs (I := I) (M := M) g F W.coeff σ‖ ≤ ‖W‖ := by
  classical
  have hle_sq :
      ‖finiteEigenComboHs (I := I) (M := M) g F W.coeff σ‖ ^ 2 ≤ ‖W‖ ^ 2 := by
    rw [TensorHs.norm_sq_eq_tsum (I := I) (M := M)
        (finiteEigenComboHs (I := I) (M := M) g F W.coeff σ),
      TensorHs.norm_sq_eq_tsum (I := I) (M := M) W]
    refine Summable.tsum_le_tsum (fun i => ?_)
      (finiteEigenComboHs (I := I) (M := M) g F W.coeff σ).weighted_summable
      W.weighted_summable
    refine mul_le_mul_of_nonneg_left ?_ (tensorSobolevWeight_nonneg (I := I) (M := M) i σ)
    simp only [finiteEigenComboHs_coeff]
    split_ifs with hi
    · exact le_refl _
    · simpa using sq_nonneg (W.coeff i)
  calc ‖finiteEigenComboHs (I := I) (M := M) g F W.coeff σ‖
      = Real.sqrt (‖finiteEigenComboHs (I := I) (M := M) g F W.coeff σ‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖W‖ ^ 2) := Real.sqrt_le_sqrt hle_sq
    _ = ‖W‖ := Real.sqrt_sq (norm_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.norm_finiteEigenComboHs_self_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.norm_finiteEigenComboHs_self_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.norm_finiteEigenComboHs_self_le ``Submission.DifferentialGeometry.Analysis.Spectral.norm_finiteEigenComboHs_self_le

def spatialEigenProjLM (σ : ℝ) (N : ℕ) :
    TensorHs (I := I) (M := M) g 0 2 σ →ₗ[ℝ] TensorHs (I := I) (M := M) g 0 2 σ where
  toFun W :=
    finiteEigenComboHs (I := I) (M := M) g (eigenIdxFinset (I := I) (M := M) g N) W.coeff σ
  map_add' W₁ W₂ := by
    refine TensorHs.ext (funext fun i => ?_)
    simp only [TensorHs.add_coeff, finiteEigenComboHs_coeff]
    by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N <;> simp [hi]
  map_smul' c W := by
    refine TensorHs.ext (funext fun i => ?_)
    simp only [TensorHs.smul_coeff, finiteEigenComboHs_coeff, RingHom.id_apply]
    by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N <;> simp [hi]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.spatialEigenProjLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.spatialEigenProjLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.spatialEigenProjLM ``Submission.DifferentialGeometry.Analysis.Spectral.spatialEigenProjLM

def spatialEigenProj (σ : ℝ) (N : ℕ) :
    TensorHs (I := I) (M := M) g 0 2 σ →L[ℝ] TensorHs (I := I) (M := M) g 0 2 σ :=
  LinearMap.mkContinuous (spatialEigenProjLM (I := I) (M := M) g σ N) 1 (fun W => by
    rw [one_mul]
    exact norm_finiteEigenComboHs_self_le (I := I) (M := M) g σ
      (eigenIdxFinset (I := I) (M := M) g N) W)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.spatialEigenProj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.spatialEigenProj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.spatialEigenProj ``Submission.DifferentialGeometry.Analysis.Spectral.spatialEigenProj

omit [BoundarylessManifold I M] in
@[simp] lemma spatialEigenProj_apply (σ : ℝ) (N : ℕ) (W : TensorHs (I := I) (M := M) g 0 2 σ) :
    spatialEigenProj (I := I) (M := M) g σ N W =
      finiteEigenComboHs (I := I) (M := M) g (eigenIdxFinset (I := I) (M := M) g N) W.coeff σ :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.spatialEigenProj_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.spatialEigenProj_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.spatialEigenProj_apply ``Submission.DifferentialGeometry.Analysis.Spectral.spatialEigenProj_apply

omit [BoundarylessManifold I M] in
lemma norm_spatialEigenProj_le_one (σ : ℝ) (N : ℕ) :
    ‖spatialEigenProj (I := I) (M := M) g σ N‖ ≤ 1 := by
  unfold spatialEigenProj
  exact LinearMap.mkContinuous_norm_le _ (by norm_num) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.norm_spatialEigenProj_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.norm_spatialEigenProj_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.norm_spatialEigenProj_le_one ``Submission.DifferentialGeometry.Analysis.Spectral.norm_spatialEigenProj_le_one

omit [BoundarylessManifold I M] in
lemma norm_spatialEigenProj_apply_le (σ : ℝ) (N : ℕ)
    (W : TensorHs (I := I) (M := M) g 0 2 σ) :
    ‖spatialEigenProj (I := I) (M := M) g σ N W‖ ≤ ‖W‖ := by
  rw [spatialEigenProj_apply]
  exact norm_finiteEigenComboHs_self_le (I := I) (M := M) g σ
    (eigenIdxFinset (I := I) (M := M) g N) W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.norm_spatialEigenProj_apply_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.norm_spatialEigenProj_apply_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.norm_spatialEigenProj_apply_le ``Submission.DifferentialGeometry.Analysis.Spectral.norm_spatialEigenProj_apply_le

omit [BoundarylessManifold I M] in
private lemma normSq_spatialEigenProj_sub_add (σ : ℝ) (N : ℕ)
    (W : TensorHs (I := I) (M := M) g 0 2 σ) :
    (∑ i ∈ eigenIdxFinset (I := I) (M := M) g N,
        tensorSobolevWeight (I := I) (M := M) i σ * (W.coeff i) ^ 2)
      + ‖spatialEigenProj (I := I) (M := M) g σ N W - W‖ ^ 2 = ‖W‖ ^ 2 := by
  classical
  set w : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => tensorSobolevWeight (I := I) (M := M) i σ * (W.coeff i) ^ 2 with hwdef
  have hwsum : Summable w := W.weighted_summable
  have hw_nonneg : ∀ i, 0 ≤ w i := by
    intro i
    rw [hwdef]
    exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _)
  have hdiff :
      ‖spatialEigenProj (I := I) (M := M) g σ N W - W‖ ^ 2 =
        ∑' i, (if i ∈ eigenIdxFinset (I := I) (M := M) g N then 0 else w i) := by
    rw [TensorHs.norm_sq_eq_tsum (I := I) (M := M)]
    refine tsum_congr (fun i => ?_)
    have hco : (spatialEigenProj (I := I) (M := M) g σ N W - W).coeff i =
        (if i ∈ eigenIdxFinset (I := I) (M := M) g N then W.coeff i else 0) - W.coeff i := by
      rw [sub_eq_add_neg]
      simp only [TensorHs.add_coeff, TensorHs.neg_coeff, spatialEigenProj_apply,
        finiteEigenComboHs_coeff]
      ring
    rw [hco]
    by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N
    · rw [if_pos hi, if_pos hi, sub_self]; ring
    · rw [if_neg hi, if_neg hi]
      simp only [hwdef]
      ring
  have hon_sum :
      Summable (fun i => if i ∈ eigenIdxFinset (I := I) (M := M) g N then w i else 0) :=
    summable_of_ne_finset_zero (s := eigenIdxFinset (I := I) (M := M) g N)
      (fun i hi => if_neg hi)
  have hoff_nonneg :
      ∀ i, 0 ≤ (if i ∈ eigenIdxFinset (I := I) (M := M) g N then 0 else w i) := fun i => by
    by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N
    · simp [hi]
    · simpa [hi] using hw_nonneg i
  have hoff_le :
      ∀ i, (if i ∈ eigenIdxFinset (I := I) (M := M) g N then 0 else w i) ≤ w i := fun i => by
    by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N
    · simpa [hi] using hw_nonneg i
    · simp [hi]
  have hoff_sum :
      Summable (fun i => if i ∈ eigenIdxFinset (I := I) (M := M) g N then 0 else w i) :=
    Summable.of_nonneg_of_le hoff_nonneg hoff_le hwsum
  have hon_tsum :
      ∑' i, (if i ∈ eigenIdxFinset (I := I) (M := M) g N then w i else 0) =
        ∑ i ∈ eigenIdxFinset (I := I) (M := M) g N, w i := by
    rw [tsum_eq_sum (s := eigenIdxFinset (I := I) (M := M) g N) (fun i hi => if_neg hi)]
    exact Finset.sum_congr rfl (fun i hi => if_pos hi)
  calc (∑ i ∈ eigenIdxFinset (I := I) (M := M) g N, w i)
        + ‖spatialEigenProj (I := I) (M := M) g σ N W - W‖ ^ 2
      = (∑ i ∈ eigenIdxFinset (I := I) (M := M) g N, w i)
          + ∑' i, (if i ∈ eigenIdxFinset (I := I) (M := M) g N then 0 else w i) := by rw [hdiff]
    _ = (∑' i, (if i ∈ eigenIdxFinset (I := I) (M := M) g N then w i else 0))
          + ∑' i, (if i ∈ eigenIdxFinset (I := I) (M := M) g N then 0 else w i) := by rw [hon_tsum]
    _ = ∑' i, ((if i ∈ eigenIdxFinset (I := I) (M := M) g N then w i else 0)
          + (if i ∈ eigenIdxFinset (I := I) (M := M) g N then 0 else w i)) :=
        (Summable.tsum_add hon_sum hoff_sum).symm
    _ = ∑' i, w i := by
        refine tsum_congr (fun i => ?_)
        by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N <;> simp [hi]
    _ = ‖W‖ ^ 2 := (TensorHs.norm_sq_eq_tsum (I := I) (M := M) W).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.normSq_spatialEigenProj_sub_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.normSq_spatialEigenProj_sub_add target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
lemma spatialEigenProj_tendsto (σ : ℝ) (W : TensorHs (I := I) (M := M) g 0 2 σ) :
    Tendsto (fun N => spatialEigenProj (I := I) (M := M) g σ N W) _root_.Filter.atTop (𝓝 W) := by
  classical
  set w : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => tensorSobolevWeight (I := I) (M := M) i σ * (W.coeff i) ^ 2 with hwdef
  have hwsum : Summable w := W.weighted_summable
  have htotW : ∑' i, w i = ‖W‖ ^ 2 := (TensorHs.norm_sq_eq_tsum (I := I) (M := M) W).symm
  have hHS :
      Tendsto (fun s : Finset (TensorEigenIdx (I := I) (M := M) g 0 2) => ∑ i ∈ s, w i)
        atTop (𝓝 (∑' i, w i)) := hwsum.hasSum
  have hpartial :
      Tendsto (fun N => ∑ i ∈ eigenIdxFinset (I := I) (M := M) g N, w i)
        atTop (𝓝 (∑' i, w i)) :=
    hHS.comp (tendsto_eigenIdxFinset_atTop (I := I) (M := M) g)
  have hsq0 :
      Tendsto (fun N => ‖spatialEigenProj (I := I) (M := M) g σ N W - W‖ ^ 2)
        atTop (𝓝 0) := by
    have hconv :
        Tendsto (fun N => ‖W‖ ^ 2 - ∑ i ∈ eigenIdxFinset (I := I) (M := M) g N, w i)
          atTop (𝓝 (‖W‖ ^ 2 - ∑' i, w i)) := tendsto_const_nhds.sub hpartial
    rw [htotW, sub_self] at hconv
    refine hconv.congr (fun N => ?_)
    have hd := normSq_spatialEigenProj_sub_add (I := I) (M := M) g σ N W
    simp only [hwdef]
    linarith [hd]
  have hnorm0 :
      Tendsto (fun N => ‖spatialEigenProj (I := I) (M := M) g σ N W - W‖) _root_.Filter.atTop (𝓝 0) := by
    have hc := (Real.continuous_sqrt.tendsto 0).comp hsq0
    rw [Real.sqrt_zero] at hc
    refine hc.congr (fun N => ?_)
    exact Real.sqrt_sq (norm_nonneg _)
  exact tendsto_sub_nhds_zero_iff.mp (tendsto_zero_iff_norm_tendsto_zero.mpr hnorm0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.spatialEigenProj_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.spatialEigenProj_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.spatialEigenProj_tendsto ``Submission.DifferentialGeometry.Analysis.Spectral.spatialEigenProj_tendsto

def timeL2EigenProj (σ T : ℝ) (N : ℕ) :
    timeL2 (TensorHs (I := I) (M := M) g 0 2 σ) T →L[ℝ]
      timeL2 (TensorHs (I := I) (M := M) g 0 2 σ) T :=
  (spatialEigenProj (I := I) (M := M) g σ N).compLpL 2 (timeMeasure T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.timeL2EigenProj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.timeL2EigenProj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.timeL2EigenProj ``Submission.DifferentialGeometry.Analysis.Spectral.timeL2EigenProj

omit [BoundarylessManifold I M] in
lemma norm_timeL2EigenProj_le_one (σ T : ℝ) (N : ℕ) :
    ‖timeL2EigenProj (I := I) (M := M) g σ T N‖ ≤ 1 := by
  refine le_trans ?_ (norm_spatialEigenProj_le_one (I := I) (M := M) g σ N)
  exact ContinuousLinearMap.norm_compLpL_le (spatialEigenProj (I := I) (M := M) g σ N)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.norm_timeL2EigenProj_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.norm_timeL2EigenProj_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.norm_timeL2EigenProj_le_one ``Submission.DifferentialGeometry.Analysis.Spectral.norm_timeL2EigenProj_le_one

omit [BoundarylessManifold I M] in
lemma timeL2EigenProj_tendsto (σ T : ℝ) (x : timeL2 (TensorHs (I := I) (M := M) g 0 2 σ) T) :
    Tendsto (fun N => timeL2EigenProj (I := I) (M := M) g σ T N x) _root_.Filter.atTop (𝓝 x) := by
  classical
  have hcoeFn : ∀ N, ⇑(timeL2EigenProj (I := I) (M := M) g σ T N x - x)
      =ᵐ[timeMeasure T] fun t => spatialEigenProj (I := I) (M := M) g σ N (x t) - x t := by
    intro N
    have h1 := Lp.coeFn_sub (timeL2EigenProj (I := I) (M := M) g σ T N x) x
    have h2 : ⇑(timeL2EigenProj (I := I) (M := M) g σ T N x)
        =ᵐ[timeMeasure T] fun t => spatialEigenProj (I := I) (M := M) g σ N (x t) :=
      ContinuousLinearMap.coeFn_compLpL (spatialEigenProj (I := I) (M := M) g σ N) x
    filter_upwards [h1, h2] with t ht1 ht2
    rw [ht1, Pi.sub_apply, ht2]
  have hAE : ∀ᵐ t ∂(timeMeasure T), ∀ N,
      ⇑(timeL2EigenProj (I := I) (M := M) g σ T N x - x) t =
        spatialEigenProj (I := I) (M := M) g σ N (x t) - x t :=
    ae_all_iff.2 hcoeFn
  have hbound_int : _root_.MeasureTheory.Integrable (fun t => 4 * ‖x t‖ ^ 2) (timeMeasure T) :=
    ((_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable x)).mp (Lp.memLp x)).const_mul 4
  have hbound : ∀ N, ∀ᵐ t ∂(timeMeasure T),
      ‖‖⇑(timeL2EigenProj (I := I) (M := M) g σ T N x - x) t‖ ^ 2‖ ≤ 4 * ‖x t‖ ^ 2 := by
    intro N
    filter_upwards [hcoeFn N] with t ht
    rw [Real.norm_of_nonneg (by positivity), ht]
    have hle : ‖spatialEigenProj (I := I) (M := M) g σ N (x t) - x t‖ ≤ 2 * ‖x t‖ := by
      calc ‖spatialEigenProj (I := I) (M := M) g σ N (x t) - x t‖
          ≤ ‖spatialEigenProj (I := I) (M := M) g σ N (x t)‖ + ‖x t‖ := norm_sub_le _ _
        _ ≤ ‖x t‖ + ‖x t‖ := by
            gcongr
            exact norm_spatialEigenProj_apply_le (I := I) (M := M) g σ N (x t)
        _ = 2 * ‖x t‖ := by ring
    nlinarith [hle, norm_nonneg (spatialEigenProj (I := I) (M := M) g σ N (x t) - x t),
      norm_nonneg (x t)]
  have hlim : ∀ᵐ t ∂(timeMeasure T),
      Tendsto (fun N => ‖⇑(timeL2EigenProj (I := I) (M := M) g σ T N x - x) t‖ ^ 2)
        atTop (𝓝 ((fun _ => (0 : ℝ)) t)) := by
    filter_upwards [hAE] with t ht
    have hconv :
        Tendsto (fun N => spatialEigenProj (I := I) (M := M) g σ N (x t) - x t)
          atTop (𝓝 0) := by
      have h0 :
          Tendsto (fun N => spatialEigenProj (I := I) (M := M) g σ N (x t) - x t)
            atTop (𝓝 (x t - x t)) :=
        (spatialEigenProj_tendsto (I := I) (M := M) g σ (x t)).sub tendsto_const_nhds
      simpa using h0
    have hsq :
        Tendsto (fun N => ‖spatialEigenProj (I := I) (M := M) g σ N (x t) - x t‖ ^ 2)
          atTop (𝓝 0) := by
      have hn : _root_.Filter.Tendsto (fun N => ‖spatialEigenProj (I := I) (M := M) g σ N (x t) - x t‖)
          atTop (𝓝 0) := by simpa using hconv.norm
      simpa using hn.pow 2
    refine hsq.congr (fun N => ?_)
    rw [ht N]
  have hdom := _root_.MeasureTheory.tendsto_integral_of_dominated_convergence (μ := timeMeasure T)
    (F := fun N t => ‖⇑(timeL2EigenProj (I := I) (M := M) g σ T N x - x) t‖ ^ 2)
    (f := fun _ => (0 : ℝ)) (bound := fun t => 4 * ‖x t‖ ^ 2)
    (fun N => (Lp.aestronglyMeasurable _).norm.pow 2) hbound_int hbound hlim
  simp only [_root_.MeasureTheory.integral_zero] at hdom
  have hsq0 :
      Tendsto (fun N => ‖timeL2EigenProj (I := I) (M := M) g σ T N x - x‖ ^ 2) _root_.Filter.atTop (𝓝 0) :=
    hdom.congr (fun N => (norm_sq_eq_integral _).symm)
  have hnorm0 :
      Tendsto (fun N => ‖timeL2EigenProj (I := I) (M := M) g σ T N x - x‖) _root_.Filter.atTop (𝓝 0) := by
    have hc := (Real.continuous_sqrt.tendsto 0).comp hsq0
    rw [Real.sqrt_zero] at hc
    refine hc.congr (fun N => ?_)
    exact Real.sqrt_sq (norm_nonneg _)
  exact tendsto_sub_nhds_zero_iff.mp (tendsto_zero_iff_norm_tendsto_zero.mpr hnorm0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.timeL2EigenProj_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.timeL2EigenProj_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.timeL2EigenProj_tendsto ``Submission.DifferentialGeometry.Analysis.Spectral.timeL2EigenProj_tendsto

omit [BoundarylessManifold I M] in
theorem exists_timeL2EigenProjection (σ T : ℝ) :
    ∃ P : ℕ → (timeL2 (TensorHs (I := I) (M := M) g 0 2 σ) T →L[ℝ]
        timeL2 (TensorHs (I := I) (M := M) g 0 2 σ) T),
      (∀ N, ‖P N‖ ≤ 1) ∧ (∀ x, _root_.Filter.Tendsto (fun N => P N x) _root_.Filter.atTop (𝓝 x)) :=
  ⟨timeL2EigenProj (I := I) (M := M) g σ T,
    fun N => norm_timeL2EigenProj_le_one (I := I) (M := M) g σ T N,
    fun x => timeL2EigenProj_tendsto (I := I) (M := M) g σ T x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.exists_timeL2EigenProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.exists_timeL2EigenProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.exists_timeL2EigenProjection ``Submission.DifferentialGeometry.Analysis.Spectral.exists_timeL2EigenProjection

end Spectral
end Analysis
end DifferentialGeometry
