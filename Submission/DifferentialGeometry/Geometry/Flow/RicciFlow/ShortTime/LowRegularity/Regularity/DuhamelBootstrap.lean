import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Forcing.SmoothIdentification
import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleParabolicTraceEnergy
import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.FieldIdentification

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Parabolic
    DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

def duhamelCross (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    {T : ℝ} (hT : 0 < T)
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    CrossScaleField (I := I) (M := M) g r s a T where
  highRegularity := maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ f
  lowRegularity := maximalRegularityDuhamelMap (I := I) (M := M) a hT u₀ f
  link := solutionField_toFun_ae (I := I) (M := M) hT
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) u₀ f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelCross ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelCross

omit [NeZero (Module.finrank ℝ E)]
  [BoundarylessManifold I M] in
theorem crossRepr_toFun
    (u : CrossScaleField (I := I) (M := M) g r s a T)
    (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 1 by linarith) (u.repr t) = u.lowRegularity.toFun t := by
  refine TensorHs.ext ?_
  funext i
  rw [tensorHsInclusion_coeff_apply, u.repr_coeff hT ht]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.crossRepr_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.crossRepr_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.crossRepr_toFun ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.crossRepr_toFun

omit [NeZero (Module.finrank ℝ E)]
  [BoundarylessManifold I M] in
theorem crossRepr_hi_ae
    (u : CrossScaleField (I := I) (M := M) g r s a T)
    (hT : 0 < T) :
    (fun t => u.repr t) =ᵐ[timeMeasure T]
      fun t => tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith) (u.highRegularity t) := by
  filter_upwards [u.ae_coeffFun_eq_hiL2,
    ae_restrict_mem (μ := _root_.MeasureTheory.MeasureSpace.volume) measurableSet_Icc] with t hcoeff ht
  refine TensorHs.ext ?_
  funext i
  rw [u.repr_coeff hT ht, tensorHsInclusion_coeff_apply]
  exact hcoeff i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.crossRepr_hi_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.crossRepr_hi_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.crossRepr_hi_ae ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.crossRepr_hi_ae

omit [BoundarylessManifold I M] in
theorem duhamelRepr_toFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    {T : ℝ} (hT : 0 < T)
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 1 by linarith)
        ((duhamelCross (I := I) (M := M) g r s a hT u₀ f).repr t) =
      (maximalRegularityDuhamelMap (I := I) (M := M) a hT u₀ f).toFun t := by
  simpa only [duhamelCross] using
    crossRepr_toFun (I := I) (M := M)
      (duhamelCross (I := I) (M := M) g r s a hT u₀ f) hT ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelRepr_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelRepr_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelRepr_toFun ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelRepr_toFun

omit [BoundarylessManifold I M] in
theorem duhamelRepr_field_ae
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    {T : ℝ} (hT : 0 < T)
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    (fun t => (duhamelCross (I := I) (M := M) g r s a hT u₀ f).repr t)
      =ᵐ[timeMeasure T]
        fun t => tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a + 1 ≤ a + 2 by linarith)
          (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ f t) := by
  simpa only [duhamelCross] using
    crossRepr_hi_ae (I := I) (M := M)
      (duhamelCross (I := I) (M := M) g r s a hT u₀ f) hT

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelRepr_field_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelRepr_field_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelRepr_field_ae ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelRepr_field_ae

omit [BoundarylessManifold I M] in
theorem duhamelRepr_meas
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    {T : ℝ} (hT : 0 < T)
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    _root_.MeasureTheory.AEStronglyMeasurable
      (fun t => (duhamelCross (I := I) (M := M)
        g r s a hT u₀ f).repr t)
      (timeMeasure T) := by
  have hfield : _root_.MeasureTheory.AEStronglyMeasurable
      (fun t => tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith)
        (maximalRegularityDuhamelSolutionField (I := I) (M := M)
          a hT u₀ f t))
      (timeMeasure T) :=
    (tensorHsInclusion (I := I) (M := M)
      (g := g) (r := r) (s := s)
      (show a + 1 ≤ a + 2 by linarith)).continuous.comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable
          (maximalRegularityDuhamelSolutionField (I := I) (M := M)
            a hT u₀ f))
  exact hfield.congr
    (duhamelRepr_field_ae (I := I) (M := M)
      g r s a hT u₀ f).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelRepr_meas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelRepr_meas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelRepr_meas ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelRepr_meas

omit [NeZero (Module.finrank ℝ E)]
  [BoundarylessManifold I M] in
theorem crossRepr_ball
    (u : CrossScaleField (I := I) (M := M) g r s a T)
    (hT : 0 < T) {R : ℝ} (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂(timeMeasure T),
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith) (u.highRegularity t)‖ ≤ R) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ‖u.repr t‖ ≤ R := by
  have hrepr := crossRepr_hi_ae (I := I) (M := M) u hT
  have hzero :
      (fun t => _root_.Max.max (‖u.repr t‖ ^ 2 - R ^ 2) 0) =ᵐ[timeMeasure T]
        (fun _ => (0 : ℝ)) := by
    filter_upwards [hrepr, hball] with t htrepr htball
    rw [htrepr]
    have hsq :
        ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (show a + 1 ≤ a + 2 by linarith) (u.highRegularity t)‖ ^ 2 ≤ R ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hR).2 htball
    exact max_eq_right (sub_nonpos.mpr hsq)
  have hcont : ContinuousOn (fun t => _root_.Max.max (‖u.repr t‖ ^ 2 - R ^ 2) 0)
      (Set.Icc (0 : ℝ) T) :=
    ((u.continuousOn_normSq_repr hT).sub continuousOn_const).sup continuousOn_const
  have hregular : Set.Icc (0 : ℝ) T ⊆
      closure (interior (Set.Icc (0 : ℝ) T)) := by
    rw [interior_Icc, closure_Ioo (ne_of_lt hT)]
  have heqOn : Set.EqOn (fun t => _root_.Max.max (‖u.repr t‖ ^ 2 - R ^ 2) 0)
      (fun _ => (0 : ℝ)) (Set.Icc (0 : ℝ) T) :=
    MeasureTheory.Measure.eqOn_of_ae_eq hzero hcont continuousOn_const hregular
  intro t ht
  have hmax := heqOn ht
  have hsub : ‖u.repr t‖ ^ 2 - R ^ 2 ≤ 0 := by
    have hle := le_max_left (‖u.repr t‖ ^ 2 - R ^ 2) 0
    exact hle.trans_eq hmax
  exact (sq_le_sq₀ (norm_nonneg _) hR).1 (sub_nonpos.mp hsub)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.crossRepr_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.crossRepr_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.crossRepr_ball ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.crossRepr_ball

omit [BoundarylessManifold I M] in
theorem duhamelRepr_ball
    (g₀ : SmoothRiemannianMetric I M) {T R : ℝ}
    (hT : 0 < T)
    (f : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2
      ((1 : ℕ) : ℝ)) T)
    (hR : 0 ≤ R)
    (hstate : ∀ᵐ t ∂(timeMeasure T),
      maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
          (0 : TensorHs (I := I) (M := M) g₀ 0 2
            (((1 : ℕ) : ℝ) + 2)) f t ∈
        lowerState (I := I) (M := M) g₀ 1 R) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖(duhamelCross (I := I) (M := M) g₀ 0 2
        ((1 : ℕ) : ℝ) hT 0 f).repr t‖ ≤ R := by
  apply crossRepr_ball (I := I) (M := M)
    (duhamelCross (I := I) (M := M) g₀ 0 2
      ((1 : ℕ) : ℝ) hT 0 f) hT hR
  filter_upwards [hstate] with t ht
  exact ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelRepr_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelRepr_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelRepr_ball ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelRepr_ball

omit [BoundarylessManifold I M] in
theorem duhamelRepr_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    {T : ℝ} (hT : 0 < T)
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    {R : ℝ} (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂(timeMeasure T),
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith)
        (maximalRegularityDuhamelSolutionField (I := I) (M := M)
          a hT u₀ f t)‖ ≤ R) :
    _root_.MeasureTheory.MemLp
      (fun t => (duhamelCross (I := I) (M := M)
        g r s a hT u₀ f).repr t)
      2 (timeMeasure T) := by
  refine MemLp.of_bound
    (duhamelRepr_meas (I := I) (M := M)
      g r s a hT u₀ f) R ?_
  have hrepr := crossRepr_ball (I := I) (M := M)
    (duhamelCross (I := I) (M := M)
      g r s a hT u₀ f) hT hR hball
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem (μ := _root_.MeasureTheory.MeasureSpace.volume) measurableSet_Icc] with t ht
  exact hrepr t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelRepr_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelRepr_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelRepr_memLp ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelRepr_memLp

def duhamelReprL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    {T : ℝ} (hT : 0 < T)
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    {R : ℝ} (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂(timeMeasure T),
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith)
        (maximalRegularityDuhamelSolutionField (I := I) (M := M)
          a hT u₀ f t)‖ ≤ R) :
    timeL2 (TensorHs (I := I) (M := M) g r s (a + 1)) T :=
  (duhamelRepr_memLp (I := I) (M := M)
    g r s a hT u₀ f hR hball).toLp
      (fun t => (duhamelCross (I := I) (M := M)
        g r s a hT u₀ f).repr t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelReprL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelReprL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelReprL2 ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelReprL2

omit [BoundarylessManifold I M] in
theorem duhamelReprL2_ae
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    {T : ℝ} (hT : 0 < T)
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    {R : ℝ} (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂(timeMeasure T),
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith)
        (maximalRegularityDuhamelSolutionField (I := I) (M := M)
          a hT u₀ f t)‖ ≤ R) :
    duhamelReprL2 (I := I) (M := M)
        g r s a hT u₀ f hR hball =ᵐ[timeMeasure T]
      fun t => (duhamelCross (I := I) (M := M)
        g r s a hT u₀ f).repr t :=
  (duhamelRepr_memLp (I := I) (M := M)
    g r s a hT u₀ f hR hball).coeFn_toLp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelReprL2_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelReprL2_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelReprL2_ae ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelReprL2_ae

omit [BoundarylessManifold I M] in
theorem duhamelReprL2_ae_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    {T : ℝ} (hT : 0 < T)
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    {R : ℝ} (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂(timeMeasure T),
      ‖tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith)
        (maximalRegularityDuhamelSolutionField (I := I) (M := M)
          a hT u₀ f t)‖ ≤ R) :
    ∀ᵐ t ∂(timeMeasure T),
      ‖duhamelReprL2 (I := I) (M := M)
        g r s a hT u₀ f hR hball t‖ ≤ R := by
  filter_upwards [
    duhamelReprL2_ae (I := I) (M := M)
      g r s a hT u₀ f hR hball,
    duhamelRepr_field_ae (I := I) (M := M)
      g r s a hT u₀ f,
    hball] with t hcoe hrepr ht
  rw [hcoe, hrepr]
  exact ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelReprL2_ae_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelReprL2_ae_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelReprL2_ae_le ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.duhamelReprL2_ae_le

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

def duhamelCross (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    {T : ℝ} (hT : 0 < T)
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    CrossScaleField (I := I) (M := M) g r s a T :=
  IntrinsicSpectral.duhamelCross (I := I) (M := M)
    g r s a hT u₀ f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.duhamelCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.duhamelCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.duhamelCross ``Submission.DifferentialGeometry.PDE.RicciFlow.duhamelCross

omit [NeZero (Module.finrank ℝ E)]
  [BoundarylessManifold I M] in
theorem crossRepr_toFun
    (u : CrossScaleField (I := I) (M := M) g r s a T)
    (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 1 by linarith) (u.repr t) = u.lowRegularity.toFun t :=
  IntrinsicSpectral.crossRepr_toFun (I := I) (M := M) u hT ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.crossRepr_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.crossRepr_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.crossRepr_toFun ``Submission.DifferentialGeometry.PDE.RicciFlow.crossRepr_toFun

omit [NeZero (Module.finrank ℝ E)]
  [BoundarylessManifold I M] in
theorem crossRepr_hi_ae
    (u : CrossScaleField (I := I) (M := M) g r s a T)
    (hT : 0 < T) :
    (fun t => u.repr t) =ᵐ[timeMeasure T]
      fun t => tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith) (u.highRegularity t) :=
  IntrinsicSpectral.crossRepr_hi_ae (I := I) (M := M) u hT

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.crossRepr_hi_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.crossRepr_hi_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.crossRepr_hi_ae ``Submission.DifferentialGeometry.PDE.RicciFlow.crossRepr_hi_ae

omit [BoundarylessManifold I M] in
theorem duhamelRepr_toFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    {T : ℝ} (hT : 0 < T)
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 1 by linarith)
        ((duhamelCross (I := I) (M := M) g r s a hT u₀ f).repr t) =
      (maximalRegularityDuhamelMap (I := I) (M := M) a hT u₀ f).toFun t := by
  simpa only [duhamelCross] using
    IntrinsicSpectral.duhamelRepr_toFun (I := I) (M := M)
      g r s a hT u₀ f ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.duhamelRepr_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.duhamelRepr_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.duhamelRepr_toFun ``Submission.DifferentialGeometry.PDE.RicciFlow.duhamelRepr_toFun

omit [BoundarylessManifold I M] in
theorem duhamelRepr_field_ae
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    {T : ℝ} (hT : 0 < T)
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (TensorHs (I := I) (M := M) g r s a) T) :
    (fun t => (duhamelCross (I := I) (M := M)
        g r s a hT u₀ f).repr t) =ᵐ[timeMeasure T]
      fun t => tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith)
        (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ f t) := by
  simpa only [duhamelCross] using
    IntrinsicSpectral.duhamelRepr_field_ae (I := I) (M := M)
      g r s a hT u₀ f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.duhamelRepr_field_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.duhamelRepr_field_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.duhamelRepr_field_ae ``Submission.DifferentialGeometry.PDE.RicciFlow.duhamelRepr_field_ae

omit [NeZero (Module.finrank ℝ E)]
  [BoundarylessManifold I M] in
theorem crossRepr_ball
    (u : CrossScaleField (I := I) (M := M) g r s a T)
    (hT : 0 < T) {R : ℝ} (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂(timeMeasure T),
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith) (u.highRegularity t)‖ ≤ R) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ‖u.repr t‖ ≤ R :=
  IntrinsicSpectral.crossRepr_ball (I := I) (M := M) u hT hR hball

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.crossRepr_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.crossRepr_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.crossRepr_ball ``Submission.DifferentialGeometry.PDE.RicciFlow.crossRepr_ball

omit [BoundarylessManifold I M] in
theorem duhamelRepr_ball
    (g₀ : SmoothRiemannianMetric I M) {T R : ℝ}
    (hT : 0 < T)
    (f : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2
      ((1 : ℕ) : ℝ)) T)
    (hR : 0 ≤ R)
    (hstate : ∀ᵐ t ∂(timeMeasure T),
      maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
          (0 : TensorHs (I := I) (M := M) g₀ 0 2
            (((1 : ℕ) : ℝ) + 2)) f t ∈
        lowerState (I := I) (M := M) g₀ 1 R) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖(duhamelCross (I := I) (M := M) g₀ 0 2
        ((1 : ℕ) : ℝ) hT 0 f).repr t‖ ≤ R := by
  simpa only [duhamelCross] using
    IntrinsicSpectral.duhamelRepr_ball (I := I) (M := M)
      g₀ hT f hR hstate

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.duhamelRepr_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.duhamelRepr_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.duhamelRepr_ball ``Submission.DifferentialGeometry.PDE.RicciFlow.duhamelRepr_ball

end DifferentialGeometry.PDE.RicciFlow

end
