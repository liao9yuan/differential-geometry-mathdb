import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.FiniteProduct

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I M} {r s : ℕ} {a b T : ℝ}

theorem timeModeCoeff_compLpL_tensorHsInclusion (hab : a ≤ b)
    (f : timeL2 (TensorHs g r s b) T) (i : TensorEigenIdx g r s) :
    timeModeCoeff ((tensorHsInclusion hab).compLpL 2 (timeMeasure T) f) i =
      timeModeCoeff f i := by
  apply Lp.ext
  filter_upwards [timeModeCoeff_coeFn
    ((tensorHsInclusion hab).compLpL 2 (timeMeasure T) f) i,
    (tensorHsInclusion hab).coeFn_compLpL (p := 2) (μ := timeMeasure T) f,
    timeModeCoeff_coeFn f i] with t h₁ h₂ h₃
  rw [h₁, h₂, tensorHsInclusion_coeff_apply, h₃]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.timeModeCoeff_compLpL_tensorHsInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.timeModeCoeff_compLpL_tensorHsInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.timeModeCoeff_compLpL_tensorHsInclusion ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.timeModeCoeff_compLpL_tensorHsInclusion

theorem maximalRegularitySolutionField_compLpL_tensorHsInclusion
    (hab : a ≤ b) (hT : 0 ≤ T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (f : timeL2 (TensorHs g r s b) T) :
    (tensorHsInclusion (show a + 2 ≤ b + 2 by linarith)).compLpL 2 (timeMeasure T)
        (maximalRegularitySolutionField b hT f) =
      maximalRegularitySolutionField a hT
        ((tensorHsInclusion hab).compLpL 2 (timeMeasure T) f) := by
  refine timeModeCoeff_injective h_compact (fun i => ?_)
  rw [timeModeCoeff_compLpL_tensorHsInclusion,
    maximalRegularitySolutionField_timeModeCoeff (h_compact := h_compact),
    maximalRegularitySolutionField_timeModeCoeff (h_compact := h_compact)]
  unfold solutionModeCoeff
  rw [timeModeCoeff_compLpL_tensorHsInclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularitySolutionField_compLpL_tensorHsInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularitySolutionField_compLpL_tensorHsInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularitySolutionField_compLpL_tensorHsInclusion ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularitySolutionField_compLpL_tensorHsInclusion

theorem maximalRegularityDuhamelSolutionField_compLpL_tensorHsInclusion
    (hab : a ≤ b) (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs g r s (b + 2)) (f : timeL2 (TensorHs g r s b) T) :
    (tensorHsInclusion (show a + 2 ≤ b + 2 by linarith)).compLpL 2 (timeMeasure T)
        (maximalRegularityDuhamelSolutionField b hT u₀ f) =
      maximalRegularityDuhamelSolutionField a hT
        (tensorHsInclusion (show a + 2 ≤ b + 2 by linarith) u₀)
        ((tensorHsInclusion hab).compLpL 2 (timeMeasure T) f) := by
  refine timeModeCoeff_injective h_compact (fun i => ?_)
  rw [timeModeCoeff_compLpL_tensorHsInclusion,
    maximalRegularityDuhamelSolutionField, maximalRegularityDuhamelSolutionField,
    timeModeCoeff_add, timeModeCoeff_add,
    maximalRegularityHomogeneousSolutionField_timeModeCoeff hT.le,
    maximalRegularityHomogeneousSolutionField_timeModeCoeff hT.le,
    maximalRegularitySolutionField_timeModeCoeff (h_compact := h_compact),
    maximalRegularitySolutionField_timeModeCoeff (h_compact := h_compact)]
  unfold solutionModeCoeff
  rw [timeModeCoeff_compLpL_tensorHsInclusion]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelSolutionField_compLpL_tensorHsInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelSolutionField_compLpL_tensorHsInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelSolutionField_compLpL_tensorHsInclusion ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelSolutionField_compLpL_tensorHsInclusion

theorem maximalRegularityDuhamelMap_deriv_compLpL_tensorHsInclusion
    (hab : a ≤ b) (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs g r s (b + 2)) (f : timeL2 (TensorHs g r s b) T) :
    (tensorHsInclusion hab).compLpL 2 (timeMeasure T)
        (maximalRegularityDuhamelMap b hT u₀ f).deriv =
      (maximalRegularityDuhamelMap a hT
        (tensorHsInclusion (show a + 2 ≤ b + 2 by linarith) u₀)
        ((tensorHsInclusion hab).compLpL 2 (timeMeasure T) f)).deriv := by
  refine timeModeCoeff_injective h_compact (fun i => ?_)
  rw [timeModeCoeff_compLpL_tensorHsInclusion,
    maximalRegularityDuhamelMap_deriv, maximalRegularityDuhamelMap_deriv,
    timeModeCoeff_add, timeModeCoeff_add,
    maximalRegularityHomogeneousDerivField_timeModeCoeff hT.le,
    maximalRegularityHomogeneousDerivField_timeModeCoeff hT.le,
    maximalRegularityDerivField_timeModeCoeff (h_compact := h_compact),
    maximalRegularityDerivField_timeModeCoeff (h_compact := h_compact)]
  unfold derivModeCoeff
  rw [timeModeCoeff_compLpL_tensorHsInclusion]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelMap_deriv_compLpL_tensorHsInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelMap_deriv_compLpL_tensorHsInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelMap_deriv_compLpL_tensorHsInclusion ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelMap_deriv_compLpL_tensorHsInclusion

theorem maximalRegularityDuhamelMap_toFun_tensorHsInclusion
    (hab : a ≤ b) (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : TensorHs g r s (b + 2)) (f : timeL2 (TensorHs g r s b) T)
    {t : ℝ} (ht : t ∈ _root_.Set.Icc 0 T) :
    tensorHsInclusion hab ((maximalRegularityDuhamelMap b hT u₀ f).toFun t) =
      (maximalRegularityDuhamelMap a hT
        (tensorHsInclusion (show a + 2 ≤ b + 2 by linarith) u₀)
        ((tensorHsInclusion hab).compLpL 2 (timeMeasure T) f)).toFun t := by
  let J := tensorHsInclusion (g := g) (r := r) (s := s) hab
  let u := maximalRegularityDuhamelMap b hT u₀ f
  let v := maximalRegularityDuhamelMap a hT
    (tensorHsInclusion (show a + 2 ≤ b + 2 by linarith) u₀)
    (J.compLpL 2 (timeMeasure T) f)
  change J (u.toFun t) = v.toFun t
  have hder : (fun s => J (u.deriv s)) =ᵐ[timeMeasure T] v.deriv := by
    have h := J.coeFn_compLpL (p := 2) (μ := timeMeasure T) u.deriv
    rw [show J.compLpL 2 (timeMeasure T) u.deriv = v.deriv from
      maximalRegularityDuhamelMap_deriv_compLpL_tensorHsInclusion hab hT h_compact u₀ f] at h
    exact h.symm
  have hint : (∫ s in (0 : ℝ)..t, J (u.deriv s)) = ∫ s in (0 : ℝ)..t, v.deriv s := by
    apply intervalIntegral.integral_congr_ae
    apply _root_.MeasureTheory.ae_imp_of_ae_restrict
    exact hder.filter_mono (_root_.MeasureTheory.ae_mono (Measure.restrict_mono
      (uIoc_subset_uIcc.trans (_root_.Set.uIcc_subset_Icc ⟨le_rfl, hT.le⟩ ht)) le_rfl))
  have hinit : J u.initial = v.initial := by
    dsimp only [u, v]
    rw [maximalRegularityDuhamelMap_initial, maximalRegularityDuhamelMap_initial]
    apply TensorHs.ext
    rfl
  rw [timeH1.toFun_apply, timeH1.toFun_apply, map_add, hinit,
    ← J.intervalIntegral_comp_comm (u.intervalIntegrable_deriv ⟨le_rfl, hT.le⟩ ht), hint]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelMap_toFun_tensorHsInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelMap_toFun_tensorHsInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelMap_toFun_tensorHsInclusion ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelMap_toFun_tensorHsInclusion

variable {ι : Type*} [Fintype ι]

theorem maximalRegularityDuhamelVectorMap_toFun_tensorHsInclusion
    (hab : a ≤ b) (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (b + 2)))
    (f : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s b)) T)
    {t : ℝ} (ht : t ∈ _root_.Set.Icc 0 T) :
    ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := r) (s := s) hab)
        ((maximalRegularityDuhamelVectorMap hT u₀ f).toFun t) =
      (maximalRegularityDuhamelVectorMap hT
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := r) (s := s)
            (show a + 2 ≤ b + 2 by linarith)) u₀)
        ((ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := r) (s := s) hab)).compLpL 2 (timeMeasure T) f)).toFun t := by
  simp only [maximalRegularityDuhamelVectorMap, timeH1.piLpEquiv_symm_toFun _ ht,
    Lp.piLpEquiv_compLpL (𝕜 := ℝ)]
  apply PiLp.ext
  intro i
  exact maximalRegularityDuhamelMap_toFun_tensorHsInclusion hab hT h_compact (u₀ i)
    (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) f i) ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelVectorMap_toFun_tensorHsInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelVectorMap_toFun_tensorHsInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelVectorMap_toFun_tensorHsInclusion ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelVectorMap_toFun_tensorHsInclusion

theorem maximalRegularityDuhamelVectorField_compLpL_tensorHsInclusion
    (hab : a ≤ b) (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (b + 2)))
    (f : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s b)) T) :
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := r) (s := s)
        (show a + 2 ≤ b + 2 by linarith))).compLpL 2 (timeMeasure T)
          (maximalRegularityDuhamelVectorField hT u₀ f) =
      maximalRegularityDuhamelVectorField hT
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := r) (s := s)
            (show a + 2 ≤ b + 2 by linarith)) u₀)
        ((ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := r) (s := s) hab)).compLpL 2 (timeMeasure T) f) := by
  apply (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).injective
  rw [Lp.piLpEquiv_compLpL (𝕜 := ℝ)]
  simp only [maximalRegularityDuhamelVectorField, LinearIsometryEquiv.apply_symm_apply,
    Lp.piLpEquiv_compLpL (𝕜 := ℝ)]
  apply PiLp.ext
  intro i
  exact maximalRegularityDuhamelSolutionField_compLpL_tensorHsInclusion hab hT h_compact
    (u₀ i) (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) f i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelVectorField_compLpL_tensorHsInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelVectorField_compLpL_tensorHsInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelVectorField_compLpL_tensorHsInclusion ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.maximalRegularityDuhamelVectorField_compLpL_tensorHsInclusion

theorem eq_maximalRegularityDuhamelVectorField_of_tensorHsInclusion_eq
    (hab : a ≤ b) (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (b + 2)))
    (FL : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T)
    (FH : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s b)) T)
    (U : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s (b + 2))) T) :
    let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := r) (s := s) hab)
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := r) (s := s)
        (show a + 2 ≤ b + 2 by linarith))
    J.compLpL 2 (timeMeasure T) FH = FL →
    K.compLpL 2 (timeMeasure T) U = maximalRegularityDuhamelVectorField hT (K u₀) FL →
    U = maximalRegularityDuhamelVectorField hT u₀ FH := by
  intro J K hF hU
  have hD : K.compLpL 2 (timeMeasure T)
      (maximalRegularityDuhamelVectorField hT u₀ FH) =
        maximalRegularityDuhamelVectorField hT (K u₀) FL := by
    rw [← hF]
    exact maximalRegularityDuhamelVectorField_compLpL_tensorHsInclusion hab hT hc u₀ FH
  have heq : K.compLpL 2 (timeMeasure T) U = K.compLpL 2 (timeMeasure T)
      (maximalRegularityDuhamelVectorField hT u₀ FH) := hU.trans hD.symm
  apply Lp.ext
  filter_upwards [K.coeFn_compLpL U,
    K.coeFn_compLpL (maximalRegularityDuhamelVectorField hT u₀ FH)] with t ht hu
  apply PiLp.ext
  intro i
  apply tensorHsInclusion_injective (g := g) (r := r) (s := s)
    (show a + 2 ≤ b + 2 by linarith)
  rw [heq] at ht
  exact congrArg (fun z => z i) (ht.symm.trans hu)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.eq_maximalRegularityDuhamelVectorField_of_tensorHsInclusion_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.eq_maximalRegularityDuhamelVectorField_of_tensorHsInclusion_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.eq_maximalRegularityDuhamelVectorField_of_tensorHsInclusion_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.eq_maximalRegularityDuhamelVectorField_of_tensorHsInclusion_eq

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
