import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Multiplication
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Operator.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter _root_.Set

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  {T : ℝ}

omit [CompleteSpace X] [CompleteSpace Y] in
private theorem timeH1_toFunL2_eq_timeOp
    (A : ℝ → X →L[ℝ] Y)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal) (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (u : timeH1 X T) (w : timeH1 Y T)
    (hw : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, w.toFun t = A t (u.toFun t)) :
    w.toFunL2 = timeOp A hA C hC u.toFunL2 := by
  apply Lp.ext
  filter_upwards [coeFn_ofContinuousOn w.continuousOn_toFun,
    timeOp_apply_ae A hA C hC u.toFunL2,
    coeFn_ofContinuousOn u.continuousOn_toFun,
    _root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with t hwt hAt hut ht
  change w.toFunL2 t = w.toFun t at hwt
  change u.toFunL2 t = u.toFun t at hut
  rw [hwt, hAt, hut]
  exact hw t ht

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1_toFunL2_eq_timeOp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1_toFunL2_eq_timeOp target :: scope.openDecls } }

omit [CompleteSpace X] [CompleteSpace Y] in
private theorem timeH1_deriv_eq_timeOp_add
    (A A' : ℝ → X →L[ℝ] Y)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T))
    (hA' : _root_.MeasureTheory.AEStronglyMeasurable A' (timeMeasure T))
    (C C' : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hC' : ∀ᵐ t ∂timeMeasure T, ‖A' t‖ ≤ (C' : ℝ))
    (u : timeH1 X T) (w : timeH1 Y T)
    (hwd : w.deriv =ᵐ[timeMeasure T]
      (fun t => A' t (u.toFun t) + A t (u.deriv t))) :
    w.deriv = timeOp A' hA' C' hC' u.toFunL2 +
      timeOp A hA C hC u.deriv := by
  apply Lp.ext
  filter_upwards [hwd,
    Lp.coeFn_add (timeOp A' hA' C' hC' u.toFunL2)
      (timeOp A hA C hC u.deriv),
    timeOp_apply_ae A' hA' C' hC' u.toFunL2,
    timeOp_apply_ae A hA C hC u.deriv,
    coeFn_ofContinuousOn u.continuousOn_toFun] with t hwt hsum hAt hAu hut
  change u.toFunL2 t = u.toFun t at hut
  rw [hwt, hsum, Pi.add_apply, hAt, hAu, hut]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1_deriv_eq_timeOp_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1_deriv_eq_timeOp_add target :: scope.openDecls } }

omit [CompleteSpace X] [CompleteSpace Y] in
private theorem time_coefficients_bounded
    {A : ℝ → X →L[ℝ] Y} (hA : ContDiffOn ℝ 1 A (_root_.Set.Icc (0 : ℝ) T)) :
    _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T) ∧
      ∃ C : NNReal, ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ) := by
  have hcont := hA.continuousOn
  have hmeas : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T) :=
    hcont.aestronglyMeasurable measurableSet_Icc
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let B : ℝ := _root_.Max.max K 0
  refine ⟨hmeas, Real.toNNReal B, ?_⟩
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.coe_toNNReal _ (le_max_right _ _)]
  exact (hK t ht).trans (le_max_left _ _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.time_coefficients_bounded
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.time_coefficients_bounded target :: scope.openDecls } }

omit [CompleteSpace X] [CompleteSpace Y] in
private theorem time_deriv_coefficients_bounded
    {A : ℝ → X →L[ℝ] Y} (hA : ContDiffOn ℝ 1 A (_root_.Set.Icc (0 : ℝ) T)) :
    _root_.MeasureTheory.AEStronglyMeasurable (_root_.deriv A) (timeMeasure T) ∧
      ∃ C : NNReal, ∀ᵐ t ∂timeMeasure T, ‖_root_.deriv A t‖ ≤ (C : ℝ) := by
  by_cases hT : 0 < T
  · let v : ℝ → X →L[ℝ] Y := derivWithin A (_root_.Set.Icc (0 : ℝ) T)
    have hv : ContinuousOn v (_root_.Set.Icc (0 : ℝ) T) :=
      hA.continuousOn_derivWithin (uniqueDiffOn_Icc hT) le_rfl
    have hvd : v =ᵐ[timeMeasure T] _root_.deriv A := by
      unfold timeMeasure
      rw [← _root_.MeasureTheory.restrict_Ioo_eq_restrict_Icc]
      filter_upwards [_root_.MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with t ht
      exact derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
    refine ⟨(hv.aestronglyMeasurable measurableSet_Icc).congr hvd, ?_⟩
    obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hv
    refine ⟨Real.toNNReal (_root_.Max.max K 0), ?_⟩
    filter_upwards [hvd, _root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht htmem
    rw [← ht, Real.coe_toNNReal _ (le_max_right _ _)]
    exact (hK t htmem).trans (le_max_left _ _)
  · rw [timeMeasure_eq_zero_of_nonpos (le_of_not_gt hT)]
    exact ⟨aestronglyMeasurable_zero_measure _, 0, by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.time_deriv_coefficients_bounded
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.time_deriv_coefficients_bounded target :: scope.openDecls } }

private def timeOpH1Aux
    (A : ℝ → X →L[ℝ] Y)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T))
    (hA' : _root_.MeasureTheory.AEStronglyMeasurable (_root_.deriv A) (timeMeasure T))
    (C C' : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hC' : ∀ᵐ t ∂timeMeasure T, ‖_root_.deriv A t‖ ≤ (C' : ℝ)) :
    timeH1 X T →L[ℝ] timeH1 Y T :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ Y (timeL2 Y T)).symm.toContinuousLinearMap.comp
    (((A 0).comp (timeH1.trace0 X T)).prod
      ((timeOp (_root_.deriv A) hA' C' hC').comp (timeH1.toTimeL2 X T) +
        (timeOp A hA C hC).comp (timeH1.timeDeriv X T)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1Aux
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1Aux target :: scope.openDecls } }

private theorem timeOpH1Aux_spec
    (hT : 0 ≤ T) {A : ℝ → X →L[ℝ] Y}
    (hAcont : ContDiffOn ℝ 1 A (_root_.Set.Icc (0 : ℝ) T))
    (hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T))
    (hA' : _root_.MeasureTheory.AEStronglyMeasurable (_root_.deriv A) (timeMeasure T))
    (C C' : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hC' : ∀ᵐ t ∂timeMeasure T, ‖_root_.deriv A t‖ ≤ (C' : ℝ))
    (u : timeH1 X T) :
    (timeOpH1Aux A hA hA' C C' hC hC' u).initial = A 0 u.initial ∧
      (∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
        (timeOpH1Aux A hA hA' C C' hC hC' u).toFun t = A t (u.toFun t)) ∧
      (timeOpH1Aux A hA hA' C C' hC hC' u).deriv =ᵐ[timeMeasure T]
        (fun t => _root_.deriv A t (u.toFun t) + A t (u.deriv t)) := by
  obtain ⟨w, hwi, hw, hwd⟩ := exists_timeH1_clm_apply_of_contDiffOn hT hAcont u
  have hdeq := timeH1_deriv_eq_timeOp_add A (_root_.deriv A) hA hA' C C' hC hC' u w hwd
  have heq : timeOpH1Aux A hA hA' C C' hC hC' u = w := by
    apply timeH1.ext
    · exact hwi.symm
    · exact hdeq.symm
  rw [heq]
  exact ⟨hwi, hw, hwd⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1Aux_spec
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1Aux_spec target :: scope.openDecls } }


def timeOpH1 (A : ℝ → X →L[ℝ] Y)
    (hA : ContDiffOn ℝ 1 A (_root_.Set.Icc (0 : ℝ) T)) : timeH1 X T →L[ℝ] timeH1 Y T :=
  timeOpH1Aux A (time_coefficients_bounded hA).1 (time_deriv_coefficients_bounded hA).1
    (time_coefficients_bounded hA).2.choose (time_deriv_coefficients_bounded hA).2.choose
    (time_coefficients_bounded hA).2.choose_spec
    (time_deriv_coefficients_bounded hA).2.choose_spec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1 ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1

omit [CompleteSpace Y] in
@[simp] theorem timeOpH1_initial (A : ℝ → X →L[ℝ] Y)
    (hA : ContDiffOn ℝ 1 A (_root_.Set.Icc (0 : ℝ) T)) (u : timeH1 X T) :
    (timeOpH1 A hA u).initial = A 0 u.initial := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1_initial ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1_initial

theorem timeOpH1_toFun (A : ℝ → X →L[ℝ] Y)
    (hA : ContDiffOn ℝ 1 A (_root_.Set.Icc (0 : ℝ) T)) (u : timeH1 X T)
    {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) T) :
    (timeOpH1 A hA u).toFun t = A t (u.toFun t) := by
  exact (timeOpH1Aux_spec (ht.1.trans ht.2) hA
    (time_coefficients_bounded hA).1 (time_deriv_coefficients_bounded hA).1
    (time_coefficients_bounded hA).2.choose (time_deriv_coefficients_bounded hA).2.choose
    (time_coefficients_bounded hA).2.choose_spec
    (time_deriv_coefficients_bounded hA).2.choose_spec u).2.1 t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1_toFun ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1_toFun

omit [CompleteSpace Y] in
theorem timeOpH1_deriv_ae (A : ℝ → X →L[ℝ] Y)
    (hA : ContDiffOn ℝ 1 A (_root_.Set.Icc (0 : ℝ) T)) (u : timeH1 X T) :
    (timeOpH1 A hA u).deriv =ᵐ[timeMeasure T]
      (fun t => _root_.deriv A t (u.toFun t) + A t (u.deriv t)) := by
  let hAm := (time_coefficients_bounded hA).1
  let hA'm := (time_deriv_coefficients_bounded hA).1
  let C := (time_coefficients_bounded hA).2.choose
  let C' := (time_deriv_coefficients_bounded hA).2.choose
  let hC := (time_coefficients_bounded hA).2.choose_spec
  let hC' := (time_deriv_coefficients_bounded hA).2.choose_spec
  change (timeOp (_root_.deriv A) hA'm C' hC' u.toFunL2 +
    timeOp A hAm C hC u.deriv : timeL2 Y T) =ᵐ[timeMeasure T] _
  filter_upwards [Lp.coeFn_add (timeOp (_root_.deriv A) hA'm C' hC' u.toFunL2)
      (timeOp A hAm C hC u.deriv),
    timeOp_apply_ae (_root_.deriv A) hA'm C' hC' u.toFunL2,
    timeOp_apply_ae A hAm C hC u.deriv,
    coeFn_ofContinuousOn u.continuousOn_toFun] with t hsum hA't hAt hut
  change u.toFunL2 t = u.toFun t at hut
  rw [hsum, Pi.add_apply, hA't, hAt, hut]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1_deriv_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1_deriv_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1_deriv_ae ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1_deriv_ae

theorem toTimeL2_comp_timeOpH1 (A : ℝ → X →L[ℝ] Y)
    (hA : ContDiffOn ℝ 1 A (_root_.Set.Icc (0 : ℝ) T))
    (hAm : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal) (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ)) :
    (timeH1.toTimeL2 Y T).comp (timeOpH1 A hA) =
      (timeOp A hAm C hC).comp (timeH1.toTimeL2 X T) := by
  apply ContinuousLinearMap.ext
  intro u
  exact timeH1_toFunL2_eq_timeOp A hAm C hC u (timeOpH1 A hA u)
    (fun _ ht => timeOpH1_toFun A hA u ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.toTimeL2_comp_timeOpH1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.toTimeL2_comp_timeOpH1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.toTimeL2_comp_timeOpH1 ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.toTimeL2_comp_timeOpH1

omit [CompleteSpace Y] in
theorem timeDeriv_comp_timeOpH1 (A : ℝ → X →L[ℝ] Y)
    (hA : ContDiffOn ℝ 1 A (_root_.Set.Icc (0 : ℝ) T))
    (hAm : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T))
    (hA'm : _root_.MeasureTheory.AEStronglyMeasurable (_root_.deriv A) (timeMeasure T))
    (C C' : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hC' : ∀ᵐ t ∂timeMeasure T, ‖_root_.deriv A t‖ ≤ (C' : ℝ)) :
    (timeH1.timeDeriv Y T).comp (timeOpH1 A hA) =
      (timeOp (_root_.deriv A) hA'm C' hC').comp (timeH1.toTimeL2 X T) +
        (timeOp A hAm C hC).comp (timeH1.timeDeriv X T) := by
  apply ContinuousLinearMap.ext
  intro u
  exact timeH1_deriv_eq_timeOp_add A (_root_.deriv A) hAm hA'm C C' hC hC'
    u (timeOpH1 A hA u) (timeOpH1_deriv_ae A hA u)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeDeriv_comp_timeOpH1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeDeriv_comp_timeOpH1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeDeriv_comp_timeOpH1 ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeDeriv_comp_timeOpH1

omit [CompleteSpace Y] in
theorem timeOpH1_norm_le (A : ℝ → X →L[ℝ] Y)
    (hA : ContDiffOn ℝ 1 A (_root_.Set.Icc (0 : ℝ) T))
    (C C' : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hC' : ∀ᵐ t ∂timeMeasure T, ‖_root_.deriv A t‖ ≤ (C' : ℝ)) :
    ‖timeOpH1 A hA‖ ≤ ‖A 0‖ + (C' : ℝ) * Real.sqrt T * (1 + Real.sqrt T) + C := by
  apply ContinuousLinearMap.opNorm_le_bound
  · positivity
  intro u
  let w := timeOpH1 A hA u
  have hwi : ‖w.initial‖ ≤ ‖A 0‖ * ‖u‖ := by
    rw [show w.initial = A 0 u.initial from timeOpH1_initial A hA u]
    exact ((A 0).le_opNorm u.initial).trans
      (mul_le_mul_of_nonneg_left u.norm_initial_le (norm_nonneg _))
  have hAm := (time_coefficients_bounded hA).1
  have hA'm := (time_deriv_coefficients_bounded hA).1
  have hwd : w.deriv = timeOp (_root_.deriv A) hA'm C' hC' u.toFunL2 +
      timeOp A hAm C hC u.deriv :=
    timeH1_deriv_eq_timeOp_add A (_root_.deriv A) hAm hA'm C C' hC hC'
      u w (timeOpH1_deriv_ae A hA u)
  have hnorm (B : ℝ → X →L[ℝ] Y) (hBm : _root_.MeasureTheory.AEStronglyMeasurable B (timeMeasure T))
      (D : NNReal) (hD : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ (D : ℝ)) (v : timeL2 X T) :
      ‖timeOp B hBm D hD v‖ ≤ (D : ℝ) * ‖v‖ :=
    ((timeOp B hBm D hD).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (timeOp_norm_le B hBm D hD) (norm_nonneg _))
  have hwdnorm : ‖w.deriv‖ ≤
      ((C' : ℝ) * Real.sqrt T * (1 + Real.sqrt T) + C) * ‖u‖ := by
    rw [hwd]
    calc
      ‖timeOp (_root_.deriv A) hA'm C' hC' u.toFunL2 + timeOp A hAm C hC u.deriv‖ ≤
          (C' : ℝ) * ‖u.toFunL2‖ + (C : ℝ) * ‖u.deriv‖ :=
        (norm_add_le _ _).trans (add_le_add (hnorm _ _ _ _ _) (hnorm _ _ _ _ _))
      _ ≤ (C' : ℝ) * (Real.sqrt T * ((1 + Real.sqrt T) * ‖u‖)) + C * ‖u‖ :=
        add_le_add (mul_le_mul_of_nonneg_left u.norm_toFunL2_le C'.coe_nonneg)
          (mul_le_mul_of_nonneg_left u.norm_deriv_le C.coe_nonneg)
      _ = _ := by ring
  have hnormsum : ‖w‖ ≤ ‖w.initial‖ + ‖w.deriv‖ := by
    have hsq := w.norm_sq_eq
    nlinarith [norm_nonneg w, norm_nonneg w.initial, norm_nonneg w.deriv,
      mul_nonneg (norm_nonneg w.initial) (norm_nonneg w.deriv)]
  exact hnormsum.trans ((add_le_add hwi hwdnorm).trans_eq (by ring))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1_norm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOpH1_norm_le

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
