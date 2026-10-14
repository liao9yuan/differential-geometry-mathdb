import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Interval _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace Real X]
  [CompleteSpace X]

private def tentSlope (T c : Real) (z : X) : Real → X :=
  Set.piecewise (_root_.Set.Iic c) (fun _ ↦ c⁻¹ • z)
    (fun _ ↦ -(T - c)⁻¹ • z)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.tentSlope
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.tentSlope target :: scope.openDecls } }

omit [CompleteSpace X] in
private theorem tentSlope_mem (T c : Real) (z : X) :
    MemLp (tentSlope T c z) 2 (timeMeasure T) := by
  exact MemLp.piecewise measurableSet_Iic (_root_.MeasureTheory.memLp_const _)
    (_root_.MeasureTheory.memLp_const _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.tentSlope_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.tentSlope_mem target :: scope.openDecls } }

namespace timeH1

noncomputable def tent (T c : Real) (z : X) : timeH1 X T :=
  mk 0 ((tentSlope_mem T c z).toLp (tentSlope T c z))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent

omit [CompleteSpace X] in
theorem tent_deriv (T c : Real) (z : X) :
    (tent T c z).deriv =ᵐ[timeMeasure T] tentSlope T c z := by
  exact (tentSlope_mem T c z).coeFn_toLp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_deriv ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_deriv

omit [CompleteSpace X] in
@[simp] theorem tent_initial (T c : Real) (z : X) :
    (tent T c z).initial = 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_initial ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_initial

omit [CompleteSpace X] in
theorem tent_deriv_left {T c : Real} (z : X) (hcT : c < T) :
    (tent T c z).deriv =ᵐ[volume.restrict (_root_.Set.Ioo (0 : Real) c)]
      fun _ ↦ c⁻¹ • z := by
  have hsub : _root_.Set.Ioo (0 : Real) c ⊆ _root_.Set.Icc (0 : Real) T := by
    intro t ht
    exact ⟨ht.1.le, ht.2.le.trans hcT.le⟩
  have hle : volume.restrict (_root_.Set.Ioo (0 : Real) c) ≤ timeMeasure T := by
    unfold timeMeasure
    exact Measure.restrict_mono hsub le_rfl
  have h := (tent_deriv T c z).filter_mono (_root_.MeasureTheory.ae_mono hle)
  filter_upwards [h, _root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht htc
  rw [ht]
  exact (_root_.Set.Iic c).piecewise_eq_of_mem _ _
    (show t ∈ _root_.Set.Iic c from htc.2.le)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_deriv_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_deriv_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_deriv_left ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_deriv_left

omit [CompleteSpace X] in
theorem tent_deriv_right {T c : Real} (z : X) (hc : 0 < c) :
    (tent T c z).deriv =ᵐ[volume.restrict (_root_.Set.Ioo c T)]
      fun _ ↦ -(T - c)⁻¹ • z := by
  have hsub : _root_.Set.Ioo c T ⊆ _root_.Set.Icc (0 : Real) T := by
    intro t ht
    exact ⟨hc.le.trans ht.1.le, ht.2.le⟩
  have hle : volume.restrict (_root_.Set.Ioo c T) ≤ timeMeasure T := by
    unfold timeMeasure
    exact Measure.restrict_mono hsub le_rfl
  have h := (tent_deriv T c z).filter_mono (_root_.MeasureTheory.ae_mono hle)
  filter_upwards [h, _root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht htc
  rw [ht]
  exact (_root_.Set.Iic c).piecewise_eq_of_notMem _ _
    (show t ∉ _root_.Set.Iic c from not_le.mpr htc.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_deriv_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_deriv_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_deriv_right ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_deriv_right

theorem tent_toFun_left {T c t : Real} (z : X) (hcT : c < T)
    (ht : t ∈ _root_.Set.Icc (0 : Real) c) :
    (tent T c z).toFun t = (t / c) • z := by
  have hsub : _root_.Set.uIoc (0 : Real) t ⊆ _root_.Set.Icc (0 : Real) T := by
    intro s hs
    rw [_root_.Set.uIoc_of_le ht.1] at hs
    exact ⟨hs.1.le, (hs.2.trans ht.2).trans hcT.le⟩
  have hle : volume.restrict (_root_.Set.uIoc (0 : Real) t) ≤ timeMeasure T := by
    unfold timeMeasure
    exact Measure.restrict_mono hsub le_rfl
  have hder := (tent_deriv T c z).filter_mono (_root_.MeasureTheory.ae_mono hle)
  have hint : (∫ s in (0 : Real)..t, (tent T c z).deriv s) =
      ∫ _ in (0 : Real)..t, c⁻¹ • z := by
    apply intervalIntegral.integral_congr_ae_restrict
    filter_upwards [hder, _root_.MeasureTheory.ae_restrict_mem measurableSet_uIoc] with s hs hst
    rw [hs]
    have hsc : s ≤ c := by
      rw [_root_.Set.uIoc_of_le ht.1] at hst
      exact hst.2.trans ht.2
    exact (_root_.Set.Iic c).piecewise_eq_of_mem _ _
      (show s ∈ _root_.Set.Iic c from hsc)
  rw [toFun_apply, tent_initial, hint, intervalIntegral.integral_const,
    zero_add, sub_zero, smul_smul, div_eq_mul_inv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_toFun_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_toFun_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_toFun_left ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_toFun_left

theorem tent_node {T c : Real} (z : X) (hc : 0 < c) (hcT : c < T) :
    (tent T c z).toFun c = z := by
  rw [tent_toFun_left z hcT ⟨hc.le, le_rfl⟩, div_self hc.ne', one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_node then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_node"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_node ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_node

theorem tent_toFun_right {T c t : Real} (z : X) (hc : 0 < c) (hcT : c < T)
    (ht : t ∈ _root_.Set.Icc c T) :
    (tent T c z).toFun t = ((T - t) / (T - c)) • z := by
  have hc_mem : c ∈ _root_.Set.Icc (0 : Real) T := ⟨hc.le, hcT.le⟩
  have ht_mem : t ∈ _root_.Set.Icc (0 : Real) T := ⟨hc.le.trans ht.1, ht.2⟩
  have hsub : _root_.Set.uIoc c t ⊆ _root_.Set.Icc (0 : Real) T := by
    intro s hs
    rw [_root_.Set.uIoc_of_le ht.1] at hs
    exact ⟨hc.le.trans hs.1.le, hs.2.trans ht.2⟩
  have hle : volume.restrict (_root_.Set.uIoc c t) ≤ timeMeasure T := by
    unfold timeMeasure
    exact Measure.restrict_mono hsub le_rfl
  have hder := (tent_deriv T c z).filter_mono (_root_.MeasureTheory.ae_mono hle)
  have hint : (∫ s in c..t, (tent T c z).deriv s) =
      ∫ _ in c..t, -(T - c)⁻¹ • z := by
    apply intervalIntegral.integral_congr_ae_restrict
    filter_upwards [hder, _root_.MeasureTheory.ae_restrict_mem measurableSet_uIoc] with s hs hst
    rw [hs]
    have hcs : c < s := by
      rw [_root_.Set.uIoc_of_le ht.1] at hst
      exact hst.1
    exact (_root_.Set.Iic c).piecewise_eq_of_notMem _ _
      (show s ∉ _root_.Set.Iic c from not_le.mpr hcs)
  have hdiff := (tent T c z).toFun_sub_toFun hc_mem ht_mem
  rw [tent_node z hc hcT, hint, intervalIntegral.integral_const] at hdiff
  have hut : (tent T c z).toFun t =
      z + (t - c) • (-(T - c)⁻¹ • z) :=
    sub_eq_iff_eq_add'.mp hdiff
  rw [hut, smul_smul]
  have hcoef : 1 + (t - c) * (-(T - c)⁻¹) =
      (T - t) / (T - c) := by
    have hTc : T - c ≠ 0 := sub_ne_zero.mpr hcT.ne'
    field_simp [hTc]
    ring
  calc
    z + ((t - c) * (-(T - c)⁻¹)) • z =
        (1 + (t - c) * (-(T - c)⁻¹)) • z := by
      rw [add_smul, one_smul]
    _ = ((T - t) / (T - c)) • z := by rw [hcoef]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_toFun_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_toFun_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_toFun_right ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_toFun_right

theorem tent_end {T c : Real} (z : X) (hc : 0 < c) (hcT : c < T) :
    (tent T c z).toFun T = 0 := by
  rw [tent_toFun_right z hc hcT ⟨hcT.le, le_rfl⟩, sub_self, zero_div,
    zero_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_end then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_end"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_end ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.tent_end

end timeH1

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
