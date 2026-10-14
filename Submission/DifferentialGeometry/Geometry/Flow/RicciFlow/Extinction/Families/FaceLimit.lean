import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.OrderClosed

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.MeasureTheory _root_.Filter
open scoped _root_.Topology
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

theorem antitoneOn_Ioo_le_endpoints {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (_root_.Set.Icc a b)) (ha : AntitoneOn f (_root_.Set.Ioo a b)) :
    f b ≤ f a := by
  have hmid : ∀ y ∈ _root_.Set.Ioo a b, f y ≤ f a := by
    intro y hy
    have hx : a ∈ closure (_root_.Set.Ioo a y) := by
      rw [closure_Ioo hy.1.ne]
      exact ⟨le_rfl, hy.1.le⟩
    exact ContinuousWithinAt.closure_le hx continuousWithinAt_const
      ((hf a ⟨le_rfl, hab.le⟩).mono (fun x hx => ⟨hx.1.le, hx.2.le.trans hy.2.le⟩))
      (fun x hx => ha ⟨hx.1, hx.2.trans hy.2⟩ hy hx.2.le)
  have hb : b ∈ closure (_root_.Set.Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact ⟨hab.le, le_rfl⟩
  exact ContinuousWithinAt.closure_le hb
    ((hf b ⟨hab.le, le_rfl⟩).mono _root_.Set.Ioo_subset_Icc_self)
    continuousWithinAt_const hmid

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.antitoneOn_Ioo_le_endpoints then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.antitoneOn_Ioo_le_endpoints"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.antitoneOn_Ioo_le_endpoints ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.antitoneOn_Ioo_le_endpoints

private theorem primitive_cont {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (_root_.Set.Icc a b)) :
    ContinuousOn (fun t => ∫ r in a..t, f r) (_root_.Set.Icc a b) := by
  intro t ht
  let : Fact (t ∈ _root_.Set.Icc a b) := ⟨ht⟩
  have hi : IntervalIntegrable f _root_.MeasureTheory.MeasureSpace.volume a t :=
    (hf.mono (_root_.Set.uIcc_subset_Icc ⟨le_rfl, ht.1.trans ht.2⟩ ht)).intervalIntegrable
  have hm : StronglyMeasurableAtFilter f (𝓝[_root_.Set.Icc a b] t) volume :=
    ⟨Icc a b, self_mem_nhdsWithin, hf.aestronglyMeasurable measurableSet_Icc⟩
  exact (intervalIntegral.integral_hasDerivWithinAt_right hi hm (hf t ht)).continuousWithinAt

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.primitive_cont
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.primitive_cont target :: scope.openDecls } }

theorem weighted_comparison_le_endpoints {rho w : ℝ → ℝ} {a b k : ℝ} (hab : a < b)
    (hrho : ContinuousOn rho (_root_.Set.Icc a b)) (hw : ContinuousOn w (_root_.Set.Icc a b))
    (hint : AntitoneOn
      (fun t => Real.exp (∫ r in a..t, rho r) * w t +
        k * ∫ v in a..t, Real.exp (∫ r in a..v, rho r)) (_root_.Set.Ioo a b)) :
    Real.exp (∫ r in a..b, rho r) * w b ≤
      w a - k * ∫ v in a..b, Real.exp (∫ r in a..v, rho r) := by
  have hi : ContinuousOn (fun t => Real.exp (∫ r in a..t, rho r)) (_root_.Set.Icc a b) :=
    Real.continuous_exp.comp_continuousOn (primitive_cont hrho)
  have hc := (hi.mul hw).add ((primitive_cont hi).const_mul k)
  have he := antitoneOn_Ioo_le_endpoints hab hc hint
  change Real.exp (∫ r in a..b, rho r) * w b +
      k * (∫ v in a..b, Real.exp (∫ r in a..v, rho r)) ≤
    Real.exp (∫ r in a..a, rho r) * w a +
      k * (∫ v in a..a, Real.exp (∫ r in a..v, rho r)) at he
  simp only [intervalIntegral.integral_same, Real.exp_zero, one_mul, _root_.MulZeroClass.mul_zero, add_zero] at he
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.weighted_comparison_le_endpoints then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.weighted_comparison_le_endpoints"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.weighted_comparison_le_endpoints ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.weighted_comparison_le_endpoints

theorem integrated_comparison_le_endpoints {rho w : ℝ → ℝ} {a b k : ℝ} (hab : a < b)
    (hrho : ContinuousOn rho (_root_.Set.Icc a b)) (hw : ContinuousOn w (_root_.Set.Icc a b))
    (hint : ∀ s ∈ _root_.Set.Ioo a b, ∀ t ∈ _root_.Set.Ioo s b,
      Real.exp (∫ r in s..t, rho r) * w t ≤
        w s - k * ∫ v in s..t, Real.exp (∫ r in s..v, rho r)) :
    Real.exp (∫ r in a..b, rho r) * w b ≤
      w a - k * ∫ v in a..b, Real.exp (∫ r in a..v, rho r) := by
  let F : ℝ → ℝ → ℝ := fun s t => Real.exp (∫ r in s..t, rho r)
  have hInt {s t : ℝ} (hs : s ∈ _root_.Set.Icc a b) (ht : t ∈ _root_.Set.Icc a b) :
      IntervalIntegrable rho _root_.MeasureTheory.MeasureSpace.volume s t :=
    (hrho.mono (_root_.Set.uIcc_subset_Icc hs ht)).intervalIntegrable
  have hFcont : ContinuousOn (F a) (_root_.Set.Icc a b) :=
    Real.continuous_exp.comp_continuousOn (primitive_cont hrho)
  have hFInt {s t : ℝ} (hs : s ∈ _root_.Set.Icc a b) (ht : t ∈ _root_.Set.Icc a b) :
      IntervalIntegrable (F a) _root_.MeasureTheory.MeasureSpace.volume s t :=
    (hFcont.mono (_root_.Set.uIcc_subset_Icc hs ht)).intervalIntegrable
  apply weighted_comparison_le_endpoints hab hrho hw
  intro s hs t ht hst
  rcases eq_or_lt_of_le hst with rfl | hst
  · exact le_rfl
  have ha : a ∈ _root_.Set.Icc a b := ⟨le_rfl, hab.le⟩
  have hs' : s ∈ _root_.Set.Icc a b := _root_.Set.Ioo_subset_Icc_self hs
  have ht' : t ∈ _root_.Set.Icc a b := _root_.Set.Ioo_subset_Icc_self ht
  have hcoc (r : ℝ) (hr : r ∈ _root_.Set.Icc s t) : F a r = F a s * F s r := by
    have hr' : r ∈ _root_.Set.Icc a b := ⟨hs.1.le.trans hr.1, hr.2.trans ht.2.le⟩
    dsimp only [F]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hInt ha hs') (hInt hs' hr'), Real.exp_add]
  have hJ : (∫ r in a..t, F a r) = (∫ r in a..s, F a r) +
      F a s * ∫ r in s..t, F s r := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hFInt ha hs') (hFInt hs' ht')]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [_root_.Set.uIcc_of_le hst.le] at hr
    exact hcoc r hr
  have h := hint s hs t ⟨hst, ht.2⟩
  change F s t * w t ≤ w s - k * ∫ r in s..t, F s r at h
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (∫ r in a..s, rho r)).le
  change F a t * w t + k * (∫ r in a..t, F a r) ≤
    F a s * w s + k * (∫ r in a..s, F a r)
  rw [hcoc t ⟨hst.le, le_rfl⟩, hJ]
  change F a s * (F s t * w t) ≤
    F a s * (w s - k * ∫ r in s..t, F s r) at hm
  nlinarith [hm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.integrated_comparison_le_endpoints then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.integrated_comparison_le_endpoints"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.integrated_comparison_le_endpoints ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.integrated_comparison_le_endpoints

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
