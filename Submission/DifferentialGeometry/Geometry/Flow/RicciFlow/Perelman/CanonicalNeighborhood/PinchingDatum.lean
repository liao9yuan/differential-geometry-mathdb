import Submission.DifferentialGeometry.Geometry.Curvature.HamiltonIveyRegion
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.MaximumPrinciple
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic
import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorBounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree
open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace Perelman

structure AdmissiblePinchingFunction (Phi : Real → Real) : Prop where
  contDiff : ContDiff Real 1 Phi
  pos : ∀ s : Real, 0 < Phi s
  mono : Monotone Phi
  quotientAntitoneOn : AntitoneOn (fun s : Real => Phi s / s) (Set.Ioi 0)
  quotientTendsto : _root_.Filter.Tendsto (fun s : Real => Phi s / s) _root_.Filter.atTop (nhds 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.AdmissiblePinchingFunction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.AdmissiblePinchingFunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.AdmissiblePinchingFunction ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.AdmissiblePinchingFunction

theorem tendsto_const_div_atTop (c : Real) :
    Tendsto (fun s : Real => c / s) _root_.Filter.atTop (nhds 0) :=
  tendsto_const_nhds.div_atTop _root_.Filter.tendsto_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.tendsto_const_div_atTop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.tendsto_const_div_atTop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.tendsto_const_div_atTop ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.tendsto_const_div_atTop


theorem admissiblePinchingFunction_const {c : Real} (hc : 0 < c) :
    AdmissiblePinchingFunction (fun _ => c) where
  contDiff := contDiff_const
  pos := fun _ => hc
  mono := monotone_const
  quotientAntitoneOn := by
    intro a ha b hb hab
    have ha' : (0 : Real) < a := ha
    have hb' : (0 : Real) < b := hb
    dsimp only
    rw [div_le_div_iff₀ hb' ha']
    nlinarith
  quotientTendsto := tendsto_const_div_atTop c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.admissiblePinchingFunction_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.admissiblePinchingFunction_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.admissiblePinchingFunction_const ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.admissiblePinchingFunction_const

theorem AdmissiblePinchingFunction.add_const {Phi : Real → Real} {c : Real}
    (hPhi : AdmissiblePinchingFunction Phi) (hc : 0 ≤ c) :
    AdmissiblePinchingFunction (fun s => Phi s + c) where
  contDiff := ContDiff.add hPhi.contDiff contDiff_const
  pos := fun s => by linarith [hPhi.pos s]
  mono := fun a b hab => by
    have := hPhi.mono hab
    dsimp only
    linarith
  quotientAntitoneOn := by
    intro a ha b hb hab
    have ha' : (0 : Real) < a := ha
    have hb' : (0 : Real) < b := hb
    have h1 := hPhi.quotientAntitoneOn ha hb hab
    dsimp only at h1 ⊢
    have h2 : c / b ≤ c / a := by
      rw [div_le_div_iff₀ hb' ha']
      nlinarith
    rw [add_div, add_div]
    linarith
  quotientTendsto := by
    have heq : (fun s : Real => (Phi s + c) / s) = fun s : Real => Phi s / s + c / s := by
      funext s
      rw [add_div]
    rw [heq]
    simpa using hPhi.quotientTendsto.add (tendsto_const_div_atTop c)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.AdmissiblePinchingFunction
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.AdmissiblePinchingFunction.add_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.AdmissiblePinchingFunction.add_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.AdmissiblePinchingFunction.add_const ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.AdmissiblePinchingFunction.add_const


def rescalePinchingFunction (Q : Real) (Phi : Real → Real) : Real → Real :=
  fun u => Q⁻¹ * Phi (Q * u)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.rescalePinchingFunction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.rescalePinchingFunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.rescalePinchingFunction ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.rescalePinchingFunction

theorem rescalePinchingFunction_div {Q : Real} (hQ : 0 < Q) (Phi : Real → Real)
    {u : Real} (hu : 0 < u) :
    rescalePinchingFunction Q Phi u / u = Phi (Q * u) / (Q * u) := by
  unfold rescalePinchingFunction
  field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.rescalePinchingFunction_div then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.rescalePinchingFunction_div"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.rescalePinchingFunction_div ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.rescalePinchingFunction_div

theorem AdmissiblePinchingFunction.rescale {Phi : Real → Real}
    (hPhi : AdmissiblePinchingFunction Phi) {Q : Real} (hQ : 0 < Q) :
    AdmissiblePinchingFunction (rescalePinchingFunction Q Phi) where
  contDiff := by
    unfold rescalePinchingFunction
    exact ContDiff.mul contDiff_const
      (ContDiff.comp hPhi.contDiff (ContDiff.mul contDiff_const contDiff_id))
  pos := fun u => mul_pos (inv_pos.mpr hQ) (hPhi.pos _)
  mono := by
    intro a b hab
    unfold rescalePinchingFunction
    have hle : Phi (Q * a) ≤ Phi (Q * b) := hPhi.mono (by nlinarith)
    have hinv : (0 : Real) ≤ Q⁻¹ := le_of_lt (inv_pos.mpr hQ)
    exact mul_le_mul_of_nonneg_left hle hinv
  quotientAntitoneOn := by
    intro a ha b hb hab
    have ha' : (0 : Real) < a := ha
    have hb' : (0 : Real) < b := hb
    dsimp only
    rw [rescalePinchingFunction_div hQ Phi ha', rescalePinchingFunction_div hQ Phi hb']
    exact hPhi.quotientAntitoneOn (by simpa using mul_pos hQ ha')
      (by simpa using mul_pos hQ hb') (by nlinarith)
  quotientTendsto := by
    have hmul : _root_.Filter.Tendsto (fun u : Real => Q * u) _root_.Filter.atTop atTop :=
      Filter.Tendsto.const_mul_atTop hQ _root_.Filter.tendsto_id
    have hcomp : _root_.Filter.Tendsto (fun u : Real => Phi (Q * u) / (Q * u)) _root_.Filter.atTop (nhds 0) :=
      hPhi.quotientTendsto.comp hmul
    refine hcomp.congr' ?_
    filter_upwards [_root_.Filter.eventually_gt_atTop (0 : Real)] with u hu
    exact (rescalePinchingFunction_div hQ Phi hu).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.AdmissiblePinchingFunction.rescale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.AdmissiblePinchingFunction.rescale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.AdmissiblePinchingFunction.rescale ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.AdmissiblePinchingFunction.rescale


theorem AdmissiblePinchingFunction.rescale_le {Phi : ℝ → ℝ}
    (hPhi : AdmissiblePinchingFunction Phi) {Q : ℝ} (hQ : 1 ≤ Q) (u : ℝ) :
    rescalePinchingFunction Q Phi u ≤ Phi u := by
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  by_cases hu : 0 < u
  · have huQ : u ≤ Q * u := by nlinarith
    have hquot := hPhi.quotientAntitoneOn hu (mul_pos hQpos hu) huQ
    dsimp only at hquot
    rw [← rescalePinchingFunction_div hQpos Phi hu] at hquot
    exact (div_le_div_iff_of_pos_right hu).mp hquot
  · have hum : u ≤ 0 := le_of_not_gt hu
    have hQu : Q * u ≤ u := by nlinarith
    have hle : Phi (Q * u) ≤ Phi u := hPhi.mono hQu
    have hInv : Q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hQ
    calc
      rescalePinchingFunction Q Phi u = Q⁻¹ * Phi (Q * u) := rfl
      _ ≤ Q⁻¹ * Phi u := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hQpos.le)
      _ ≤ Phi u := by nlinarith [hPhi.pos u]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.AdmissiblePinchingFunction.rescale_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.AdmissiblePinchingFunction.rescale_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.AdmissiblePinchingFunction.rescale_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.AdmissiblePinchingFunction.rescale_le


theorem exists_forall_rescalePinchingFunction_le {Phi : Real → Real}
    (hPhi : AdmissiblePinchingFunction Phi) {eps B : Real} (heps : 0 < eps) :
    ∃ Q0 : Real, 0 < Q0 ∧ ∀ Q : Real, Q0 ≤ Q → ∀ u : Real, u ∈ Set.Icc (0 : Real) B →
      rescalePinchingFunction Q Phi u ≤ eps := by
  have hB : (0 : Real) < _root_.Max.max B 1 := lt_of_lt_of_le zero_lt_one (le_max_right B 1)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hPhi.quotientTendsto (eps / _root_.Max.max B 1) (by positivity)
  refine ⟨max 1 (_root_.Max.max N 1 / _root_.Max.max B 1), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro Q hQ0 u hu
  have hQ1 : (1 : Real) ≤ Q := le_trans (le_max_left _ _) hQ0
  have hQpos : (0 : Real) < Q := lt_of_lt_of_le zero_lt_one hQ1
  have hQB : N ≤ Q * _root_.Max.max B 1 := by
    have h1 : _root_.Max.max N 1 / _root_.Max.max B 1 ≤ Q := le_trans (le_max_right _ _) hQ0
    have h2 : _root_.Max.max N 1 ≤ Q * _root_.Max.max B 1 := by
      rw [div_le_iff₀ hB] at h1
      linarith
    exact le_trans (le_max_left N 1) h2
  have hQBpos : (0 : Real) < Q * _root_.Max.max B 1 := mul_pos hQpos hB
  have hdist := hN (Q * _root_.Max.max B 1) hQB
  rw [Real.dist_eq, sub_zero] at hdist
  have hquot : Phi (Q * _root_.Max.max B 1) / (Q * _root_.Max.max B 1) < eps / _root_.Max.max B 1 :=
    lt_of_abs_lt hdist
  have hle : Phi (Q * u) ≤ Phi (Q * _root_.Max.max B 1) := by
    refine hPhi.mono ?_
    have hub : u ≤ _root_.Max.max B 1 := le_trans hu.2 (le_max_left B 1)
    nlinarith
  have h1 : Phi (Q * _root_.Max.max B 1) < eps / _root_.Max.max B 1 * (Q * _root_.Max.max B 1) := (div_lt_iff₀ hQBpos).mp hquot
  have h2 : eps / _root_.Max.max B 1 * (Q * _root_.Max.max B 1) = eps * Q := by
    field_simp
  rw [h2] at h1
  unfold rescalePinchingFunction
  rw [inv_mul_eq_div, div_le_iff₀ hQpos]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_forall_rescalePinchingFunction_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.exists_forall_rescalePinchingFunction_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_forall_rescalePinchingFunction_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_forall_rescalePinchingFunction_le

private noncomputable def pinchingTailSlope (psi : Real → Real) (s : Real) : Real :=
  _root_.SupSet.sSup ((fun v : Real => psi v / v) '' Set.Ici (_root_.Max.max s 1))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.pinchingTailSlope
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.pinchingTailSlope target :: scope.openDecls } }

private theorem exists_quotient_lt_one {psi : Real → Real}
    (hlim : _root_.Filter.Tendsto (fun s : Real => psi s / s) _root_.Filter.atTop (nhds 0)) :
    ∃ N : Real, 1 ≤ N ∧ ∀ v : Real, N ≤ v → psi v / v < 1 := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim 1 one_pos
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  intro v hv
  have h := hN v (le_trans (le_max_left N 1) hv)
  rw [Real.dist_eq, sub_zero] at h
  exact lt_of_abs_lt h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_quotient_lt_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_quotient_lt_one target :: scope.openDecls } }

private theorem bddAbove_pinchingQuotient {psi : Real → Real} (hmono : Monotone psi)
    (hnonneg : ∀ s : Real, 0 ≤ psi s)
    (hlim : _root_.Filter.Tendsto (fun s : Real => psi s / s) _root_.Filter.atTop (nhds 0)) (s : Real) :
    BddAbove ((fun v : Real => psi v / v) '' Set.Ici (_root_.Max.max s 1)) := by
  obtain ⟨N, hN1, hN⟩ := exists_quotient_lt_one hlim
  refine ⟨max 1 (psi N), ?_⟩
  rintro y ⟨v, hv, rfl⟩
  have hv1 : (1 : Real) ≤ v := le_trans (le_max_right s 1) hv
  rcases le_total N v with h | h
  · exact le_trans (le_of_lt (hN v h)) (le_max_left _ _)
  · have h1 : psi v / v ≤ psi v := div_le_self (hnonneg v) hv1
    exact le_trans (le_trans h1 (hmono h)) (le_max_right _ _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.bddAbove_pinchingQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.bddAbove_pinchingQuotient target :: scope.openDecls } }

private theorem nonempty_pinchingQuotient (psi : Real → Real) (s : Real) :
    ((fun v : Real => psi v / v) '' Set.Ici (_root_.Max.max s 1)).Nonempty :=
  ⟨psi (_root_.Max.max s 1) / _root_.Max.max s 1, Set.mem_image_of_mem _ (le_refl (_root_.Max.max s 1))⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.nonempty_pinchingQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.nonempty_pinchingQuotient target :: scope.openDecls } }

private theorem quotient_le_pinchingTailSlope {psi : Real → Real} (hmono : Monotone psi)
    (hnonneg : ∀ s : Real, 0 ≤ psi s)
    (hlim : _root_.Filter.Tendsto (fun s : Real => psi s / s) _root_.Filter.atTop (nhds 0)) {s v : Real}
    (hv : _root_.Max.max s 1 ≤ v) :
    psi v / v ≤ pinchingTailSlope psi s :=
  le_csSup (bddAbove_pinchingQuotient hmono hnonneg hlim s) ⟨v, hv, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.quotient_le_pinchingTailSlope
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.quotient_le_pinchingTailSlope target :: scope.openDecls } }

private theorem pinchingTailSlope_nonneg {psi : Real → Real} (hmono : Monotone psi)
    (hnonneg : ∀ s : Real, 0 ≤ psi s)
    (hlim : _root_.Filter.Tendsto (fun s : Real => psi s / s) _root_.Filter.atTop (nhds 0)) (s : Real) :
    0 ≤ pinchingTailSlope psi s := by
  have h := quotient_le_pinchingTailSlope hmono hnonneg hlim (s := s) (le_refl (_root_.Max.max s 1))
  have h0 : 0 ≤ psi (_root_.Max.max s 1) / _root_.Max.max s 1 :=
    div_nonneg (hnonneg _) (le_trans zero_le_one (le_max_right s 1))
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.pinchingTailSlope_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.pinchingTailSlope_nonneg target :: scope.openDecls } }

private theorem pinchingTailSlope_antitone {psi : Real → Real} (hmono : Monotone psi)
    (hnonneg : ∀ s : Real, 0 ≤ psi s)
    (hlim : _root_.Filter.Tendsto (fun s : Real => psi s / s) _root_.Filter.atTop (nhds 0)) :
    Antitone (pinchingTailSlope psi) := by
  intro a b hab
  refine csSup_le_csSup (bddAbove_pinchingQuotient hmono hnonneg hlim a)
    (nonempty_pinchingQuotient psi b) ?_
  exact Set.image_mono (Set.Ici_subset_Ici.mpr (max_le_max hab (le_refl 1)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.pinchingTailSlope_antitone
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.pinchingTailSlope_antitone target :: scope.openDecls } }

private theorem pinchingTailSlope_tendsto {psi : Real → Real} (hmono : Monotone psi)
    (hnonneg : ∀ s : Real, 0 ≤ psi s)
    (hlim : _root_.Filter.Tendsto (fun s : Real => psi s / s) _root_.Filter.atTop (nhds 0)) :
    Tendsto (pinchingTailSlope psi) _root_.Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (eps / 2) (by positivity)
  refine ⟨max N 1, ?_⟩
  intro s hs
  have hub : pinchingTailSlope psi s ≤ eps / 2 := by
    refine csSup_le (nonempty_pinchingQuotient psi s) ?_
    rintro y ⟨v, hv, rfl⟩
    have hNs : N ≤ s := le_trans (le_max_left N 1) hs
    have hsv : s ≤ v := le_trans (le_max_left s 1) hv
    have h := hN v (le_trans hNs hsv)
    rw [Real.dist_eq, sub_zero] at h
    exact le_of_lt (lt_of_abs_lt h)
  have hlb := pinchingTailSlope_nonneg hmono hnonneg hlim s
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hlb]
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.pinchingTailSlope_tendsto
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.pinchingTailSlope_tendsto target :: scope.openDecls } }

private noncomputable def pinchingEnvelope (psi : Real → Real) (s : Real) : Real :=
  _root_.Max.max s 1 * pinchingTailSlope psi s + 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.pinchingEnvelope
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.pinchingEnvelope target :: scope.openDecls } }

private theorem one_le_pinchingEnvelope {psi : Real → Real} (hmono : Monotone psi)
    (hnonneg : ∀ s : Real, 0 ≤ psi s)
    (hlim : _root_.Filter.Tendsto (fun s : Real => psi s / s) _root_.Filter.atTop (nhds 0)) (s : Real) :
    1 ≤ pinchingEnvelope psi s := by
  have h1 : (0 : Real) ≤ _root_.Max.max s 1 := le_trans zero_le_one (le_max_right s 1)
  have h2 := pinchingTailSlope_nonneg hmono hnonneg hlim s
  unfold pinchingEnvelope
  nlinarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.one_le_pinchingEnvelope
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.one_le_pinchingEnvelope target :: scope.openDecls } }

private theorem pinchingEnvelope_monotone {psi : Real → Real} (hmono : Monotone psi)
    (hnonneg : ∀ s : Real, 0 ≤ psi s)
    (hlim : _root_.Filter.Tendsto (fun s : Real => psi s / s) _root_.Filter.atTop (nhds 0)) :
    Monotone (pinchingEnvelope psi) := by
  intro s1 s2 h12
  have ha1 : (1 : Real) ≤ _root_.Max.max s1 1 := le_max_right _ _
  have hapos : (0 : Real) < _root_.Max.max s1 1 := lt_of_lt_of_le zero_lt_one ha1
  have hb1 : (1 : Real) ≤ _root_.Max.max s2 1 := le_max_right _ _
  have hbpos : (0 : Real) < _root_.Max.max s2 1 := lt_of_lt_of_le zero_lt_one hb1
  have hab : _root_.Max.max s1 1 ≤ _root_.Max.max s2 1 := max_le_max h12 (le_refl 1)
  have hT2 := pinchingTailSlope_nonneg hmono hnonneg hlim s2
  have hqb : psi (_root_.Max.max s2 1) / _root_.Max.max s2 1 ≤ pinchingTailSlope psi s2 :=
    quotient_le_pinchingTailSlope hmono hnonneg hlim (le_refl (_root_.Max.max s2 1))
  have hkey : pinchingTailSlope psi s1 ≤
      max s2 1 * pinchingTailSlope psi s2 / _root_.Max.max s1 1 := by
    refine csSup_le (nonempty_pinchingQuotient psi s1) ?_
    rintro y ⟨v, hv, rfl⟩
    rw [le_div_iff₀ hapos]
    have hv1 : (1 : Real) ≤ v := le_trans (le_max_right s1 1) hv
    have hvpos : (0 : Real) < v := lt_of_lt_of_le zero_lt_one hv1
    have hq0 : 0 ≤ psi v / v := div_nonneg (hnonneg v) (le_of_lt hvpos)
    have hav : _root_.Max.max s1 1 ≤ v := hv
    rcases le_total (_root_.Max.max s2 1) v with h | h
    · have hqv : psi v / v ≤ pinchingTailSlope psi s2 :=
        quotient_le_pinchingTailSlope hmono hnonneg hlim h
      nlinarith
    · have hcancel : psi v / v * v = psi v := div_mul_cancel₀ _ (ne_of_gt hvpos)
      have hmono' : psi v ≤ psi (_root_.Max.max s2 1) := hmono h
      have hcancel2 : psi (_root_.Max.max s2 1) / _root_.Max.max s2 1 * _root_.Max.max s2 1 = psi (_root_.Max.max s2 1) :=
        div_mul_cancel₀ _ (ne_of_gt hbpos)
      nlinarith
  rw [le_div_iff₀ hapos] at hkey
  unfold pinchingEnvelope
  nlinarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.pinchingEnvelope_monotone
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.pinchingEnvelope_monotone target :: scope.openDecls } }

private theorem le_pinchingEnvelope {psi : Real → Real} (hmono : Monotone psi)
    (hnonneg : ∀ s : Real, 0 ≤ psi s)
    (hlim : _root_.Filter.Tendsto (fun s : Real => psi s / s) _root_.Filter.atTop (nhds 0)) {s : Real} (hs : 0 ≤ s) :
    psi s ≤ pinchingEnvelope psi s := by
  rcases le_total s 1 with h | h
  · have hmax : _root_.Max.max s 1 = 1 := max_eq_right h
    have hq : psi 1 / 1 ≤ pinchingTailSlope psi s :=
      quotient_le_pinchingTailSlope hmono hnonneg hlim (by rw [hmax])
    rw [div_one] at hq
    have hps : psi s ≤ psi 1 := hmono h
    unfold pinchingEnvelope
    rw [hmax]
    linarith
  · have hmax : _root_.Max.max s 1 = s := max_eq_left h
    have hspos : (0 : Real) < s := lt_of_lt_of_le zero_lt_one h
    have hq : psi s / s ≤ pinchingTailSlope psi s :=
      quotient_le_pinchingTailSlope hmono hnonneg hlim (by rw [hmax])
    have hcancel : psi s / s * s = psi s := div_mul_cancel₀ _ (ne_of_gt hspos)
    unfold pinchingEnvelope
    rw [hmax]
    nlinarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.le_pinchingEnvelope
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.le_pinchingEnvelope target :: scope.openDecls } }

private theorem pinchingEnvelope_quotient {psi : Real → Real} (hmono : Monotone psi)
    (hnonneg : ∀ s : Real, 0 ≤ psi s)
    (hlim : _root_.Filter.Tendsto (fun s : Real => psi s / s) _root_.Filter.atTop (nhds 0)) {s1 s2 : Real}
    (hs1 : 0 < s1) (h12 : s1 ≤ s2) :
    pinchingEnvelope psi s2 * s1 ≤ pinchingEnvelope psi s1 * s2 := by
  have hT2 := pinchingTailSlope_nonneg hmono hnonneg hlim s2
  have hTanti := pinchingTailSlope_antitone hmono hnonneg hlim h12
  have hmaxkey : _root_.Max.max s2 1 * s1 ≤ _root_.Max.max s1 1 * s2 := by
    rcases le_total 1 s1 with h | h
    · rw [max_eq_left h, max_eq_left (le_trans h h12)]
      exact le_of_eq (mul_comm s2 s1)
    · rcases le_total 1 s2 with h2 | h2
      · rw [max_eq_right h, max_eq_left h2]
        nlinarith
      · rw [max_eq_right h, max_eq_right h2]
        nlinarith
  have hs2 : (0 : Real) < s2 := lt_of_lt_of_le hs1 h12
  have ha1 : (1 : Real) ≤ _root_.Max.max s1 1 := le_max_right _ _
  have hprod1 : pinchingTailSlope psi s2 * (_root_.Max.max s2 1 * s1) ≤
      pinchingTailSlope psi s2 * (_root_.Max.max s1 1 * s2) :=
    mul_le_mul_of_nonneg_left hmaxkey hT2
  have hprod2 : pinchingTailSlope psi s2 * (_root_.Max.max s1 1 * s2) ≤
      pinchingTailSlope psi s1 * (_root_.Max.max s1 1 * s2) := by
    refine mul_le_mul_of_nonneg_right hTanti ?_
    nlinarith
  unfold pinchingEnvelope
  nlinarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.pinchingEnvelope_quotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.pinchingEnvelope_quotient target :: scope.openDecls } }

private theorem pinchingEnvelope_quotient_tendsto {psi : Real → Real} (hmono : Monotone psi)
    (hnonneg : ∀ s : Real, 0 ≤ psi s)
    (hlim : _root_.Filter.Tendsto (fun s : Real => psi s / s) _root_.Filter.atTop (nhds 0)) :
    Tendsto (fun s : Real => pinchingEnvelope psi s / s) _root_.Filter.atTop (nhds 0) := by
  have h1 : _root_.Filter.Tendsto (fun s : Real => pinchingTailSlope psi s + 1 / s) _root_.Filter.atTop (nhds 0) := by
    simpa using (pinchingTailSlope_tendsto hmono hnonneg hlim).add (tendsto_const_div_atTop 1)
  refine h1.congr' ?_
  filter_upwards [_root_.Filter.eventually_ge_atTop (1 : Real)] with s hs
  have hspos : (0 : Real) < s := lt_of_lt_of_le zero_lt_one hs
  unfold pinchingEnvelope
  rw [max_eq_left hs]
  field_simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.pinchingEnvelope_quotient_tendsto
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.pinchingEnvelope_quotient_tendsto target :: scope.openDecls } }

private noncomputable def unitAverage (f : Real → Real) (s : Real) : Real :=
  ∫ w in s..(s + 1), f w

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.unitAverage
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.unitAverage target :: scope.openDecls } }

private theorem unitAverage_eq_shift (f : Real → Real) (s : Real) :
    unitAverage f s = ∫ w in (0 : Real)..1, f (s + w) := by
  unfold unitAverage
  rw [intervalIntegral.integral_comp_add_left (f := f) s]
  norm_num

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.unitAverage_eq_shift
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.unitAverage_eq_shift target :: scope.openDecls } }

private theorem monotone_shift {f : Real → Real} (hf : Monotone f) (s : Real) :
    Monotone (fun w : Real => f (s + w)) := fun a b hab => hf (by linarith)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.monotone_shift
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.monotone_shift target :: scope.openDecls } }

private theorem intervalIntegrable_shift {f : Real → Real} (hf : Monotone f) (s : Real) :
    IntervalIntegrable (fun w : Real => f (s + w)) MeasureTheory.volume 0 1 :=
  (monotone_shift hf s).intervalIntegrable

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_shift
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_shift target :: scope.openDecls } }

private theorem unitAverage_monotone {f : Real → Real} (hf : Monotone f) :
    Monotone (unitAverage f) := by
  intro s1 s2 h12
  rw [unitAverage_eq_shift, unitAverage_eq_shift]
  refine intervalIntegral.integral_mono_on (by norm_num) (intervalIntegrable_shift hf s1)
    (intervalIntegrable_shift hf s2) ?_
  intro w _
  exact hf (by linarith)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.unitAverage_monotone
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.unitAverage_monotone target :: scope.openDecls } }

private theorem le_unitAverage {f : Real → Real} (hf : Monotone f) (s : Real) :
    f s ≤ unitAverage f s := by
  rw [unitAverage_eq_shift]
  have h : (∫ _w in (0 : Real)..1, f s) ≤ ∫ w in (0 : Real)..1, f (s + w) := by
    refine intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const
      (intervalIntegrable_shift hf s) ?_
    intro w hw
    exact hf (by linarith [hw.1])
  simpa using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.le_unitAverage
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.le_unitAverage target :: scope.openDecls } }

private theorem unitAverage_le {f : Real → Real} (hf : Monotone f) (s : Real) :
    unitAverage f s ≤ f (s + 1) := by
  rw [unitAverage_eq_shift]
  have h : (∫ w in (0 : Real)..1, f (s + w)) ≤ ∫ _w in (0 : Real)..1, f (s + 1) := by
    refine intervalIntegral.integral_mono_on (by norm_num) (intervalIntegrable_shift hf s)
      intervalIntegrable_const ?_
    intro w hw
    exact hf (by linarith [hw.2])
  simpa using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.unitAverage_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.unitAverage_le target :: scope.openDecls } }

private theorem unitAverage_nonneg {f : Real → Real} (hf : ∀ s : Real, 0 ≤ f s) (s : Real) :
    0 ≤ unitAverage f s := by
  unfold unitAverage
  exact intervalIntegral.integral_nonneg (by linarith) (fun u _ => hf u)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.unitAverage_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.unitAverage_nonneg target :: scope.openDecls } }

private theorem unitAverage_quotient {f : Real → Real} (hf : Monotone f)
    (hf0 : ∀ s : Real, 0 ≤ f s)
    (hq : ∀ s1 s2 : Real, 0 < s1 → s1 ≤ s2 → f s2 * s1 ≤ f s1 * s2)
    {s1 s2 : Real} (hs1 : 0 < s1) (h12 : s1 ≤ s2) :
    unitAverage f s2 * s1 ≤ unitAverage f s1 * s2 := by
  rw [unitAverage_eq_shift, unitAverage_eq_shift, ← intervalIntegral.integral_mul_const,
    ← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_mono_on (by norm_num)
    ((intervalIntegrable_shift hf s2).mul_const _)
    ((intervalIntegrable_shift hf s1).mul_const _) ?_
  intro w hw
  have hw0 : (0 : Real) ≤ w := hw.1
  have hbase := hq (s1 + w) (s2 + w) (by linarith) (by linarith)
  have hfnn1 : 0 ≤ f (s1 + w) := hf0 _
  have h1 : f (s2 + w) * (s1 + w) * s1 ≤ f (s1 + w) * (s2 + w) * s1 :=
    mul_le_mul_of_nonneg_right hbase (le_of_lt hs1)
  have h2 : f (s1 + w) * (s1 * w) ≤ f (s1 + w) * (s2 * w) := by
    refine mul_le_mul_of_nonneg_left ?_ hfnn1
    nlinarith
  have hpos : (0 : Real) < s1 + w := by linarith
  nlinarith [h1, h2, hpos]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.unitAverage_quotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.unitAverage_quotient target :: scope.openDecls } }

private theorem unitAverage_quotient_tendsto {f : Real → Real} (hf : Monotone f)
    (hf0 : ∀ s : Real, 0 ≤ f s)
    (hlim : _root_.Filter.Tendsto (fun s : Real => f s / s) _root_.Filter.atTop (nhds 0)) :
    Tendsto (fun s : Real => unitAverage f s / s) _root_.Filter.atTop (nhds 0) := by
  have hshift : _root_.Filter.Tendsto (fun s : Real => f (s + 1) / (s + 1)) _root_.Filter.atTop (nhds 0) := by
    have hmap : _root_.Filter.Tendsto (fun s : Real => s + 1) _root_.Filter.atTop atTop :=
      _root_.Filter.tendsto_atTop_add_const_right _root_.Filter.atTop 1 _root_.Filter.tendsto_id
    simpa [Function.comp_def] using hlim.comp hmap
  have hratio : _root_.Filter.Tendsto (fun s : Real => 1 + 1 / s) _root_.Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop 1)
  have hprod : _root_.Filter.Tendsto (fun s : Real => f (s + 1) / (s + 1) * (1 + 1 / s)) _root_.Filter.atTop (nhds 0) := by
    simpa using hshift.mul hratio
  refine squeeze_zero' ?_ ?_ hprod
  · filter_upwards [_root_.Filter.eventually_gt_atTop (0 : Real)] with s hs
    exact div_nonneg (unitAverage_nonneg hf0 s) (le_of_lt hs)
  · filter_upwards [_root_.Filter.eventually_gt_atTop (0 : Real)] with s hs
    have hs1 : s + 1 ≠ 0 := by
      have hpos : (0 : Real) < s + 1 := by linarith
      exact ne_of_gt hpos
    have heq : f (s + 1) / (s + 1) * (1 + 1 / s) = f (s + 1) / s := by
      field_simp
    rw [heq, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (unitAverage_le hf s) (le_of_lt (inv_pos.mpr hs))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.unitAverage_quotient_tendsto
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.unitAverage_quotient_tendsto target :: scope.openDecls } }

private theorem unitAverage_eq_sub {f : Real → Real}
    (hf : ∀ a b : Real, IntervalIntegrable f MeasureTheory.volume a b) (s : Real) :
    unitAverage f s = (∫ w in (0 : Real)..(s + 1), f w) - ∫ w in (0 : Real)..s, f w := by
  unfold unitAverage
  rw [eq_sub_iff_add_eq, add_comm]
  exact intervalIntegral.integral_add_adjacent_intervals (hf 0 s) (hf s (s + 1))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.unitAverage_eq_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.unitAverage_eq_sub target :: scope.openDecls } }

private theorem unitAverage_continuous {f : Real → Real} (hf : Monotone f) :
    Continuous (unitAverage f) := by
  have hprim : Continuous (fun x : Real => ∫ w in (0 : Real)..x, f w) :=
    intervalIntegral.continuous_primitive (fun _ _ => hf.intervalIntegrable) 0
  have heq : unitAverage f =
      fun s : Real => (∫ w in (0 : Real)..(s + 1), f w) - ∫ w in (0 : Real)..s, f w :=
    funext (unitAverage_eq_sub (fun _ _ => hf.intervalIntegrable))
  rw [heq]
  exact (hprim.comp (continuous_id.add continuous_const)).sub hprim

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.unitAverage_continuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.unitAverage_continuous target :: scope.openDecls } }

private theorem unitAverage_hasDerivAt {f : Real → Real} (hf : Continuous f) (s : Real) :
    HasDerivAt (unitAverage f) (f (s + 1) - f s) s := by
  have h1 : HasDerivAt (fun x : Real => ∫ w in (0 : Real)..x, f w) (f (s + 1)) (s + 1) :=
    (hf.integral_hasStrictDerivAt 0 (s + 1)).hasDerivAt
  have h3 : HasDerivAt (fun x : Real => ∫ w in (0 : Real)..(x + 1), f w) (f (s + 1)) s :=
    HasDerivAt.comp_add_const s 1 h1
  have h4 : HasDerivAt (fun x : Real => ∫ w in (0 : Real)..x, f w) (f s) s :=
    (hf.integral_hasStrictDerivAt 0 s).hasDerivAt
  have heq : unitAverage f =
      fun x : Real => (∫ w in (0 : Real)..(x + 1), f w) - ∫ w in (0 : Real)..x, f w :=
    funext (unitAverage_eq_sub (fun a b => hf.intervalIntegrable a b))
  rw [heq]
  exact h3.sub h4

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.unitAverage_hasDerivAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.unitAverage_hasDerivAt target :: scope.openDecls } }

private theorem unitAverage_contDiff {f : Real → Real} (hf : Continuous f) :
    ContDiff Real 1 (unitAverage f) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun s => (unitAverage_hasDerivAt hf s).differentiableAt, ?_⟩
  have hderiv : deriv (unitAverage f) = fun s : Real => f (s + 1) - f s :=
    funext fun s => (unitAverage_hasDerivAt hf s).deriv
  rw [hderiv]
  exact (hf.comp (continuous_id.add continuous_const)).sub hf

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.unitAverage_contDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.unitAverage_contDiff target :: scope.openDecls } }

private theorem exists_admissiblePinchingFunction_ge_of_monotone {psi : Real → Real}
    (hmono : Monotone psi) (hnonneg : ∀ s : Real, 0 ≤ psi s)
    (hlim : _root_.Filter.Tendsto (fun s : Real => psi s / s) _root_.Filter.atTop (nhds 0)) :
    ∃ Phi : Real → Real, AdmissiblePinchingFunction Phi ∧ ∀ s : Real, 0 ≤ s → psi s ≤ Phi s := by
  have henvMono := pinchingEnvelope_monotone hmono hnonneg hlim
  have henvOne := one_le_pinchingEnvelope hmono hnonneg hlim
  have henvNonneg : ∀ s : Real, 0 ≤ pinchingEnvelope psi s := fun s => by linarith [henvOne s]
  have haMono := unitAverage_monotone henvMono
  have haNonneg : ∀ s : Real, 0 ≤ unitAverage (pinchingEnvelope psi) s :=
    fun s => unitAverage_nonneg henvNonneg s
  have haCont := unitAverage_continuous henvMono
  have haQuot : ∀ s1 s2 : Real, 0 < s1 → s1 ≤ s2 →
      unitAverage (pinchingEnvelope psi) s2 * s1 ≤
        unitAverage (pinchingEnvelope psi) s1 * s2 := by
    intro s1 s2 hs1 h12
    exact unitAverage_quotient henvMono henvNonneg
      (fun a b ha hab => pinchingEnvelope_quotient hmono hnonneg hlim ha hab) hs1 h12
  refine ⟨unitAverage (unitAverage (pinchingEnvelope psi)), ⟨unitAverage_contDiff haCont, ?_, ?_,
    ?_, ?_⟩, ?_⟩
  · intro s
    have h1 : pinchingEnvelope psi s ≤ unitAverage (pinchingEnvelope psi) s :=
      le_unitAverage henvMono s
    have h2 : unitAverage (pinchingEnvelope psi) s ≤
        unitAverage (unitAverage (pinchingEnvelope psi)) s := le_unitAverage haMono s
    have h3 := henvOne s
    linarith
  · exact unitAverage_monotone haMono
  · intro a ha b hb hab
    have ha' : (0 : Real) < a := ha
    have hb' : (0 : Real) < b := hb
    dsimp only
    rw [div_le_div_iff₀ hb' ha']
    exact unitAverage_quotient haMono haNonneg haQuot ha' hab
  · exact unitAverage_quotient_tendsto haMono haNonneg
      (unitAverage_quotient_tendsto henvMono henvNonneg
        (pinchingEnvelope_quotient_tendsto hmono hnonneg hlim))
  · intro s hs
    have h0 := le_pinchingEnvelope hmono hnonneg hlim hs
    have h1 : pinchingEnvelope psi s ≤ unitAverage (pinchingEnvelope psi) s :=
      le_unitAverage henvMono s
    have h2 : unitAverage (pinchingEnvelope psi) s ≤
        unitAverage (unitAverage (pinchingEnvelope psi)) s := le_unitAverage haMono s
    linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_ge_of_monotone
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_ge_of_monotone target :: scope.openDecls } }

theorem exists_admissiblePinchingFunction_ge {psi : Real → Real}
    (hmono : MonotoneOn psi (Set.Ici 0)) (hnonneg : ∀ s : Real, 0 ≤ s → 0 ≤ psi s)
    (hlim : _root_.Filter.Tendsto (fun s : Real => psi s / s) _root_.Filter.atTop (nhds 0)) :
    ∃ Phi : Real → Real, AdmissiblePinchingFunction Phi ∧ ∀ s : Real, 0 ≤ s → psi s ≤ Phi s := by
  have hchiMono : Monotone (fun s : Real => psi (_root_.Max.max s 0)) := by
    intro a b hab
    exact hmono (le_max_right a 0) (le_max_right b 0) (max_le_max hab (le_refl 0))
  have hchiNonneg : ∀ s : Real, 0 ≤ psi (_root_.Max.max s 0) := fun s => hnonneg _ (le_max_right s 0)
  have hchiLim : _root_.Filter.Tendsto (fun s : Real => psi (_root_.Max.max s 0) / s) _root_.Filter.atTop (nhds 0) := by
    refine hlim.congr' ?_
    filter_upwards [_root_.Filter.eventually_ge_atTop (0 : Real)] with s hs
    rw [max_eq_left hs]
  obtain ⟨Phi, hPhi, hge⟩ :=
    exists_admissiblePinchingFunction_ge_of_monotone hchiMono hchiNonneg hchiLim
  refine ⟨Phi, hPhi, ?_⟩
  intro s hs
  have h := hge s hs
  rwa [max_eq_left hs] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_ge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_ge ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_ge

theorem eventually_neg_le_div_of_admissiblePinchingFunction {Phi : Real → Real}
    (hPhi : AdmissiblePinchingFunction Phi) {lam scal Q : Nat → Real} {C : Real}
    (hQpos : ∀ᶠ i in _root_.Filter.atTop, 0 < Q i) (hQ : _root_.Filter.Tendsto Q _root_.Filter.atTop _root_.Filter.atTop)
    (hpinch : ∀ᶠ i in _root_.Filter.atTop, -Phi (scal i) ≤ lam i)
    (hbound : ∀ᶠ i in _root_.Filter.atTop, scal i ≤ C * Q i) {eps : Real} (heps : 0 < eps) :
    ∀ᶠ i in _root_.Filter.atTop, -eps ≤ lam i / Q i := by
  have hC : (0 : Real) < _root_.Max.max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hPhi.quotientTendsto (eps / (2 * _root_.Max.max C 1))
    (by positivity)
  have hbig : ∀ᶠ i in _root_.Filter.atTop, _root_.Max.max N 1 * (Phi (_root_.Max.max N 1) / eps) ≤ Q i :=
    Filter.tendsto_atTop.mp hQ (_root_.Max.max N 1 * (Phi (_root_.Max.max N 1) / eps))
  have hbig' : ∀ᶠ i in _root_.Filter.atTop, Phi (_root_.Max.max N 1) / eps ≤ Q i := by
    filter_upwards [hbig] with i hi
    have h1 : (1 : Real) ≤ _root_.Max.max N 1 := le_max_right N 1
    have h2 : 0 ≤ Phi (_root_.Max.max N 1) / eps := le_of_lt (div_pos (hPhi.pos _) heps)
    nlinarith
  filter_upwards [hQpos, hpinch, hbound, hbig'] with i hQi hpi hbi hbgi
  have hkey : Phi (scal i) ≤ eps * Q i := by
    rcases le_total (scal i) (_root_.Max.max N 1) with hcase | hcase
    · have h1 : Phi (scal i) ≤ Phi (_root_.Max.max N 1) := hPhi.mono hcase
      have h2 : Phi (_root_.Max.max N 1) ≤ eps * Q i := by
        rw [div_le_iff₀ heps] at hbgi
        linarith
      linarith
    · have hNpos : (0 : Real) < _root_.Max.max N 1 := lt_of_lt_of_le zero_lt_one (le_max_right N 1)
      have hspos : (0 : Real) < scal i := lt_of_lt_of_le hNpos hcase
      have hdist := hN (scal i) (le_trans (le_max_left N 1) hcase)
      rw [Real.dist_eq, sub_zero] at hdist
      have hquot : Phi (scal i) / scal i < eps / (2 * _root_.Max.max C 1) := lt_of_abs_lt hdist
      rw [div_lt_iff₀ hspos] at hquot
      have hsC : scal i ≤ _root_.Max.max C 1 * Q i := by
        have h1 : C * Q i ≤ _root_.Max.max C 1 * Q i :=
          mul_le_mul_of_nonneg_right (le_max_left C 1) (le_of_lt hQi)
        linarith
      have hmul : eps / (2 * _root_.Max.max C 1) * scal i ≤ eps / (2 * _root_.Max.max C 1) * (_root_.Max.max C 1 * Q i) :=
        mul_le_mul_of_nonneg_left hsC (le_of_lt (by positivity))
      have hsimp : eps / (2 * _root_.Max.max C 1) * (_root_.Max.max C 1 * Q i) = eps * Q i / 2 := by
        field_simp
      have hQinn : 0 ≤ eps * Q i := le_of_lt (mul_pos heps hQi)
      rw [hsimp] at hmul
      linarith
  have hlow : -(eps * Q i) ≤ lam i := by linarith
  rw [le_div_iff₀ hQi]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.eventually_neg_le_div_of_admissiblePinchingFunction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.eventually_neg_le_div_of_admissiblePinchingFunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.eventually_neg_le_div_of_admissiblePinchingFunction ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.eventually_neg_le_div_of_admissiblePinchingFunction

theorem nonneg_of_tendsto_div_of_admissiblePinchingFunction {Phi : Real → Real}
    (hPhi : AdmissiblePinchingFunction Phi) {lam scal Q : Nat → Real} {C L : Real}
    (hQpos : ∀ᶠ i in _root_.Filter.atTop, 0 < Q i) (hQ : _root_.Filter.Tendsto Q _root_.Filter.atTop _root_.Filter.atTop)
    (hpinch : ∀ᶠ i in _root_.Filter.atTop, -Phi (scal i) ≤ lam i)
    (hbound : ∀ᶠ i in _root_.Filter.atTop, scal i ≤ C * Q i)
    (hlam : _root_.Filter.Tendsto (fun i => lam i / Q i) _root_.Filter.atTop (nhds L)) :
    0 ≤ L := by
  by_contra hcon
  have hneg : L < 0 := not_le.mp hcon
  have heps : (0 : Real) < -L / 2 := by linarith
  have hev := eventually_neg_le_div_of_admissiblePinchingFunction hPhi hQpos hQ hpinch hbound heps
  have hle : -(-L / 2) ≤ L := ge_of_tendsto hlam hev
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.nonneg_of_tendsto_div_of_admissiblePinchingFunction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.nonneg_of_tendsto_div_of_admissiblePinchingFunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.nonneg_of_tendsto_div_of_admissiblePinchingFunction ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.nonneg_of_tendsto_div_of_admissiblePinchingFunction

def RescaledCurvatureTendsto (lam scal Q : Nat → Real) (lamLimit scalLimit : Real) : Prop :=
  _root_.Filter.Tendsto (fun i => lam i / Q i) _root_.Filter.atTop (nhds lamLimit) ∧
    _root_.Filter.Tendsto (fun i => scal i / Q i) _root_.Filter.atTop (nhds scalLimit)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.RescaledCurvatureTendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.RescaledCurvatureTendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.RescaledCurvatureTendsto ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.RescaledCurvatureTendsto

theorem nonneg_of_rescaledCurvatureTendsto {Phi : Real → Real}
    (hPhi : AdmissiblePinchingFunction Phi) {lam scal Q : Nat → Real} {lamLimit scalLimit : Real}
    (hQpos : ∀ᶠ i in _root_.Filter.atTop, 0 < Q i) (hQ : _root_.Filter.Tendsto Q _root_.Filter.atTop _root_.Filter.atTop)
    (hpinch : ∀ᶠ i in _root_.Filter.atTop, -Phi (scal i) ≤ lam i)
    (hconv : RescaledCurvatureTendsto lam scal Q lamLimit scalLimit) :
    0 ≤ lamLimit := by
  have hscal : ∀ᶠ i in _root_.Filter.atTop, scal i / Q i ≤ scalLimit + 1 := by
    have hlt : ∀ᶠ i in _root_.Filter.atTop, scal i / Q i < scalLimit + 1 :=
      hconv.2.eventually_lt_const (by linarith)
    filter_upwards [hlt] with i hi
    exact le_of_lt hi
  have hbound : ∀ᶠ i in _root_.Filter.atTop, scal i ≤ (scalLimit + 1) * Q i := by
    filter_upwards [hQpos, hscal] with i hQi hi
    rw [div_le_iff₀ hQi] at hi
    linarith
  exact nonneg_of_tendsto_div_of_admissiblePinchingFunction hPhi hQpos hQ hpinch hbound hconv.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.nonneg_of_rescaledCurvatureTendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.nonneg_of_rescaledCurvatureTendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.nonneg_of_rescaledCurvatureTendsto ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.nonneg_of_rescaledCurvatureTendsto

end Perelman

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

namespace Perelman

omit [FiniteDimensional Real E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem algebraicCurvatureOperatorQuadraticEval_of_coe_smul
    {x : M} {n : Nat} (Q : Real)
    (A B : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hB : (B : Tensor04At (I := I) (M := M) x) = Q • (A : Tensor04At (I := I) (M := M) x))
    (c : Fin n → Real) (v w : Fin n → TangentSpace I x) :
    algebraicCurvatureOperatorQuadraticEval (I := I) (M := M) B c v w =
      Q * algebraicCurvatureOperatorQuadraticEval (I := I) (M := M) A c v w := by
  unfold algebraicCurvatureOperatorQuadraticEval
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  have hval : tensor04StandardAt (I := I) (M := M) (B : Tensor04At (I := I) (M := M) x)
      (v i) (w i) (w j) (v j) =
      Q * tensor04StandardAt (I := I) (M := M) (A : Tensor04At (I := I) (M := M) x)
        (v i) (w i) (w j) (v j) := by
    unfold tensor04StandardAt
    rw [hB]
    simp
  rw [hval]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.algebraicCurvatureOperatorQuadraticEval_of_coe_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.algebraicCurvatureOperatorQuadraticEval_of_coe_smul target :: scope.openDecls } }

omit [FiniteDimensional Real E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem algebraicCurvatureIdentityQuadraticEval_scaleMetric
    {x : M} {n : Nat} {Q : Real} (hQ : 0 < Q) (g : SmoothRiemannianMetric I M)
    (c : Fin n → Real) (v w : Fin n → TangentSpace I x) :
    algebraicCurvatureIdentityQuadraticEval (I := I) (M := M)
        (scaleMetric (I := I) Q hQ g) c v w =
      Q ^ 2 * algebraicCurvatureIdentityQuadraticEval (I := I) (M := M) g c v w := by
  unfold algebraicCurvatureIdentityQuadraticEval
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  simp only [scaleMetric_inner]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.algebraicCurvatureIdentityQuadraticEval_scaleMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.algebraicCurvatureIdentityQuadraticEval_scaleMetric target :: scope.openDecls } }

omit [FiniteDimensional Real E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem curvatureOperatorLowerBoundAt_scaleMetric_smul_iff
    {Q : Real} (hQ : 0 < Q) (g g' : SmoothRiemannianMetric I M) (x : M)
    (A B : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) (K : Real)
    (hg : g' = scaleMetric (I := I) Q hQ g)
    (hB : (B : Tensor04At (I := I) (M := M) x) = Q • (A : Tensor04At (I := I) (M := M) x)) :
    curvatureOperatorLowerBoundAt (I := I) g' x B (Q⁻¹ * K) ↔
      curvatureOperatorLowerBoundAt (I := I) g x A K := by
  subst hg
  have hkey : ∀ (n : Nat) (c : Fin n → Real) (v w : Fin n → TangentSpace I x),
      algebraicCurvatureOperatorQuadraticEval (I := I) (M := M) B c v w +
          Q⁻¹ * K * algebraicCurvatureIdentityQuadraticEval (I := I) (M := M)
            (scaleMetric (I := I) Q hQ g) c v w =
        Q * (algebraicCurvatureOperatorQuadraticEval (I := I) (M := M) A c v w +
          K * algebraicCurvatureIdentityQuadraticEval (I := I) (M := M) g c v w) := by
    intro n c v w
    rw [algebraicCurvatureOperatorQuadraticEval_of_coe_smul Q A B hB,
      algebraicCurvatureIdentityQuadraticEval_scaleMetric hQ g]
    field_simp
  constructor
  · intro h n c v w
    have hn := h n c v w
    rw [hkey n c v w] at hn
    nlinarith [hn, hQ]
  · intro h n c v w
    have hn := h n c v w
    rw [hkey n c v w]
    exact mul_nonneg (le_of_lt hQ) hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.curvatureOperatorLowerBoundAt_scaleMetric_smul_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.curvatureOperatorLowerBoundAt_scaleMetric_smul_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.curvatureOperatorLowerBoundAt_scaleMetric_smul_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.curvatureOperatorLowerBoundAt_scaleMetric_smul_iff

def PhiAlmostNonnegative {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (W : Set Real) (Phi : Real → Real) : Prop :=
  ∀ t ∈ W, ∀ x : M,
    curvatureOperatorLowerBoundAt (I := I) (S.base.metric t) x
      ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t) x⟩ (Phi (S.scalar t x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.PhiAlmostNonnegative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.PhiAlmostNonnegative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.PhiAlmostNonnegative ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.PhiAlmostNonnegative

omit [SigmaCompactSpace M] in
theorem phiAlmostNonnegative_iff_neg_le_leastCurvatureOperatorEigenvalueAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (W : Set Real)
    (Phi : Real → Real) (hdim : Module.finrank Real E = 3) :
    PhiAlmostNonnegative (I := I) (M := M) S W Phi ↔
      ∀ t ∈ W, ∀ x : M,
        -Phi (S.scalar t x) ≤ leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩ := by
  have hdimT : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3 := by
    intro x
    calc Module.finrank Real (TangentSpace I x) = Module.finrank Real E := rfl
      _ = 3 := hdim
  constructor
  · intro h t ht x
    obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) (S.base.metric t) x (hdimT x)
    have hiff := curvatureOperatorLowerBoundAt_iff_neg_sectionalMin_le (I := I)
      (S.base.metric t) basis horth
      (A := ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t) x⟩) (K := Phi (S.scalar t x))
    have hle := hiff.mp (h t ht x)
    rw [leastCurvatureOperatorEigenvalueAt_eq_sectionalMin (I := I) (S.base.metric t) x
      basis horth]
    linarith
  · intro h t ht x
    obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) (S.base.metric t) x (hdimT x)
    have hle := h t ht x
    rw [leastCurvatureOperatorEigenvalueAt_eq_sectionalMin (I := I) (S.base.metric t) x
      basis horth] at hle
    refine (curvatureOperatorLowerBoundAt_iff_neg_sectionalMin_le (I := I)
      (S.base.metric t) basis horth
      (A := ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t) x⟩) (K := Phi (S.scalar t x))).mpr ?_
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.phiAlmostNonnegative_iff_neg_le_leastCurvatureOperatorEigenvalueAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.phiAlmostNonnegative_iff_neg_le_leastCurvatureOperatorEigenvalueAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.phiAlmostNonnegative_iff_neg_le_leastCurvatureOperatorEigenvalueAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.phiAlmostNonnegative_iff_neg_le_leastCurvatureOperatorEigenvalueAt

omit [SigmaCompactSpace M] in
theorem neg_le_orderedSectionalCurvaturesAt_of_phiAlmostNonnegative
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D} {W : Set Real}
    {Phi : Real → Real} (h : PhiAlmostNonnegative (I := I) (M := M) S W Phi)
    {t : Real} (ht : t ∈ W) {x : M} (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis) (i : Fin 3) :
    -Phi (S.scalar t x) ≤ orderedSectionalCurvaturesAt (I := I) x basis
      ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t) x⟩ i := by
  have hmin := (curvatureOperatorLowerBoundAt_iff_neg_sectionalMin_le (I := I)
    (S.base.metric t) basis horth
    (A := ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩) (K := Phi (S.scalar t x))).mp (h t ht x)
  have hi : i ≤ (2 : Fin 3) := by
    fin_cases i <;> decide
  have hle := orderedSectionalCurvaturesAt_antitone (I := I) x basis
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩ hi
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.neg_le_orderedSectionalCurvaturesAt_of_phiAlmostNonnegative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.neg_le_orderedSectionalCurvaturesAt_of_phiAlmostNonnegative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.neg_le_orderedSectionalCurvaturesAt_of_phiAlmostNonnegative ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.neg_le_orderedSectionalCurvaturesAt_of_phiAlmostNonnegative

noncomputable def hamiltonIveyPinchingBound (K s : Real) : Real :=
  _root_.InfSet.sInf {y : Real | ∃ d : Real, 0 < d ∧ y = d * _root_.Max.max s 0 + 2 * d * K * Real.exp (2 + (2 * d)⁻¹)}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound

private theorem bddBelow_hamiltonIveyPinchingSet {K : Real} (hK : 0 ≤ K) (s : Real) :
    BddBelow {y : Real |
      ∃ d : Real, 0 < d ∧ y = d * _root_.Max.max s 0 + 2 * d * K * Real.exp (2 + (2 * d)⁻¹)} := by
  refine ⟨0, ?_⟩
  rintro y ⟨d, hd, rfl⟩
  have h1 : 0 ≤ d * _root_.Max.max s 0 := mul_nonneg (le_of_lt hd) (le_max_right s 0)
  have h2 : 0 ≤ 2 * d * K * Real.exp (2 + (2 * d)⁻¹) :=
    mul_nonneg (mul_nonneg (by linarith) hK) (le_of_lt (Real.exp_pos _))
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.bddBelow_hamiltonIveyPinchingSet
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.bddBelow_hamiltonIveyPinchingSet target :: scope.openDecls } }

private theorem nonempty_hamiltonIveyPinchingSet (K s : Real) :
    {y : Real |
      ∃ d : Real, 0 < d ∧ y = d * _root_.Max.max s 0 + 2 * d * K * Real.exp (2 + (2 * d)⁻¹)}.Nonempty :=
  ⟨1 * _root_.Max.max s 0 + 2 * 1 * K * Real.exp (2 + (2 * 1)⁻¹), 1, one_pos, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.nonempty_hamiltonIveyPinchingSet
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.nonempty_hamiltonIveyPinchingSet target :: scope.openDecls } }

theorem hamiltonIveyPinchingBound_nonneg {K : Real} (hK : 0 ≤ K) (s : Real) :
    0 ≤ hamiltonIveyPinchingBound K s := by
  refine le_csInf (nonempty_hamiltonIveyPinchingSet K s) ?_
  rintro y ⟨d, hd, rfl⟩
  have h1 : 0 ≤ d * _root_.Max.max s 0 := mul_nonneg (le_of_lt hd) (le_max_right s 0)
  have h2 : 0 ≤ 2 * d * K * Real.exp (2 + (2 * d)⁻¹) :=
    mul_nonneg (mul_nonneg (by linarith) hK) (le_of_lt (Real.exp_pos _))
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound_nonneg

theorem hamiltonIveyPinchingBound_monotone {K : Real} (hK : 0 ≤ K) :
    Monotone (hamiltonIveyPinchingBound K) := by
  intro s1 s2 h12
  refine le_csInf (nonempty_hamiltonIveyPinchingSet K s2) ?_
  rintro y ⟨d, hd, rfl⟩
  have hle : hamiltonIveyPinchingBound K s1 ≤
      d * _root_.Max.max s1 0 + 2 * d * K * Real.exp (2 + (2 * d)⁻¹) :=
    csInf_le (bddBelow_hamiltonIveyPinchingSet hK s1) ⟨d, hd, rfl⟩
  have hmax : _root_.Max.max s1 0 ≤ _root_.Max.max s2 0 := max_le_max h12 (le_refl 0)
  nlinarith [hle, hmax, hd]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound_monotone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound_monotone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound_monotone ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound_monotone

theorem hamiltonIveyPinchingBound_le_affine {K : Real} (hK : 0 ≤ K) {d : Real} (hd : 0 < d)
    {s : Real} (hs : 0 ≤ s) :
    hamiltonIveyPinchingBound K s ≤ d * s + 2 * d * K * Real.exp (2 + (2 * d)⁻¹) := by
  have h : hamiltonIveyPinchingBound K s ≤
      d * _root_.Max.max s 0 + 2 * d * K * Real.exp (2 + (2 * d)⁻¹) :=
    csInf_le (bddBelow_hamiltonIveyPinchingSet hK s) ⟨d, hd, rfl⟩
  rwa [max_eq_left hs] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound_le_affine then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound_le_affine"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound_le_affine ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound_le_affine

theorem hamiltonIveyPinchingBound_le_of_nonpos {K : Real} (hK : 0 ≤ K) {s : Real} (hs : s ≤ 0) :
    hamiltonIveyPinchingBound K s ≤ K * Real.exp 3 := by
  have h : hamiltonIveyPinchingBound K s ≤
      1 / 2 * _root_.Max.max s 0 + 2 * (1 / 2) * K * Real.exp (2 + (2 * (1 / 2 : Real))⁻¹) :=
    csInf_le (bddBelow_hamiltonIveyPinchingSet hK s) ⟨1 / 2, by norm_num, rfl⟩
  have heq : 2 * (1 / 2 : Real) * K * Real.exp (2 + (2 * (1 / 2 : Real))⁻¹) = K * Real.exp 3 := by
    norm_num
  rw [max_eq_right hs, heq] at h
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound_le_of_nonpos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound_le_of_nonpos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound_le_of_nonpos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound_le_of_nonpos

theorem hamiltonIveyPinchingBound_quotient_tendsto {K : Real} (hK : 0 ≤ K) :
    Tendsto (fun s : Real => hamiltonIveyPinchingBound K s / s) _root_.Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  have hd : (0 : Real) < eps / 4 := by linarith
  obtain ⟨C, hC, hCle⟩ : ∃ C : Real, 0 ≤ C ∧ ∀ s : Real, 0 ≤ s →
      hamiltonIveyPinchingBound K s ≤ eps / 4 * s + C :=
    ⟨2 * (eps / 4) * K * Real.exp (2 + (2 * (eps / 4))⁻¹),
      mul_nonneg (mul_nonneg (by linarith) hK) (le_of_lt (Real.exp_pos _)),
      fun s hs => hamiltonIveyPinchingBound_le_affine hK hd hs⟩
  refine ⟨max 1 (4 * C / eps), ?_⟩
  intro s hs
  have hs1 : (1 : Real) ≤ s := le_trans (le_max_left _ _) hs
  have hspos : (0 : Real) < s := lt_of_lt_of_le zero_lt_one hs1
  have hsC : 4 * C / eps ≤ s := le_trans (le_max_right _ _) hs
  rw [div_le_iff₀ heps] at hsC
  have hCs : C / s ≤ eps / 4 := by
    rw [div_le_div_iff₀ hspos (by norm_num : (0 : Real) < 4)]
    linarith
  have hnn := hamiltonIveyPinchingBound_nonneg hK s
  have hdiv : hamiltonIveyPinchingBound K s / s ≤ eps / 4 + C / s := by
    rw [div_le_iff₀ hspos]
    have hexp : (eps / 4 + C / s) * s = eps / 4 * s + C := by
      field_simp
    rw [hexp]
    exact hCle s (le_of_lt hspos)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hnn (le_of_lt hspos))]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound_quotient_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound_quotient_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound_quotient_tendsto ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.hamiltonIveyPinchingBound_quotient_tendsto

private theorem half_neg_le_hamiltonIveyPinchingBound_of_fixedHamiltonIveyRegion
    {a₀ a R ν : ℝ} (ha₀ : 0 < a₀) (ha : a₀ ≤ a)
    (h : (R, ν) ∈ fixedHamiltonIveyRegion a) :
    -ν / 2 ≤ hamiltonIveyPinchingBound ((2 * a₀)⁻¹) R := by
  by_cases hν : 0 ≤ ν
  · exact (by linarith : -ν / 2 ≤ 0).trans
      (hamiltonIveyPinchingBound_nonneg (by positivity) R)
  have hX : 0 < -ν := by linarith
  have hbar : fixedHamiltonIveyBarrier a (-ν) ≤ R := h.resolve_left hν
  have hbar₀ : fixedHamiltonIveyBarrier a₀ (-ν) ≤ R := by
    apply le_trans ?_ hbar
    unfold fixedHamiltonIveyBarrier
    apply mul_le_mul_of_nonneg_left _ hX.le
    exact sub_le_sub_right (Real.log_le_log (mul_pos ha₀ hX)
      (mul_le_mul_of_nonneg_right ha hX.le)) 3
  unfold hamiltonIveyPinchingBound
  refine le_csInf ⟨1 * _root_.Max.max R 0 + 2 * 1 * (2 * a₀)⁻¹ * Real.exp (2 + (2 * 1 : ℝ)⁻¹),
    1, one_pos, rfl⟩ ?_
  rintro y ⟨d, hd, rfl⟩
  have hK : 0 < (2 * a₀)⁻¹ := by positivity
  have hbarhalf : hamiltonIveyBarrier ((2 * a₀)⁻¹) 0 (-ν / 2) ≤ R / 2 := by
    have heq := two_mul_hamiltonIveyBarrier_eq_fixedHamiltonIveyBarrier
      (K := (2 * a₀)⁻¹) (t := 0) hK le_rfl hX
    have hparam : (2 * (2 * a₀)⁻¹)⁻¹ + 0 = a₀ := by field_simp; ring
    rw [hparam] at heq
    linarith
  have hlin := pinchHeight_le_linear_sectionalSum_of_barrier hK hd le_rfl
    (by positivity : 0 ≤ -ν / 2) hbarhalf
  have hmax : d * R ≤ d * _root_.Max.max R 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hd.le
  simp only [_root_.MulZeroClass.mul_zero, add_zero, div_one] at hlin
  nlinarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.half_neg_le_hamiltonIveyPinchingBound_of_fixedHamiltonIveyRegion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.half_neg_le_hamiltonIveyPinchingBound_of_fixedHamiltonIveyRegion target :: scope.openDecls } }

theorem exists_admissiblePinchingFunction_neg_le_of_fixedHamiltonIveyRegion
    {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi ∧
      ∀ a : ℝ, a₀ ≤ a → ∀ R ν : ℝ,
        (R, ν) ∈ fixedHamiltonIveyRegion a → -ν ≤ Phi R := by
  let K := (2 * a₀)⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨Phi₀, hPhi₀, hge⟩ := exists_admissiblePinchingFunction_ge
    (psi := fun R => 2 * hamiltonIveyPinchingBound K R)
    (fun x _ y _ hxy => mul_le_mul_of_nonneg_left
      (hamiltonIveyPinchingBound_monotone hK.le hxy) (by norm_num))
    (fun R _ => mul_nonneg (by norm_num) (hamiltonIveyPinchingBound_nonneg hK.le R))
    (by
      have hlim := (hamiltonIveyPinchingBound_quotient_tendsto hK.le).const_mul 2
      simpa only [_root_.MulZeroClass.mul_zero, mul_div_assoc] using hlim)
  let C := 2 * K * Real.exp 3
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨fun R => Phi₀ R + C, hPhi₀.add_const hC, ?_⟩
  intro a ha R ν h
  have hb := half_neg_le_hamiltonIveyPinchingBound_of_fixedHamiltonIveyRegion ha₀ ha h
  change -ν / 2 ≤ hamiltonIveyPinchingBound K R at hb
  by_cases hR : 0 ≤ R
  · have hm := hge R hR
    dsimp only
    linarith
  · have hm := hamiltonIveyPinchingBound_le_of_nonpos hK.le (le_of_not_ge hR)
    have hp := hPhi₀.pos R
    dsimp [C]
    nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_neg_le_of_fixedHamiltonIveyRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_neg_le_of_fixedHamiltonIveyRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_neg_le_of_fixedHamiltonIveyRegion ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_neg_le_of_fixedHamiltonIveyRegion


omit [SigmaCompactSpace M] in
private theorem neg_leastCurvatureOperatorEigenvalueAt_le_hamiltonIveyPinchingBound
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t0 T K : Real} (hK : 0 < K)
    (hprop : curvatureOperatorRegionPropagationOn (I := I) (M := M) S K t0 T)
    {t : Real} (ht : t ∈ Set.Icc t0 (t0 + T)) (x : M) :
    -leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
        ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t) x⟩ ≤
      hamiltonIveyPinchingBound K (S.scalar t x) := by
  refine le_csInf (nonempty_hamiltonIveyPinchingSet K (S.scalar t x)) ?_
  rintro y ⟨d, hd, rfl⟩
  have hmain := hamilton_ivey_asymptotic_pinching_of_curvatureOperatorRegionPropagationOn
    (I := I) (M := M) S hK hd hprop t ht x
  have hpinch : -leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
      ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t) x⟩ ≤
      pinchHeight3 (leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
        ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t) x⟩) := le_max_left _ _
  have hden : (1 : Real) ≤ 1 + 2 * K * (t - t0) := by
    have h := ht.1
    nlinarith
  have hnum : 0 ≤ 2 * d * K * Real.exp (2 + (2 * d)⁻¹) :=
    mul_nonneg (mul_nonneg (by linarith) (le_of_lt hK)) (le_of_lt (Real.exp_pos _))
  have hfrac : 2 * d * K * Real.exp (2 + (2 * d)⁻¹) / (1 + 2 * K * (t - t0)) ≤
      2 * d * K * Real.exp (2 + (2 * d)⁻¹) := div_le_self hnum hden
  have hmax : d * S.scalar t x ≤ d * _root_.Max.max (S.scalar t x) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (le_of_lt hd)
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.neg_leastCurvatureOperatorEigenvalueAt_le_hamiltonIveyPinchingBound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.neg_leastCurvatureOperatorEigenvalueAt_le_hamiltonIveyPinchingBound target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
theorem exists_admissiblePinchingFunction_phiAlmostNonnegative_of_curvatureOperatorRegionPropagationOn
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t0 T K : Real} (hK : 0 < K)
    (hprop : curvatureOperatorRegionPropagationOn (I := I) (M := M) S K t0 T) :
    ∃ Phi : Real → Real, AdmissiblePinchingFunction Phi ∧
      PhiAlmostNonnegative (I := I) (M := M) S (Set.Icc t0 (t0 + T)) Phi := by
  obtain ⟨Phi0, hPhi0, hge⟩ := exists_admissiblePinchingFunction_ge
    (psi := hamiltonIveyPinchingBound K)
    (MonotoneOn.mono (Monotone.monotoneOn (hamiltonIveyPinchingBound_monotone (le_of_lt hK))
      Set.univ) (Set.subset_univ _))
    (fun s _ => hamiltonIveyPinchingBound_nonneg (le_of_lt hK) s)
    (hamiltonIveyPinchingBound_quotient_tendsto (le_of_lt hK))
  have hKexp : (0 : Real) < K * Real.exp 3 := mul_pos hK (Real.exp_pos 3)
  refine ⟨fun s => Phi0 s + K * Real.exp 3, hPhi0.add_const (le_of_lt hKexp), ?_⟩
  intro t ht x
  obtain ⟨basis, horth, _⟩ := hprop t ht x
  have hbound := neg_leastCurvatureOperatorEigenvalueAt_le_hamiltonIveyPinchingBound
    (I := I) (M := M) S hK hprop ht x
  have hkey : -leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
      ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t) x⟩ ≤ Phi0 (S.scalar t x) + K * Real.exp 3 := by
    rcases le_total 0 (S.scalar t x) with hR | hR
    · have h1 := hge (S.scalar t x) hR
      linarith
    · have h1 := hamiltonIveyPinchingBound_le_of_nonpos (le_of_lt hK) hR
      have h2 := hPhi0.pos (S.scalar t x)
      linarith
  have heq := leastCurvatureOperatorEigenvalueAt_eq_sectionalMin (I := I) (S.base.metric t) x
    basis horth
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩
  dsimp only
  rw [curvatureOperatorLowerBoundAt_iff_neg_sectionalMin_le (I := I) (S.base.metric t)
    basis horth
    (A := ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩)
    (K := Phi0 (S.scalar t x) + K * Real.exp 3), ← heq]
  exact hkey

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_of_curvatureOperatorRegionPropagationOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_of_curvatureOperatorRegionPropagationOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_of_curvatureOperatorRegionPropagationOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_of_curvatureOperatorRegionPropagationOn

omit [SigmaCompactSpace M] in
theorem exists_admissiblePinchingFunction_phiAlmostNonnegative_of_curvatureOperatorLowerBoundAt
    [I.Boundaryless] [CompactSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    {t0 T K : Real} (hT : 0 ≤ T) (hK : 0 < K)
    (hslab : Set.Icc t0 (t0 + T) ⊆ D.carrier)
    (hreg : Set.Ioo t0 (t0 + T) ⊆ D.regular)
    (hdim : Module.finrank Real E = 3)
    (hinit : ∀ x : M, curvatureOperatorLowerBoundAt (I := I) (S.base.metric t0) x
      ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t0) x⟩ K) :
    ∃ Phi : Real → Real, AdmissiblePinchingFunction Phi ∧
      PhiAlmostNonnegative (I := I) (M := M) S (Set.Icc t0 (t0 + T)) Phi :=
  exists_admissiblePinchingFunction_phiAlmostNonnegative_of_curvatureOperatorRegionPropagationOn
    (I := I) (M := M) S hK
    (curvatureOperatorRegionPropagationOn_of_initial_lower_bound (I := I) (M := M) S hS hT hK
      hslab hreg hdim hinit)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_of_curvatureOperatorLowerBoundAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_of_curvatureOperatorLowerBoundAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_of_curvatureOperatorLowerBoundAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_of_curvatureOperatorLowerBoundAt

theorem exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M]
    {a b : ℝ} (hab : a < b)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen a b hab))
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ E = 3) :
    ∃ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi ∧
      PhiAlmostNonnegative S (_root_.Set.Ico a b) Phi := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨K, hK, hKbound⟩ :=
    exists_curvatureOperatorLowerBoundAt_metricRm04 (S.base.metric a) hdim
  have hinit : ∀ x : M, curvatureOperatorLowerBoundAt (S.base.metric a) x
      ⟨S.base.rm04 a x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (S.base.metric a) x⟩ K := by
    simpa only [SolutionFamily.rm04, metricRm04_apply] using hKbound
  obtain ⟨Phi0, hPhi0, hge⟩ := exists_admissiblePinchingFunction_ge
    (psi := hamiltonIveyPinchingBound K)
    (MonotoneOn.mono (Monotone.monotoneOn (hamiltonIveyPinchingBound_monotone hK.le)
      Set.univ) (Set.subset_univ _))
    (fun s _ => hamiltonIveyPinchingBound_nonneg hK.le s)
    (hamiltonIveyPinchingBound_quotient_tendsto hK.le)
  have hKexp : (0 : ℝ) < K * Real.exp 3 := mul_pos hK (Real.exp_pos 3)
  refine ⟨fun s => Phi0 s + K * Real.exp 3, hPhi0.add_const hKexp.le, ?_⟩
  apply (phiAlmostNonnegative_iff_neg_le_leastCurvatureOperatorEigenvalueAt
    S (_root_.Set.Ico a b) (fun s => Phi0 s + K * Real.exp 3) hdim).mpr
  intro t ht x
  have hslab : _root_.Set.Icc a (a + (t - a)) ⊆
      (RealTimeInterval.closedOpen a b hab).carrier := by
    intro s hs
    exact ⟨hs.1, by linarith [hs.2, ht.2]⟩
  have hreg : _root_.Set.Ioo a (a + (t - a)) ⊆
      (RealTimeInterval.closedOpen a b hab).regular := by
    intro s hs
    exact ⟨hs.1, by linarith [hs.2, ht.2]⟩
  have htt : t ∈ _root_.Set.Icc a (a + (t - a)) := ⟨ht.1, by ring_nf; exact le_rfl⟩
  have hprop := curvatureOperatorRegionPropagationOn_of_initial_lower_bound
    S hS (sub_nonneg.mpr ht.1) hK hslab hreg hdim hinit
  have hbound := neg_leastCurvatureOperatorEigenvalueAt_le_hamiltonIveyPinchingBound
    S hK hprop htt x
  rcases le_total 0 (S.scalar t x) with hR | hR
  · have h1 := hge (S.scalar t x) hR
    linarith
  · have h1 := hamiltonIveyPinchingBound_le_of_nonpos hK.le hR
    have h2 := hPhi0.pos (S.scalar t x)
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen

section Rescaling

variable [IsManifold I 1 M]

omit [SigmaCompactSpace M] in
theorem phiAlmostNonnegative_paraSolution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {tau Q : Real} (hQ : 0 < Q) (htau : tau ∈ D.carrier) {W : Set Real} {Phi : Real → Real}
    (h : PhiAlmostNonnegative (I := I) (M := M) S W Phi) :
    PhiAlmostNonnegative (I := I) (M := M) (parabolicSolution (I := I) S tau Q hQ htau)
      {s : Real | parabolicTime tau Q s ∈ W} (rescalePinchingFunction Q Phi) := by
  intro s hs x
  have hbase := h (parabolicTime tau Q s) hs x
  have hscalar : (parabolicSolution (I := I) S tau Q hQ htau).scalar s x =
      Q⁻¹ * S.scalar (parabolicTime tau Q s) x := by
    rw [parabolicSolution_scalar]
  have hrescale : rescalePinchingFunction Q Phi
      ((parabolicSolution (I := I) S tau Q hQ htau).scalar s x) =
      Q⁻¹ * Phi (S.scalar (parabolicTime tau Q s) x) := by
    rw [hscalar]
    unfold rescalePinchingFunction
    congr 2
    field_simp
  rw [hrescale]
  refine (curvatureOperatorLowerBoundAt_scaleMetric_smul_iff (I := I) (M := M) hQ
    (S.base.metric (parabolicTime tau Q s)) _ x
    ⟨S.base.rm04 (parabolicTime tau Q s) x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric (parabolicTime tau Q s)) x⟩ _
    (Phi (S.scalar (parabolicTime tau Q s) x)) rfl ?_).mpr hbase
  exact parabolicSolution_rm04 (I := I) S tau Q hQ htau s x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.phiAlmostNonnegative_paraSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.phiAlmostNonnegative_paraSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.phiAlmostNonnegative_paraSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.phiAlmostNonnegative_paraSolution

omit [SigmaCompactSpace M] in
theorem exists_admissiblePinchingFunction_phiAlmostNonnegative_paraSolution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t0 T K Q : Real} (hK : 0 < K) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier)
    (hprop : curvatureOperatorRegionPropagationOn (I := I) (M := M) S K t0 T) :
    ∃ Phi : Real → Real, AdmissiblePinchingFunction (rescalePinchingFunction Q Phi) ∧
      PhiAlmostNonnegative (I := I) (M := M) (parabolicSolution (I := I) S t0 Q hQ ht0)
        {s : Real | parabolicTime t0 Q s ∈ Set.Icc t0 (t0 + T)} (rescalePinchingFunction Q Phi) := by
  obtain ⟨Phi, hPhi, hanc⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_of_curvatureOperatorRegionPropagationOn
      (I := I) (M := M) S hK hprop
  exact ⟨Phi, hPhi.rescale hQ, phiAlmostNonnegative_paraSolution (I := I) (M := M) S hQ ht0 hanc⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_paraSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_paraSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_paraSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_admissiblePinchingFunction_phiAlmostNonnegative_paraSolution

end Rescaling

end Perelman

end DifferentialGeometry.PDE.RicciFlow
