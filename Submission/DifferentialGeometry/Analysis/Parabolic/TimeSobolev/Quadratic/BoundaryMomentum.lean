import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.C1Regularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.intervalIntegral
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} {T : ℝ}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X]

private theorem mom_ramp_ftc
    (hT : 0 < T) (P F r r' : ℝ → X)
    (hP : ContDiffOn ℝ 1 P (_root_.Set.Icc (0 : ℝ) T))
    (hPF : _root_.Set.EqOn (derivWithin P (_root_.Set.Icc (0 : ℝ) T)) F
      (_root_.Set.Icc (0 : ℝ) T))
    (hr : ContDiffOn ℝ 1 r (_root_.Set.Icc (0 : ℝ) T))
    (hr' : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      HasDerivWithinAt r (r' t) (_root_.Set.Icc (0 : ℝ) T) t) :
    ∫ t in (0 : ℝ)..T,
        (_root_.Inner.inner ℝ (F t) (r t) + _root_.Inner.inner ℝ (P t) (r' t)) =
      inner ℝ (P T) (r T) - _root_.Inner.inner ℝ (P 0) (r 0) := by
  let φ : ℝ → ℝ := fun t ↦ _root_.Inner.inner ℝ (P t) (r t)
  have hφ : ContDiffOn ℝ 1 φ (_root_.Set.Icc (0 : ℝ) T) := hP.inner ℝ hr
  have huniq : UniqueDiffOn ℝ (_root_.Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  have hφd : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      derivWithin φ (_root_.Set.Icc (0 : ℝ) T) t =
        inner ℝ (F t) (r t) + _root_.Inner.inner ℝ (P t) (r' t) := by
    intro t ht
    have hPd : HasDerivWithinAt P
        (derivWithin P (_root_.Set.Icc (0 : ℝ) T) t) (_root_.Set.Icc (0 : ℝ) T) t :=
      ((hP t ht).differentiableWithinAt one_ne_zero).hasDerivWithinAt
    have hd := (hPd.inner ℝ (hr' t ht)).derivWithin
      (huniq.uniqueDiffWithinAt ht)
    rw [hPF ht] at hd
    simpa only [φ, add_comm] using hd
  calc
    ∫ t in (0 : ℝ)..T,
        (_root_.Inner.inner ℝ (F t) (r t) + _root_.Inner.inner ℝ (P t) (r' t)) =
        ∫ t in (0 : ℝ)..T,
          derivWithin φ (_root_.Set.Icc (0 : ℝ) T) t := by
            apply intervalIntegral.integral_congr
            intro t ht
            rw [_root_.Set.uIcc_of_le hT.le] at ht
            exact (hφd t ht).symm
    _ = φ T - φ 0 :=
      intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc hφ hT.le
    _ = _root_.Inner.inner ℝ (P T) (r T) - _root_.Inner.inner ℝ (P 0) (r 0) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.mom_ramp_ftc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.mom_ramp_ftc target :: scope.openDecls } }

theorem mom_ramp_up
    (hT : 0 < T) (P F : ℝ → X)
    (hP : ContDiffOn ℝ 1 P (_root_.Set.Icc (0 : ℝ) T))
    (hPF : _root_.Set.EqOn (derivWithin P (_root_.Set.Icc (0 : ℝ) T)) F
      (_root_.Set.Icc (0 : ℝ) T)) (z : X) :
    ∫ t in (0 : ℝ)..T,
        (_root_.Inner.inner ℝ (F t) ((t / T) • z) +
          _root_.Inner.inner ℝ (P t) ((1 / T) • z)) =
      inner ℝ (P T) z := by
  have hr : ContDiffOn ℝ 1 (fun t : ℝ ↦ (t / T) • z)
      (_root_.Set.Icc (0 : ℝ) T) :=
    ((contDiff_id.div_const T).smul_const z).contDiffOn
  have hr' : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s : ℝ ↦ (s / T) • z) ((1 / T) • z)
        (_root_.Set.Icc (0 : ℝ) T) t := by
    intro t _
    exact (((hasDerivAt_id t).div_const T).smul_const z).hasDerivWithinAt
  have hTT : T / T = 1 := div_self hT.ne'
  simpa only [hTT, one_smul, zero_div, zero_smul, inner_zero_right,
    sub_zero] using
    mom_ramp_ftc hT P F (fun t : ℝ ↦ (t / T) • z)
      (fun _ ↦ (1 / T) • z) hP hPF hr hr'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.mom_ramp_up then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.mom_ramp_up"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.mom_ramp_up ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.mom_ramp_up

theorem mom_ramp_down
    (hT : 0 < T) (P F : ℝ → X)
    (hP : ContDiffOn ℝ 1 P (_root_.Set.Icc (0 : ℝ) T))
    (hPF : _root_.Set.EqOn (derivWithin P (_root_.Set.Icc (0 : ℝ) T)) F
      (_root_.Set.Icc (0 : ℝ) T)) (z : X) :
    ∫ t in (0 : ℝ)..T,
        (_root_.Inner.inner ℝ (F t) (((T - t) / T) • z) +
          _root_.Inner.inner ℝ (P t) ((-(1 / T)) • z)) =
      -_root_.Inner.inner ℝ (P 0) z := by
  have hr : ContDiffOn ℝ 1 (fun t : ℝ ↦ ((T - t) / T) • z)
      (_root_.Set.Icc (0 : ℝ) T) :=
    (((contDiff_const.sub contDiff_id).div_const T).smul_const z).contDiffOn
  have hr' : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s : ℝ ↦ ((T - s) / T) • z)
        ((-(1 / T)) • z) (_root_.Set.Icc (0 : ℝ) T) t := by
    intro t _
    simpa only [Pi.sub_apply, id_eq, zero_sub, neg_div, one_div] using
      ((((hasDerivAt_const t T).sub (hasDerivAt_id t)).div_const T).smul_const z).hasDerivWithinAt
  have hTT : T / T = 1 := div_self hT.ne'
  simpa only [sub_self, sub_zero, zero_div, zero_smul, inner_zero_right, zero_sub,
    hTT, one_smul] using
    mom_ramp_ftc hT P F (fun t : ℝ ↦ ((T - t) / T) • z)
      (fun _ ↦ (-(1 / T)) • z) hP hPF hr hr'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.mom_ramp_down then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.mom_ramp_down"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.mom_ramp_down ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.mom_ramp_down

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
