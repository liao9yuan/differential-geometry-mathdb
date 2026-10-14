import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

section

variable {X : Type*} [NormedAddCommGroup X] [CompleteSpace X]

theorem deriv_ae_of_eqOn [NormedSpace ℝ X]
    {T : ℝ} (hT : 0 < T) (u : timeH1 X T)
    (f : ℝ → X) (hf : ContDiff ℝ 1 f)
    (heq : _root_.Set.EqOn u.toFun f (_root_.Set.Icc (0 : ℝ) T)) :
    u.deriv =ᵐ[timeMeasure T] _root_.deriv f := by
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ _root_.Set.Ioo (0 : ℝ) T := by
    unfold timeMeasure
    rw [← _root_.MeasureTheory.restrict_Ioo_eq_restrict_Icc]
    exact _root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo
  filter_upwards [u.ae_hasDerivWithinAt_toFun, hmem] with t hu ht
  have htIcc : t ∈ _root_.Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
  have huniq := (uniqueDiffOn_Icc hT).uniqueDiffWithinAt htIcc
  have hfAt : HasDerivAt f (_root_.deriv f t) t :=
    ((hf.differentiable (by norm_num)) t).hasDerivAt
  calc
    u.deriv t = derivWithin u.toFun (_root_.Set.Icc (0 : ℝ) T) t :=
      (hu.derivWithin huniq).symm
    _ = derivWithin f (_root_.Set.Icc (0 : ℝ) T) t :=
      derivWithin_congr heq (heq htIcc)
    _ = _root_.deriv f t :=
      hfAt.hasDerivWithinAt.derivWithin huniq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.deriv_ae_of_eqOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.deriv_ae_of_eqOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.deriv_ae_of_eqOn ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.deriv_ae_of_eqOn

end

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {T : ℝ}

theorem toFun_c1_of_rep
    (hT : 0 < T) (u : timeH1 X T) (w : ℝ → X)
    (hw : ContinuousOn w (_root_.Set.Icc (0 : ℝ) T))
    (hrep : u.deriv =ᵐ[timeMeasure T] w) :
    ContDiffOn ℝ 1 u.toFun (_root_.Set.Icc (0 : ℝ) T) ∧
      EqOn (derivWithin u.toFun (_root_.Set.Icc (0 : ℝ) T)) w (_root_.Set.Icc (0 : ℝ) T) := by
  have hd : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      HasDerivWithinAt u.toFun (w t) (_root_.Set.Icc (0 : ℝ) T) t :=
    fun t ht ↦ u.hasDerivWithinAt_toFun_of_continuousOn hw hrep ht
  have huniq : UniqueDiffOn ℝ (_root_.Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  have heq : _root_.Set.EqOn (derivWithin u.toFun (_root_.Set.Icc (0 : ℝ) T)) w
      (_root_.Set.Icc (0 : ℝ) T) := by
    intro t ht
    exact (hd t ht).derivWithin (huniq.uniqueDiffWithinAt ht)
  refine ⟨?_, heq⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
    contDiffOn_succ_iff_derivWithin huniq]
  refine ⟨fun t ht ↦ (hd t ht).differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  exact hw.congr fun _ ht ↦ heq ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.toFun_c1_of_rep then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.toFun_c1_of_rep"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.toFun_c1_of_rep ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.toFun_c1_of_rep

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
