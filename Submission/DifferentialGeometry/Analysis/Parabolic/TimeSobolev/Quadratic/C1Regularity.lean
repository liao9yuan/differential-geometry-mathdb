import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.L1Regularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.intervalIntegral
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*}
variable {T : ℝ}

section Primitive

variable [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem primitive_c1
    (hT : 0 < T) (F : ℝ → X)
    (hF : ContinuousOn F (_root_.Set.Icc (0 : ℝ) T)) (c : X) :
    ContDiffOn ℝ 1 (fun t ↦ c + ∫ r in (0 : ℝ)..t, F r)
        (_root_.Set.Icc (0 : ℝ) T) ∧
      _root_.Set.EqOn (derivWithin (fun t ↦ c + ∫ r in (0 : ℝ)..t, F r)
        (_root_.Set.Icc (0 : ℝ) T)) F (_root_.Set.Icc (0 : ℝ) T) := by
  have hFint : _root_.MeasureTheory.IntegrableOn F (_root_.Set.Icc (0 : ℝ) T) volume :=
    hF.integrableOn_compact _root_.CompactIccSpace.isCompact_Icc
  have hd : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s ↦ c + ∫ r in (0 : ℝ)..s, F r) (F t)
        (_root_.Set.Icc (0 : ℝ) T) t := by
    intro t ht
    have : Fact (t ∈ _root_.Set.Icc (0 : ℝ) T) := ⟨ht⟩
    have hint : IntervalIntegrable F _root_.MeasureTheory.MeasureSpace.volume 0 t :=
      MeasureTheory.IntegrableOn.intervalIntegrable (by
        rw [_root_.Set.uIcc_of_le ht.1]
        exact hFint.mono_set (_root_.Set.Icc_subset_Icc le_rfl ht.2))
    have hmeas : StronglyMeasurableAtFilter F
        (𝓝[_root_.Set.Icc (0 : ℝ) T] t) volume :=
      ⟨Icc (0 : ℝ) T, self_mem_nhdsWithin,
        hF.aestronglyMeasurable measurableSet_Icc⟩
    exact (intervalIntegral.integral_hasDerivWithinAt_right hint hmeas
      (hF t ht)).const_add c
  have huniq : UniqueDiffOn ℝ (_root_.Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  have heq : _root_.Set.EqOn
      (derivWithin (fun t ↦ c + ∫ r in (0 : ℝ)..t, F r)
        (_root_.Set.Icc (0 : ℝ) T)) F (_root_.Set.Icc (0 : ℝ) T) := by
    intro t ht
    exact (hd t ht).derivWithin (huniq.uniqueDiffWithinAt ht)
  refine ⟨?_, heq⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
    contDiffOn_succ_iff_derivWithin huniq]
  refine ⟨fun t ht ↦ (hd t ht).differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  exact hF.congr fun _ ht ↦ heq ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.primitive_c1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.primitive_c1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.primitive_c1 ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.primitive_c1

end Primitive

section Inner

variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

theorem mom_rep_c1
    (hT : 0 < T)
    (A : ℝ → X →L[ℝ] X)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (u : timeH1 X T) (F : ℝ → X)
    (hF : ContinuousOn F (_root_.Set.Icc (0 : ℝ) T))
    (hEuler : ∀ v : timeH1 X T, v.initial = 0 → v.toFun T = 0 →
      2 * _root_.Inner.inner ℝ (timeOp A hA C hC u.deriv) v.deriv +
        ∫ t in _root_.Set.Icc (0 : ℝ) T, _root_.Inner.inner ℝ (F t) (v.toFun t) = 0) :
    ∃ c : X,
      ((fun t ↦ (2 : ℝ) • A t (u.deriv t))
        =ᵐ[volume.restrict (_root_.Set.Ioo (0 : ℝ) T)]
          fun t ↦ c + ∫ r in (0 : ℝ)..t, F r) ∧
      ContDiffOn ℝ 1 (fun t ↦ c + ∫ r in (0 : ℝ)..t, F r)
        (_root_.Set.Icc (0 : ℝ) T) ∧
      _root_.Set.EqOn (derivWithin (fun t ↦ c + ∫ r in (0 : ℝ)..t, F r)
        (_root_.Set.Icc (0 : ℝ) T)) F (_root_.Set.Icc (0 : ℝ) T) := by
  have hFint : _root_.MeasureTheory.IntegrableOn F (_root_.Set.Icc (0 : ℝ) T) volume :=
    hF.integrableOn_compact _root_.CompactIccSpace.isCompact_Icc
  obtain ⟨c, hc⟩ := mom_primitive_l1 hT A hA C hC u F hFint hEuler
  obtain ⟨hc1, hderiv⟩ := primitive_c1 hT F hF c
  exact ⟨c, hc, hc1, hderiv⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.mom_rep_c1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.mom_rep_c1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.mom_rep_c1 ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.mom_rep_c1

end Inner

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
