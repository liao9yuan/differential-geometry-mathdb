import Submission.DifferentialGeometry.Analysis.Sobolev.Embedding.Tensor.Cm
import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.Space
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Analysis.Parabolic

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem maxreg_l2deriv_to_pointwise_hasderivwithinat
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] {T : ℝ} (u : timeH1 X T) {g : ℝ → X}
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) T))
    (hrep : u.deriv =ᵐ[timeMeasure T] g) :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt u.toFun (g t) (Set.Ici (0 : ℝ)) t := by
  intro t ht
  have ht_icc : t ∈ Set.Icc (0 : ℝ) T :=
    ⟨ht.1, le_of_lt ht.2⟩
  have hderivIcc : HasDerivWithinAt u.toFun (g t) (Set.Icc (0 : ℝ) T) t :=
    u.hasDerivWithinAt_toFun_of_continuousOn hg hrep ht_icc
  have hIic : Set.Iic T ∈ nhds t := Iic_mem_nhds ht.2
  have hmem : Set.Icc (0 : ℝ) T ∈ nhdsWithin t (Set.Ici (0 : ℝ)) := by
    have : Set.Ici (0 : ℝ) ∩ Set.Iic T ∈ nhdsWithin t (Set.Ici (0 : ℝ)) :=
      inter_mem_nhdsWithin _ hIic
    simpa [Set.Ici_inter_Iic] using this
  exact hderivIcc.mono_of_mem_nhdsWithin hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.maxreg_l2deriv_to_pointwise_hasderivwithinat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.maxreg_l2deriv_to_pointwise_hasderivwithinat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.maxreg_l2deriv_to_pointwise_hasderivwithinat ``Submission.DifferentialGeometry.Analysis.Parabolic.maxreg_l2deriv_to_pointwise_hasderivwithinat

theorem hasDerivAt_clm_apply_from_h1_time
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : ℝ → X →L[ℝ] Y) (L' : ℝ → X →L[ℝ] Y) (u : ℝ → X) (u' : ℝ → X)
    (t : ℝ)
    (hL : HasDerivAt L (L' t) t) (hu : HasDerivAt u (u' t) t) :
    HasDerivAt (fun s : ℝ => L s (u s)) (L' t (u t) + L t (u' t)) t :=
  hL.clm_apply hu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.hasDerivAt_clm_apply_from_h1_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.hasDerivAt_clm_apply_from_h1_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.hasDerivAt_clm_apply_from_h1_time ``Submission.DifferentialGeometry.Analysis.Parabolic.hasDerivAt_clm_apply_from_h1_time

end DifferentialGeometry.Analysis.Parabolic
