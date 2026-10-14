import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter _root_.Metric
open scoped _root_.Topology _root_.ContDiff

open _root_.HasFTaylorSeriesUpToOn in
theorem HasFTaylorSeriesUpToOn.closure_of_continuousOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ∞ω} {f : E → F} {p : E → FormalMultilinearSeries ℝ E F} {s : Set E}
    (hp : HasFTaylorSeriesUpToOn n f p s) (hs : Convex ℝ s) (ho : IsOpen s)
    (hf : ContinuousOn f (closure s))
    (hc : ∀ k : ℕ, k ≤ n → ContinuousOn (fun x => p x k) (closure s)) :
    HasFTaylorSeriesUpToOn n f p (closure s) := by
  refine ⟨?_, ?_, hc⟩
  · exact (show _root_.Set.EqOn (fun x => (p x 0).curry0) f s from hp.zero_eq).of_subset_closure
      ((continuousMultilinearCurryFin0 ℝ E F).continuous.comp_continuousOn
        (hc 0 (by simp))) hf subset_closure Subset.rfl
  · intro k hk x hx
    have hk1 : ((k + 1 : ℕ) : ℕ∞ω) ≤ n := ENat.add_one_natCast_le_withTop_of_lt hk
    have hd (y : E) (hy : y ∈ s) :
        HasFDerivAt (fun z => p z k) (p y (k + 1)).curryLeft y :=
      (hp.fderivWithin k hk y hy).hasFDerivAt (ho.mem_nhds hy)
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt) hs ho
      (fun y hy => (hc k hk.le y hy).mono subset_closure)
    have ht : _root_.Filter.Tendsto (fun y => (p y (k + 1)).curryLeft) (𝓝[s] x)
        (𝓝 ((p x (k + 1)).curryLeft)) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).continuous.tendsto _ |>.comp
        ((hc (k + 1) hk1 x hx).mono subset_closure)
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hd y hy).fderiv.symm

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.HasFTaylorSeriesUpToOn
  let env ← Lean.getEnv
  if env.contains `HasFTaylorSeriesUpToOn.closure_of_continuousOn then
    throwError "Refusing to shadow existing declaration HasFTaylorSeriesUpToOn.closure_of_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `HasFTaylorSeriesUpToOn.closure_of_continuousOn ``Submission.HasFTaylorSeriesUpToOn.closure_of_continuousOn

namespace DifferentialGeometry.Analysis

theorem contDiffOn_closure_of_continuousOn_jets
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ∞} {f : E → F} {p : E → FormalMultilinearSeries ℝ E F} {s : Set E}
    (hs : Convex ℝ s) (ho : IsOpen s) (hf : ContDiffOn ℝ n f s)
    (hfc : ContinuousOn f (closure s))
    (hc : ∀ k : ℕ, k ≤ n → ContinuousOn (fun x => p x k) (closure s))
    (he : ∀ k : ℕ, k ≤ n → _root_.Set.EqOn (fun x => p x k) (iteratedFDeriv ℝ k f) s) :
    ContDiffOn ℝ n f (closure s) ∧
      ∀ k : ℕ, k ≤ n → _root_.Set.EqOn (fun x => p x k) (iteratedFDerivWithin ℝ k f (closure s)) (closure s) := by
  have hp : HasFTaylorSeriesUpToOn n f p s := by
    apply (hf.ftaylorSeriesWithin ho.uniqueDiffOn).congr_series
    intro k hk x hx
    rw [he k (by exact_mod_cast hk) hx]
    exact iteratedFDerivWithin_of_isOpen k ho hx
  have hpc := hp.closure_of_continuousOn hs ho hfc (fun k hk => hc k (by exact_mod_cast hk))
  refine ⟨hpc.contDiffOn, ?_⟩
  have hUD : UniqueDiffOn ℝ (closure s) := by
    rcases _root_.Set.eq_empty_or_nonempty s with rfl | hne
    · simp [UniqueDiffOn]
    · apply uniqueDiffOn_convex hs.closure
      apply hne.mono
      simpa only [ho.interior_eq] using
        (interior_mono subset_closure : interior s ⊆ interior (closure s))
  intro k hk x hx
  exact hpc.eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast hk) hUD hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiffOn_closure_of_continuousOn_jets then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiffOn_closure_of_continuousOn_jets"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiffOn_closure_of_continuousOn_jets ``Submission.DifferentialGeometry.Analysis.contDiffOn_closure_of_continuousOn_jets

end DifferentialGeometry.Analysis
