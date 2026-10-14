import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Submission.DifferentialGeometry.Topology.UniformConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

open _root_.Filter _root_.Set _root_.MeasureTheory
open scoped _root_.Topology _root_.Submission.Topology

theorem exists_tendstoUniformlyOn_left_endpoint_of_integrable_deriv_bound
    {X F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {a b : ℝ} (hab : a < b) {U : Set X} (f d : ℝ → X → F) (B : ℝ → ℝ)
    (hderiv : ∀ t ∈ _root_.Set.Ioo a b, ∀ x ∈ U, HasDerivAt (fun s => f s x) (d t x) t)
    (hbound : ∀ t ∈ _root_.Set.Ioo a b, ∀ x ∈ U, ‖d t x‖ ≤ B t)
    (hint : IntervalIntegrable B _root_.MeasureTheory.MeasureSpace.volume a b) :
    ∃ g : X → F, TendstoUniformlyOn f g (𝓝[_root_.Set.Ioo a b] a) U := by
  let m : ℝ → ℝ := fun t => ∫ r in a..t, B r
  have ha : a ∈ _root_.Set.uIcc a b := _root_.Set.left_mem_uIcc
  have hmem : ∀ t ∈ _root_.Set.Ioo a b, t ∈ _root_.Set.uIcc a b := by
    intro t ht
    rw [_root_.Set.uIcc_of_le hab.le]
    exact ⟨ht.1.le, ht.2.le⟩
  have hm : _root_.Filter.Tendsto m (𝓝[_root_.Set.Ioo a b] a) (𝓝 0) := by
    have hc := (intervalIntegral.continuousOn_primitive_interval' hint ha) a ha
    have hl := hc.mono (fun t ht => hmem t ht)
    simpa only [intervalIntegral.integral_same] using hl.tendsto
  apply exists_tendstoUniformlyOn_left_endpoint_of_time_modulus hab f m hm
  have hordered : ∀ s ∈ _root_.Set.Ioo a b, ∀ t ∈ _root_.Set.Ioo a b, s ≤ t → ∀ x ∈ U,
      dist (f t x) (f s x) ≤ |m t - m s| := by
    intro s hs t ht hst x hx
    have hsub : _root_.Set.Icc s t ⊆ _root_.Set.Ioo a b := by
      intro r hr
      exact ⟨hs.1.trans_le hr.1, hr.2.trans_lt ht.2⟩
    have hd : ∀ r ∈ _root_.Set.Icc s t, HasDerivAt (fun v => f v x) (d r x) r :=
      fun r hr => hderiv r (hsub hr) x hx
    have hc : ContinuousOn (fun r => f r x) (_root_.Set.Icc s t) :=
      fun r hr => (hd r hr).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ (fun r => f r x) (_root_.Set.Ioo s t) :=
      fun r hr => (hd r ⟨hr.1.le, hr.2.le⟩).differentiableAt.differentiableWithinAt
    have hb : ∀ᵐ r, r ∈ _root_.Set.Ioo s t → ‖deriv (fun v => f v x) r‖ ≤ B r := by
      exact Eventually.of_forall fun r hr => by
        rw [(hd r ⟨hr.1.le, hr.2.le⟩).deriv]
        exact hbound r (hsub ⟨hr.1.le, hr.2.le⟩) x hx
    have hist := hint.mono_set (_root_.Set.uIcc_subset_uIcc (hmem s hs) (hmem t ht))
    have hib : ∀ r ∈ _root_.Set.Ioo a b, IntervalIntegrable B _root_.MeasureTheory.MeasureSpace.volume a r :=
      fun r hr => hint.mono_set (_root_.Set.uIcc_subset_uIcc ha (hmem r hr))
    have hi := norm_sub_le_integral_of_norm_deriv_le_of_le hst hc hdiff hb hist
    calc
      dist (f t x) (f s x) = ‖f t x - f s x‖ := dist_eq_norm _ _
      _ ≤ ∫ r in s..t, B r := hi
      _ = m t - m s := (intervalIntegral.integral_interval_sub_left (hib t ht) (hib s hs)).symm
      _ ≤ |m t - m s| := le_abs_self _
  intro s hs t ht x hx
  rcases le_total s t with hst | hts
  · simpa only [dist_comm, abs_sub_comm] using hordered s hs t ht hst x hx
  · exact hordered t ht s hs hts x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_tendstoUniformlyOn_left_endpoint_of_integrable_deriv_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_tendstoUniformlyOn_left_endpoint_of_integrable_deriv_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_tendstoUniformlyOn_left_endpoint_of_integrable_deriv_bound ``Submission.DifferentialGeometry.Analysis.exists_tendstoUniformlyOn_left_endpoint_of_integrable_deriv_bound

end DifferentialGeometry.Analysis
