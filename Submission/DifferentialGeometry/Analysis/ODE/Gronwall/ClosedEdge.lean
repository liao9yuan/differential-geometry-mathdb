import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.MeanValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Filter _root_.Set
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis.ODE

theorem le_gronwallBound_of_hasDerivAt_on_Ioo
    {u u' : ℝ → ℝ} {a b δ K ε : ℝ}
    (hcont : ContinuousOn u (_root_.Set.Icc a b))
    (hderiv : ∀ t ∈ _root_.Set.Ioo a b, HasDerivAt u (u' t) t)
    (hinit : u a ≤ δ)
    (hsub : ∀ t ∈ _root_.Set.Ioo a b, u' t ≤ K * u t + ε) :
    ∀ t ∈ _root_.Set.Icc a b, u t ≤ gronwallBound δ K ε (t - a) := by
  let g (t : ℝ) := gronwallBound δ K ε (t - a)
  have hgd (t : ℝ) : HasDerivAt g (K * g t + ε) t :=
    hasDerivAt_gronwallBound_shift δ K ε t a
  let f (t : ℝ) := Real.exp (-K * t) * (u t - g t)
  have hc : ContinuousOn f (_root_.Set.Icc a b) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      (hcont.sub (fun t _ => (hgd t).continuousAt.continuousWithinAt))
  have hd (t : ℝ) (ht : t ∈ _root_.Set.Ioo a b) :
      HasDerivAt f (Real.exp (-K * t) * (u' t - K * u t - ε)) t := by
    convert (((hasDerivAt_id t).const_mul (-K)).exp.mul
      ((hderiv t ht).sub (hgd t))) using 1 <;>
      first | rfl | (simp only [id_eq, Pi.sub_apply, mul_one]; ring)
  have hm : AntitoneOn f (_root_.Set.Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hc
    · intro t ht
      exact (hd t (by simpa only [interior_Icc] using ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have hti : t ∈ _root_.Set.Ioo a b := by simpa only [interior_Icc] using ht
      rw [(hd t hti).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith [hsub t hti])
  intro t ht
  have hfa : f a ≤ 0 := by
    have hg : g a = δ := by simp only [g, sub_self, gronwallBound_x0]
    dsimp only [f]
    rw [hg]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr hinit)
  have hf := (hm ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1).trans hfa
  have hn : u t - g t ≤ 0 := nonpos_of_mul_nonpos_right hf (Real.exp_pos _)
  exact sub_nonpos.mp hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.le_gronwallBound_of_hasDerivAt_on_Ioo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.le_gronwallBound_of_hasDerivAt_on_Ioo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.le_gronwallBound_of_hasDerivAt_on_Ioo ``Submission.DifferentialGeometry.Analysis.ODE.le_gronwallBound_of_hasDerivAt_on_Ioo

theorem gronwall_zero_on {a c K : ℝ} (hac : a < c)
    (energy energy' : ℝ → ℝ)
    (hcont : ContinuousOn energy (_root_.Set.Icc a c))
    (hzero : energy a = 0)
    (hnonneg : ∀ t ∈ _root_.Set.Icc a c, 0 ≤ energy t)
    (hderiv : ∀ t ∈ _root_.Set.Ioo a c, HasDerivAt energy (energy' t) t)
    (hbound : ∀ t ∈ _root_.Set.Ioo a c, energy' t ≤ K * energy t) :
    ∀ t ∈ _root_.Set.Icc a c, energy t = 0 := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | htpos
  · exact hzero
  have hlimc : _root_.Filter.Tendsto energy (nhdsWithin a (_root_.Set.Ioo a c)) (𝓝 0) := by
    have hlim := (hcont a ⟨le_rfl, hac.le⟩).tendsto.mono_left
      (nhdsWithin_mono a _root_.Set.Ioo_subset_Icc_self)
    simpa only [hzero] using hlim
  have hsub : _root_.Set.Ioo a t ⊆ _root_.Set.Ioo a c := fun s hs =>
    ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩
  have hlim : _root_.Filter.Tendsto energy (nhdsWithin a (_root_.Set.Ioo a t)) (𝓝 0) :=
    hlimc.mono_left (nhdsWithin_mono a hsub)
  have : (nhdsWithin a (_root_.Set.Ioo a t)).NeBot := by
    rw [nhdsWithin_Ioo_eq_nhdsGT htpos]
    infer_instance
  have heps : _root_.Filter.Tendsto (fun ε : ℝ => ε) (nhdsWithin a (_root_.Set.Ioo a t)) (𝓝 a) :=
    (continuous_id.tendsto a).mono_left nhdsWithin_le_nhds
  have harg : _root_.Filter.Tendsto (fun ε : ℝ => K * (t - ε))
      (nhdsWithin a (_root_.Set.Ioo a t)) (𝓝 (K * (t - a))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub heps)
  have hexp : _root_.Filter.Tendsto (fun ε : ℝ => Real.exp (K * (t - ε)))
      (nhdsWithin a (_root_.Set.Ioo a t)) (𝓝 (Real.exp (K * (t - a)))) :=
    Real.continuous_exp.continuousAt.tendsto.comp harg
  have hrhs : _root_.Filter.Tendsto (fun ε : ℝ => energy ε * Real.exp (K * (t - ε)))
      (nhdsWithin a (_root_.Set.Ioo a t)) (𝓝 0) := by
    simpa only [_root_.MulZeroClass.zero_mul] using hlim.mul hexp
  have hev : ∀ᶠ ε in nhdsWithin a (_root_.Set.Ioo a t),
      energy t ≤ energy ε * Real.exp (K * (t - ε)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hcontε : ContinuousOn energy (_root_.Set.Icc ε t) :=
      hcont.mono (_root_.Set.Icc_subset_Icc hε.1.le ht.2)
    have hslope : ∀ x ∈ _root_.Set.Ico ε t, ∀ r, energy' x < r →
        ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (energy z - energy x) < r := by
      intro x hx r hr
      have hxc : x ∈ _root_.Set.Ioo a c :=
        ⟨lt_of_lt_of_le hε.1 hx.1, lt_of_lt_of_le hx.2 ht.2⟩
      exact (hderiv x hxc).hasDerivWithinAt.liminf_right_slope_le hr
    have hgr := le_gronwallBound_of_liminf_deriv_right_le
      (ε := 0) hcontε hslope le_rfl
      (fun x hx => by
        have hxc : x ∈ _root_.Set.Ioo a c :=
          ⟨lt_of_lt_of_le hε.1 hx.1, lt_of_lt_of_le hx.2 ht.2⟩
        simpa only [add_zero] using hbound x hxc) t ⟨hε.2.le, le_rfl⟩
    simpa only [gronwallBound_ε0] using hgr
  exact le_antisymm (ge_of_tendsto hrhs hev) (hnonneg t ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.gronwall_zero_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.gronwall_zero_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.gronwall_zero_on ``Submission.DifferentialGeometry.Analysis.ODE.gronwall_zero_on

end DifferentialGeometry.Analysis.ODE
