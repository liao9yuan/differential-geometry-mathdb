/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Filter _root_.Topology

namespace DifferentialGeometry.Analysis

variable {E Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace Q]

theorem lipschitzOnWith_of_eventually_dist_le {f : E → Q} {s : Set E} {C : NNReal}
    (hs : Convex ℝ s)
    (hlocal : ∀ x ∈ s, ∀ᶠ y in 𝓝[s] x, _root_.Dist.dist (f y) (f x) ≤ C * _root_.Dist.dist y x) :
    LipschitzOnWith C f s := by
  have hf : ContinuousOn f s := by
    intro x hx
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hden : 0 < (C : ℝ) + 1 := by positivity
    filter_upwards [hlocal x hx, mem_nhdsWithin_of_mem_nhds
      (Metric.ball_mem_nhds x (div_pos hε hden))] with y hy hyx
    have hdist : _root_.Dist.dist y x < ε / ((C : ℝ) + 1) := hyx
    have hmul : _root_.Dist.dist y x * ((C : ℝ) + 1) < ε := (lt_div_iff₀ hden).mp hdist
    have hd0 : 0 ≤ _root_.Dist.dist y x := dist_nonneg
    nlinarith
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  let γ : ℝ → E := fun t => x + t • (y - x)
  have hγ : Continuous γ := by fun_prop
  have hγs : _root_.Set.MapsTo γ (_root_.Set.Icc 0 1) s := fun _ ht => hs.add_smul_sub_mem hx hy ht
  let g : ℝ → ℝ := fun t => _root_.Dist.dist (f (γ t)) (f x)
  let c : ℝ := C * ‖y - x‖
  have hg : ContinuousOn g (_root_.Set.Icc 0 1) := by
    intro t ht
    exact (hf.comp hγ.continuousOn hγs t ht).dist tendsto_const_nhds
  have hg0 : g 0 ≤ c * 0 := by simp [g, γ]
  have hB : ContinuousOn (fun t : ℝ => c * t) (_root_.Set.Icc 0 1) := by fun_prop
  have hB' : ∀ t ∈ _root_.Set.Ico (0 : ℝ) 1,
      HasDerivWithinAt (fun z : ℝ => c * z) c (_root_.Set.Ici t) t := by
    intro t _
    have hderiv : HasDerivAt (fun z : ℝ => c * z) (c * 1) t := (hasDerivAt_id t).const_mul c
    simpa only [mul_one] using hderiv.hasDerivWithinAt (s := _root_.Set.Ici t)
  have hbound : ∀ t ∈ _root_.Set.Ico (0 : ℝ) 1, ∀ r, c < r → ∃ᶠ z in 𝓝[>] t, slope g t z < r := by
    intro t ht r hr
    have hzI : ∀ᶠ z in 𝓝[>] t, z ∈ _root_.Set.Icc (0 : ℝ) 1 := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds ht.2)]
        with z hzt hz1
      exact ⟨ht.1.trans hzt.le, hz1.le⟩
    have hγt : _root_.Filter.Tendsto γ (𝓝[>] t) (𝓝[s] (γ t)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hγ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
        hzI.mono fun z hz => hγs hz⟩
    have hnear := hγt.eventually (hlocal (γ t) (hγs ⟨ht.1, ht.2.le⟩))
    apply Eventually.frequently
    filter_upwards [hnear, self_mem_nhdsWithin] with z hz hzt
    have hpos : 0 < z - t := sub_pos.mpr hzt
    have hd : _root_.Dist.dist (γ z) (γ t) = (z - t) * ‖y - x‖ := by
      rw [dist_eq_norm]
      change ‖(x + z • (y - x)) - (x + t • (y - x))‖ = _
      rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    have hinc : g z - g t ≤ c * (z - t) := by
      have htri := dist_triangle (f (γ z)) (f (γ t)) (f x)
      rw [hd] at hz
      dsimp [g, c]
      nlinarith
    rw [slope_def_field]
    exact (div_le_iff₀ hpos).mpr hinc |>.trans_lt hr
  have h := image_le_of_liminf_slope_right_le_deriv_boundary hg hg0 hB hB' hbound
    (right_mem_Icc.mpr (show (0 : ℝ) ≤ 1 by norm_num))
  simpa only [g, γ, one_smul, add_sub_cancel, mul_one, c, ← dist_eq_norm, dist_comm] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.lipschitzOnWith_of_eventually_dist_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.lipschitzOnWith_of_eventually_dist_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.lipschitzOnWith_of_eventually_dist_le ``Submission.DifferentialGeometry.Analysis.lipschitzOnWith_of_eventually_dist_le

theorem lipschitzOnWith_of_continuous_finite_selection {ι : Type*} [Finite ι]
    {f : E → Q} {g : ι → E → Q} {s : Set E} {C : NNReal} (hs : Convex ℝ s)
    (hf : ContinuousOn f s) (hg : ∀ i, LipschitzOnWith C (g i) s)
    (hselect : ∀ x ∈ s, ∃ i, f x = g i x) : LipschitzOnWith C f s := by
  apply lipschitzOnWith_of_eventually_dist_le hs
  intro x hx
  have hactive : ∀ i, ∀ᶠ y in 𝓝[s] x, _root_.Dist.dist (f y) (g i y) = 0 → _root_.Dist.dist (f x) (g i x) = 0 := by
    intro i
    by_cases hzero : _root_.Dist.dist (f x) (g i x) = 0
    · exact Eventually.of_forall fun _ _ => hzero
    · have hpos : 0 < _root_.Dist.dist (f x) (g i x) := lt_of_le_of_ne dist_nonneg (Ne.symm hzero)
      have hnear : ∀ᶠ y in 𝓝[s] x, 0 < _root_.Dist.dist (f y) (g i y) :=
        ((hf x hx).dist ((hg i).continuousOn x hx)).eventually (eventually_gt_nhds hpos)
      filter_upwards [hnear] with y hy hzero'
      exact (ne_of_gt hy hzero').elim
  filter_upwards [eventually_all.mpr hactive, self_mem_nhdsWithin] with y hy hys
  obtain ⟨i, hi⟩ := hselect y hys
  have hzero : _root_.Dist.dist (f x) (g i x) = 0 := hy i (by rw [hi, dist_self])
  rw [hi]
  calc _root_.Dist.dist (g i y) (f x) ≤ _root_.Dist.dist (g i y) (g i x) + _root_.Dist.dist (g i x) (f x) := dist_triangle _ _ _
    _ = _root_.Dist.dist (g i y) (g i x) := by rw [dist_comm (g i x), hzero, add_zero]
    _ ≤ C * _root_.Dist.dist y x := (hg i).dist_le_mul y hys x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.lipschitzOnWith_of_continuous_finite_selection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.lipschitzOnWith_of_continuous_finite_selection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.lipschitzOnWith_of_continuous_finite_selection ``Submission.DifferentialGeometry.Analysis.lipschitzOnWith_of_continuous_finite_selection

theorem lipschitzWith_of_continuous_finite_selection {ι : Type*} [Finite ι]
    {f : E → Q} {g : ι → E → Q} {C : NNReal} (hf : Continuous f)
    (hg : ∀ i, LipschitzWith C (g i)) (hselect : ∀ x, ∃ i, f x = g i x) :
    LipschitzWith C f := by
  rw [← lipschitzOnWith_univ]
  exact lipschitzOnWith_of_continuous_finite_selection convex_univ hf.continuousOn
    (fun i => (hg i).lipschitzOnWith) (fun x _ => hselect x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.lipschitzWith_of_continuous_finite_selection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.lipschitzWith_of_continuous_finite_selection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.lipschitzWith_of_continuous_finite_selection ``Submission.DifferentialGeometry.Analysis.lipschitzWith_of_continuous_finite_selection

theorem exists_lipschitzWith_of_continuous_finite_affine_selection [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Finite ι]
    {f : E → F} (A : ι → E →ᵃ[ℝ] F) (hf : Continuous f) (hselect : ∀ x, ∃ i, f x = A i x) :
    ∃ C : NNReal, LipschitzWith C f := by
  classical
  cases nonempty_fintype ι
  let C : NNReal := Finset.univ.sup fun i => ‖(A i).linear.toContinuousLinearMap‖₊
  refine ⟨C, lipschitzWith_of_continuous_finite_selection hf
    (g := fun i => A i) (fun i => ?_) hselect⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hbound : ‖(A i).linear.toContinuousLinearMap‖₊ ≤ C :=
    Finset.le_sup (f := fun i => ‖(A i).linear.toContinuousLinearMap‖₊) (Finset.mem_univ i)
  have hdiff : A i x - A i y = (A i).linear (x - y) := ((A i).linearMap_vsub x y).symm
  calc _root_.Dist.dist (A i x) (A i y) = ‖(A i).linear (x - y)‖ := by rw [dist_eq_norm, hdiff]
    _ ≤ ‖(A i).linear.toContinuousLinearMap‖ * ‖x - y‖ :=
      (A i).linear.toContinuousLinearMap.le_opNorm _
    _ ≤ C * _root_.Dist.dist x y := by
      rw [dist_eq_norm]
      exact mul_le_mul_of_nonneg_right (show (‖(A i).linear.toContinuousLinearMap‖₊ : ℝ) ≤ C from
        NNReal.coe_le_coe.mpr hbound) (norm_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_lipschitzWith_of_continuous_finite_affine_selection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_lipschitzWith_of_continuous_finite_affine_selection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_lipschitzWith_of_continuous_finite_affine_selection ``Submission.DifferentialGeometry.Analysis.exists_lipschitzWith_of_continuous_finite_affine_selection

end DifferentialGeometry.Analysis
