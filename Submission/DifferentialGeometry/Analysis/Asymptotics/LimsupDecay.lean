import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Submission.DifferentialGeometry.Analysis.Asymptotics.PowerDecay

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter
open scoped _root_.Topology

namespace Filter
open _root_.Filter

open _root_.Filter in
theorem limsup_le_mul_limsup_of_eventually_le_add_tendsto_zero
    {ι : Type*} {l : Filter ι} [_root_.Filter.NeBot l] {a b ε : ι → ℝ} {θ : ℝ}
    (hθ : 0 ≤ θ) (ha : ∀ᶠ i in l, 0 ≤ a i)
    (hbound : _root_.Filter.IsBoundedUnder (· ≤ ·) l a) (hb : ∀ᶠ i in l, 0 ≤ b i)
    (hε : _root_.Filter.Tendsto ε l (𝓝 0)) (hle : ∀ᶠ i in l, b i ≤ θ * a i + ε i) :
    limsup b l ≤ θ * _root_.Filter.limsup a l := by
  have hp0 : ∀ᶠ i in l, 0 ≤ θ * a i := ha.mono fun i hi => mul_nonneg hθ hi
  have hpbound : _root_.Filter.IsBoundedUnder (· ≤ ·) l (fun i => θ * a i) := by
    obtain ⟨C, hC⟩ := hbound
    refine ⟨θ * C, ?_⟩
    exact hC.mono fun i hi => mul_le_mul_of_nonneg_left hi hθ
  have hsumBound : _root_.Filter.IsBoundedUnder (· ≤ ·) l (fun i => θ * a i + ε i) :=
    _root_.Filter.isBoundedUnder_le_add hpbound hε.isBoundedUnder_le
  have hmul : _root_.Filter.limsup (fun i => θ * a i) l ≤ θ * _root_.Filter.limsup a l := by
    have h := limsup_mul_le
      ((Eventually.of_forall fun _ : ι => hθ).frequently)
      (show _root_.Filter.IsBoundedUnder (· ≤ ·) l (fun _ : ι => θ) from
        (tendsto_const_nhds (x := θ)).isBoundedUnder_le)
      ha hbound
    simpa only [Pi.mul_def, _root_.Filter.limsup_const] using h
  have hadd : _root_.Filter.limsup (fun i => θ * a i + ε i) l ≤ _root_.Filter.limsup (fun i => θ * a i) l := by
    have h := limsup_add_le
      (_root_.Filter.isBoundedUnder_of_eventually_ge hp0) hpbound
      hε.isBoundedUnder_ge.isCoboundedUnder_le hε.isBoundedUnder_le
    simpa only [Pi.add_def, hε.limsup_eq, add_zero] using h
  exact (_root_.Filter.limsup_le_limsup hle
    (_root_.Filter.isBoundedUnder_of_eventually_ge hb).isCoboundedUnder_le hsumBound).trans (hadd.trans hmul)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Filter.limsup_le_mul_limsup_of_eventually_le_add_tendsto_zero then
    throwError "Refusing to shadow existing declaration Filter.limsup_le_mul_limsup_of_eventually_le_add_tendsto_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `Filter.limsup_le_mul_limsup_of_eventually_le_add_tendsto_zero ``Submission.Filter.limsup_le_mul_limsup_of_eventually_le_add_tendsto_zero

open _root_.Filter in
private theorem isBoundedUnder_of_eventually_le_succ
    {ι : Type*} {l : Filter ι}
    (a ε : ℕ → ι → ℝ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hbound : _root_.Filter.IsBoundedUnder (· ≤ ·) l (a 0))
    (hε : ∀ k, _root_.Filter.Tendsto (ε k) l (𝓝 0))
    (hrec : ∀ k, ∀ᶠ i in l, a (k + 1) i ≤ θ * a k i + ε k i)
    (k : ℕ) : _root_.Filter.IsBoundedUnder (· ≤ ·) l (a k) := by
  induction k with
  | zero => exact hbound
  | succ k ih =>
    have hp : _root_.Filter.IsBoundedUnder (· ≤ ·) l (fun i => θ * a k i) := by
      obtain ⟨C, hC⟩ := ih.eventually_le
      refine ⟨θ * C, ?_⟩
      change ∀ᶠ i in l, θ * a k i ≤ θ * C
      exact hC.mono fun i hi => mul_le_mul_of_nonneg_left hi hθ
    exact (_root_.Filter.isBoundedUnder_le_add hp (hε k).isBoundedUnder_le).mono_le (hrec k)

run_cmd do
  let target := ``Submission.Filter.isBoundedUnder_of_eventually_le_succ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Filter.isBoundedUnder_of_eventually_le_succ target :: scope.openDecls } }

open _root_.Filter in
theorem limsup_le_pow_mul_limsup_of_eventually_le_succ
    {ι : Type*} {l : Filter ι} [_root_.Filter.NeBot l]
    (a ε : ℕ → ι → ℝ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hnonneg : ∀ k, ∀ᶠ i in l, 0 ≤ a k i)
    (hbound : _root_.Filter.IsBoundedUnder (· ≤ ·) l (a 0))
    (hε : ∀ k, _root_.Filter.Tendsto (ε k) l (𝓝 0))
    (hrec : ∀ k, ∀ᶠ i in l, a (k + 1) i ≤ θ * a k i + ε k i)
    (k : ℕ) : _root_.Filter.limsup (a k) l ≤ θ ^ k * _root_.Filter.limsup (a 0) l := by
  induction k with
  | zero => simp only [pow_zero, one_mul, le_refl]
  | succ k ih =>
    calc
      limsup (a (k + 1)) l ≤ θ * _root_.Filter.limsup (a k) l :=
        limsup_le_mul_limsup_of_eventually_le_add_tendsto_zero
          hθ (hnonneg k) (isBoundedUnder_of_eventually_le_succ a ε hθ hbound hε hrec k)
          (hnonneg (k + 1)) (hε k) (hrec k)
      _ ≤ θ * (θ ^ k * _root_.Filter.limsup (a 0) l) := mul_le_mul_of_nonneg_left ih hθ
      _ = θ ^ (k + 1) * _root_.Filter.limsup (a 0) l := by rw [pow_succ]; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Filter.limsup_le_pow_mul_limsup_of_eventually_le_succ then
    throwError "Refusing to shadow existing declaration Filter.limsup_le_pow_mul_limsup_of_eventually_le_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `Filter.limsup_le_pow_mul_limsup_of_eventually_le_succ ``Submission.Filter.limsup_le_pow_mul_limsup_of_eventually_le_succ

open _root_.Filter in
theorem le_pow_mul_of_le_liminf_of_eventually_le_succ
    {ι : Type*} {l : Filter ι} [_root_.Filter.NeBot l]
    (a ε : ℕ → ι → ℝ) (e : ℕ → ℝ) {θ B : ℝ} (hθ : 0 ≤ θ)
    (hnonneg : ∀ k, ∀ᶠ i in l, 0 ≤ a k i)
    (hB : ∀ᶠ i in l, a 0 i ≤ B)
    (hε : ∀ k, _root_.Filter.Tendsto (ε k) l (𝓝 0))
    (hrec : ∀ k, ∀ᶠ i in l, a (k + 1) i ≤ θ * a k i + ε k i)
    (he : ∀ k, e k ≤ _root_.Filter.liminf (a k) l) (k : ℕ) : e k ≤ θ ^ k * B := by
  have hbound : _root_.Filter.IsBoundedUnder (· ≤ ·) l (a 0) := _root_.Filter.isBoundedUnder_of_eventually_le hB
  have hzero : _root_.Filter.limsup (a 0) l ≤ B :=
    _root_.Filter.limsup_le_of_le (_root_.Filter.isBoundedUnder_of_eventually_ge (hnonneg 0)).isCoboundedUnder_le hB
  exact (he k).trans ((_root_.Filter.liminf_le_limsup
    (isBoundedUnder_of_eventually_le_succ a ε hθ hbound hε hrec k)
    (_root_.Filter.isBoundedUnder_of_eventually_ge (hnonneg k))).trans
      ((limsup_le_pow_mul_limsup_of_eventually_le_succ a ε hθ hnonneg hbound hε hrec k).trans
        (mul_le_mul_of_nonneg_left hzero (pow_nonneg hθ k))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Filter.le_pow_mul_of_le_liminf_of_eventually_le_succ then
    throwError "Refusing to shadow existing declaration Filter.le_pow_mul_of_le_liminf_of_eventually_le_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `Filter.le_pow_mul_of_le_liminf_of_eventually_le_succ ``Submission.Filter.le_pow_mul_of_le_liminf_of_eventually_le_succ

open _root_.Filter in
theorem tendsto_zero_of_le_liminf_of_eventually_le_succ
    {ι : Type*} {l : Filter ι} [_root_.Filter.NeBot l]
    (a ε : ℕ → ι → ℝ) (e : ℕ → ℝ) {θ B : ℝ}
    (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hnonneg : ∀ k, ∀ᶠ i in l, 0 ≤ a k i)
    (hB : ∀ᶠ i in l, a 0 i ≤ B)
    (hε : ∀ k, _root_.Filter.Tendsto (ε k) l (𝓝 0))
    (hrec : ∀ k, ∀ᶠ i in l, a (k + 1) i ≤ θ * a k i + ε k i)
    (he0 : ∀ k, 0 ≤ e k) (he : ∀ k, e k ≤ _root_.Filter.liminf (a k) l) :
    Tendsto e _root_.Filter.atTop (𝓝 0) := by
  apply squeeze_zero he0
    (le_pow_mul_of_le_liminf_of_eventually_le_succ a ε e hθ hnonneg hB hε hrec he)
  simpa only [_root_.MulZeroClass.zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ hθ1).mul_const B

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Filter.tendsto_zero_of_le_liminf_of_eventually_le_succ then
    throwError "Refusing to shadow existing declaration Filter.tendsto_zero_of_le_liminf_of_eventually_le_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `Filter.tendsto_zero_of_le_liminf_of_eventually_le_succ ``Submission.Filter.tendsto_zero_of_le_liminf_of_eventually_le_succ

end Filter

end

noncomputable section

open _root_.Set _root_.Filter _root_.Submission.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis

theorem exists_radius_power_bound_of_dyadic_decay
    {ι : Type*} (E : ι → ℝ → ℝ) {δ θ B : ℝ}
    (hδ : 0 < δ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hB : 0 ≤ B)
    (hmono : ∀ c, MonotoneOn (E c) (_root_.Set.Ioc (0 : ℝ) δ))
    (hdec : ∀ c k, E c (δ / (2 : ℝ) ^ k) ≤ θ ^ k * B) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧
      ∀ c r, r ∈ _root_.Set.Ioc (0 : ℝ) δ → E c r ≤ C * r ^ (2 * α) := by
  let t : ℝ := _root_.Max.max θ (1 / 2)
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_right _ _)
  have ht1 : t < 1 := max_lt hθ1 (by norm_num)
  have htθ : θ ≤ t := le_max_left _ _
  let q : ℝ := -Real.log t / Real.log 2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq0 : 0 < q := div_pos (neg_pos.mpr (Real.log_neg ht0 ht1)) hl2
  have hq1 : q ≤ 1 := by
    apply (div_le_one hl2).mpr
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) (le_max_right θ (1 / 2))
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at hlog
    dsimp only [t] at hlog ⊢
    linarith
  have hpow : (1 / 2 : ℝ) ^ q = t := by
    rw [Real.rpow_def_of_pos (by norm_num), Real.log_div (by norm_num) (by norm_num), Real.log_one]
    have heq : (0 - Real.log 2) * q = Real.log t := by
      dsimp only [q]
      field_simp
      ring
    rw [heq, Real.exp_log ht0]
  let C := B / ((1 / 2 : ℝ) * δ) ^ q
  refine ⟨q / 2, C, half_pos hq0, by linarith, by dsimp [C]; positivity, ?_⟩
  intro c r hr
  have h := radius_power_bound_of_geometric_decay (E := E c)
    (θ := (1 / 2 : ℝ)) (R := δ) (q := q) (M := B)
    (by norm_num) (by norm_num) hδ hq0.le hB (hmono c) (fun k => ?_) r hr
  · simpa only [C, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using h
  · rw [hpow]
    have heq : (1 / 2 : ℝ) ^ k * δ = δ / (2 : ℝ) ^ k := by rw [div_pow]; ring
    rw [heq]
    exact (hdec c k).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hθ htθ k) hB)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_radius_power_bound_of_dyadic_decay then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_radius_power_bound_of_dyadic_decay"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_radius_power_bound_of_dyadic_decay ``Submission.DifferentialGeometry.Analysis.exists_radius_power_bound_of_dyadic_decay

end DifferentialGeometry.Analysis

end
