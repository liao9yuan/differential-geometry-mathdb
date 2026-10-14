import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardForwardNeck

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Filter _root_.Set
open scoped _root_.Topology _root_.Submission.Topology


theorem backwardForward_time_error_le (a s : ℝ) (hs : s ∈ _root_.Set.Icc (-1 : ℝ) 0) :
    |(1 - s / a) - (1 - s)| ≤ |a⁻¹ - 1| := by
  have hidentity : (1 - s / a) - (1 - s) = s * (1 - a⁻¹) := by
    rw [div_eq_mul_inv]
    ring
  have hsabs : |s| ≤ 1 := abs_le.mpr ⟨hs.1, hs.2.trans zero_le_one⟩
  rw [hidentity, abs_mul, abs_sub_comm 1]
  exact (mul_le_mul_of_nonneg_right hsabs (abs_nonneg (a⁻¹ - 1))).trans_eq
    (one_mul _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForward_time_error_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForward_time_error_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForward_time_error_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForward_time_error_le


theorem backwardForward_jet_coefficient_tendsto
    {a : ℕ → ℝ} (ha : _root_.Filter.Tendsto a _root_.Filter.atTop (𝓝 (1 : ℝ))) (q : ℕ) :
    Tendsto (fun i => a i * (-(a i)⁻¹) ^ q) _root_.Filter.atTop (𝓝 ((-1 : ℝ) ^ q)) := by
  simpa only [inv_one, one_mul] using ha.mul ((ha.inv₀ one_ne_zero).neg.pow q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForward_jet_coefficient_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForward_jet_coefficient_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForward_jet_coefficient_tendsto ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForward_jet_coefficient_tendsto


theorem backwardForward_weighted_jet_convergence
    {α : Type*} (F : ℕ → ℝ → α → ℝ) (F₀ : ℝ → α → ℝ) (w : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t ∈ _root_.Set.Icc (1 : ℝ) 3, ∀ x, |F₀ t x| ≤ B * w x)
    (hLip : ∀ s ∈ _root_.Set.Icc (1 : ℝ) 3, ∀ t ∈ _root_.Set.Icc (1 : ℝ) 3, ∀ x,
      |F₀ s x - F₀ t x| ≤ B * w x * |s - t|)
    (hconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ i in _root_.Filter.atTop,
      ∀ t ∈ _root_.Set.Icc (1 : ℝ) 3, ∀ x, |F i t x - F₀ t x| ≤ eta * w x)
    {a : ℕ → ℝ} (ha : _root_.Filter.Tendsto a _root_.Filter.atTop (𝓝 (1 : ℝ))) (q : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ i in _root_.Filter.atTop,
      ∀ s ∈ _root_.Set.Icc (-1 : ℝ) 0, ∀ x,
        |(a i * (-(a i)⁻¹) ^ q) * F i (1 - s / a i) x -
          (-1 : ℝ) ^ q * F₀ (1 - s) x| ≤ epsilon * w x := by
  let c : ℕ → ℝ := fun i => a i * (-(a i)⁻¹) ^ q
  let c₀ : ℝ := (-1 : ℝ) ^ q
  have hc : _root_.Filter.Tendsto c _root_.Filter.atTop (𝓝 c₀) := backwardForward_jet_coefficient_tendsto ha q
  have hinv : _root_.Filter.Tendsto (fun i => (a i)⁻¹) _root_.Filter.atTop (𝓝 (1 : ℝ)) := by
    simpa only [inv_one] using ha.inv₀ one_ne_zero
  have hcabs : _root_.Filter.Tendsto (fun i => |c i|) _root_.Filter.atTop (𝓝 (1 : ℝ)) := by
    simpa only [c₀, abs_pow, abs_neg, abs_one, one_pow] using hc.abs
  have hhalf : ∀ᶠ i in _root_.Filter.atTop, (1 : ℝ) / 2 ≤ a i :=
    ((tendsto_order.1 ha).1 (1 / 2) (by norm_num)).mono fun _ hi => hi.le
  have hcoeff : ∀ᶠ i in _root_.Filter.atTop, |c i| ≤ 2 :=
    ((tendsto_order.1 hcabs).2 2 (by norm_num)).mono fun _ hi => hi.le
  have herror : _root_.Filter.Tendsto (fun i =>
      2 * B * |(a i)⁻¹ - 1| + B * |c i - c₀|) _root_.Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, abs_zero, _root_.MulZeroClass.mul_zero, add_zero] using
      (((hinv.sub_const 1).abs.const_mul (2 * B)).add
        ((hc.sub_const c₀).abs.const_mul B))
  intro epsilon hepsilon
  have hsmall : ∀ᶠ i in _root_.Filter.atTop,
      2 * B * |(a i)⁻¹ - 1| + B * |c i - c₀| ≤ epsilon / 2 :=
    ((tendsto_order.1 herror).2 (epsilon / 2) (by positivity)).mono fun _ hi => hi.le
  filter_upwards [hhalf, hcoeff, hsmall, hconv (epsilon / 4) (by positivity)]
    with i hhalf_i hcoeff_i hsmall_i hconv_i
  intro s hs x
  have htheta : 1 - s / a i ∈ _root_.Set.Icc (1 : ℝ) 3 := backwardForward_time_mapsTo hhalf_i hs
  have htheta₀ : 1 - s ∈ _root_.Set.Icc (1 : ℝ) 3 := by
    constructor <;> linarith [hs.1, hs.2]
  have hweight : 0 ≤ B * w x := mul_nonneg hB (hw x)
  have htime : |F₀ (1 - s / a i) x - F₀ (1 - s) x| ≤
      B * w x * |(a i)⁻¹ - 1| :=
    (hLip _ htheta _ htheta₀ x).trans
      (mul_le_mul_of_nonneg_left (backwardForward_time_error_le (a i) s hs) hweight)
  have hidentity : c i * F i (1 - s / a i) x - c₀ * F₀ (1 - s) x =
      c i * (F i (1 - s / a i) x - F₀ (1 - s / a i) x) +
        c i * (F₀ (1 - s / a i) x - F₀ (1 - s) x) +
          (c i - c₀) * F₀ (1 - s) x := by ring
  change |c i * F i (1 - s / a i) x - c₀ * F₀ (1 - s) x| ≤ _
  calc
    _ = |c i * (F i (1 - s / a i) x - F₀ (1 - s / a i) x) +
        c i * (F₀ (1 - s / a i) x - F₀ (1 - s) x) +
          (c i - c₀) * F₀ (1 - s) x| := congrArg abs hidentity
    _ ≤ |c i| * |F i (1 - s / a i) x - F₀ (1 - s / a i) x| +
        |c i| * |F₀ (1 - s / a i) x - F₀ (1 - s) x| +
          |c i - c₀| * |F₀ (1 - s) x| := by
      simpa only [abs_mul] using (abs_add_le
        (c i * (F i (1 - s / a i) x - F₀ (1 - s / a i) x) +
          c i * (F₀ (1 - s / a i) x - F₀ (1 - s) x))
        ((c i - c₀) * F₀ (1 - s) x)).trans
        (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |c i| * ((epsilon / 4) * w x + B * w x * |(a i)⁻¹ - 1|) +
        |c i - c₀| * (B * w x) := by
      rw [mul_add]
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left (hconv_i _ htheta x) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left htime (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left (hbound _ htheta₀ x) (abs_nonneg _))
    _ ≤ 2 * ((epsilon / 4) * w x + B * w x * |(a i)⁻¹ - 1|) +
        |c i - c₀| * (B * w x) := by
      have hnonneg : 0 ≤ (epsilon / 4) * w x + B * w x * |(a i)⁻¹ - 1| :=
        add_nonneg (mul_nonneg (by positivity) (hw x))
          (mul_nonneg hweight (abs_nonneg _))
      exact add_le_add (mul_le_mul_of_nonneg_right hcoeff_i hnonneg) le_rfl
    _ = (epsilon / 2 + (2 * B * |(a i)⁻¹ - 1| + B * |c i - c₀|)) * w x := by ring
    _ ≤ epsilon * w x := mul_le_mul_of_nonneg_right (by linarith) (hw x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForward_weighted_jet_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForward_weighted_jet_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForward_weighted_jet_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForward_weighted_jet_convergence

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
