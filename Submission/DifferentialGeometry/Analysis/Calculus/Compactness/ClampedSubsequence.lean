import Submission.DifferentialGeometry.Analysis.Calculus.Compactness.DiagonalSubsequence
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace ContinuousMap

open _root_.Filter _root_.Set
open scoped _root_.Topology

universe u
variable {X : Type u} [TopologicalSpace X]

theorem exists_subsequence_clamped_Ico_of_eventually_continuousOn
    {ell : ℝ} (hell : 0 < ell) (f : ℕ → ℝ → X)
    (hcontinuous : ∀ r : ℝ, 0 ≤ r → r < ell →
      ∀ᶠ n in _root_.Filter.atTop, ContinuousOn (f n) (_root_.Set.Icc (0 : ℝ) r)) :
    ∃ (sigma : ℕ → ℕ) (T : ℕ → ℝ) (beta : ℕ → C(_root_.Set.Ico (0 : ℝ) ell, X)),
      StrictMono sigma ∧ StrictMono T ∧ (∀ n, T n ∈ _root_.Set.Ioo (0 : ℝ) ell) ∧
      _root_.Filter.Tendsto T _root_.Filter.atTop (𝓝 ell) ∧
      (∀ n (s : _root_.Set.Ico (0 : ℝ) ell), beta n s = f (sigma n) (_root_.Min.min (s : ℝ) (T n))) ∧
      (∀ r : ℝ, r < ell → ∀ᶠ n in _root_.Filter.atTop,
        ∀ s : _root_.Set.Ico (0 : ℝ) ell, (s : ℝ) ≤ r → beta n s = f (sigma n) s) := by
  classical
  obtain ⟨T, hTmono, hT, hTlim⟩ := exists_seq_strictMono_tendsto' hell
  have hthreshold (j : ℕ) : ∃ N : ℕ, ∀ n ≥ N,
      ContinuousOn (f n) (_root_.Set.Icc (0 : ℝ) (T j)) :=
    eventually_atTop.mp (hcontinuous (T j) (hT j).1.le (hT j).2)
  choose N hN using hthreshold
  obtain ⟨sigma, hsigma, hsigN⟩ :=
    DifferentialGeometry.CheegerGromovCompactness.exists_strictMono_ge N
  let beta (n : ℕ) : C(_root_.Set.Ico (0 : ℝ) ell, X) :=
    ⟨fun s => f (sigma n) (_root_.Min.min (s : ℝ) (T n)),
      (hN n (sigma n) (hsigN n)).comp_continuous
        (continuous_subtype_val.min continuous_const) fun s =>
          ⟨le_min s.property.1 (hT n).1.le, min_le_right _ _⟩⟩
  refine ⟨sigma, T, beta, hsigma, hTmono, hT, hTlim, fun _ _ => rfl, ?_⟩
  intro r hr
  filter_upwards [hTlim.eventually (lt_mem_nhds hr)] with n hn
  intro s hs
  change f (sigma n) (_root_.Min.min (s : ℝ) (T n)) = f (sigma n) s
  rw [min_eq_left (hs.trans hn.le)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousMap.exists_subsequence_clamped_Ico_of_eventually_continuousOn then
    throwError "Refusing to shadow existing declaration ContinuousMap.exists_subsequence_clamped_Ico_of_eventually_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousMap.exists_subsequence_clamped_Ico_of_eventually_continuousOn ``Submission.ContinuousMap.exists_subsequence_clamped_Ico_of_eventually_continuousOn

end ContinuousMap

end
