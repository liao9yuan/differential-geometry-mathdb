import Mathlib.Topology.Order.Compact


import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Tactic.Order

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open _root_.Filter _root_.Topology

theorem exists_subseq_tendsto_pi {C : ℕ → ℝ} (f : ℕ → ℕ → ℝ)
    (hbd : ∀ n k, f n k ∈ Set.Icc (0 : ℝ) (C n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n, ∃ L ∈ Set.Icc (0 : ℝ) (C n),
        Tendsto (fun k => f n (φ k)) _root_.Filter.atTop (𝓝 L) := by
  have : ∀ n : ℕ, CompactSpace (Set.Icc (0 : ℝ) (C n)) :=
    fun n => isCompact_iff_compactSpace.mp _root_.CompactIccSpace.isCompact_Icc
  set x : ℕ → (Π n : ℕ, Set.Icc (0 : ℝ) (C n)) := fun k n => ⟨f n k, hbd n k⟩ with hx
  obtain ⟨a, -, φ, hφ, ha⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (Π n : ℕ, Set.Icc (0 : ℝ) (C n)))).tendsto_subseq
      (x := x) (fun k => Set.mem_univ _)
  refine ⟨φ, hφ, fun n => ⟨(a n : ℝ), (a n).2, ?_⟩⟩
  have h1 : _root_.Filter.Tendsto (fun k => x (φ k) n) _root_.Filter.atTop (𝓝 (a n)) := by
    exact (tendsto_pi_nhds.mp ha) n
  have h2 := (continuous_subtype_val.tendsto (a n)).comp h1
  change _root_.Filter.Tendsto (fun k => (x (φ k) n : ℝ)) _root_.Filter.atTop (𝓝 (a n : ℝ)) at h2
  rw [hx] at h2
  exact h2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.exists_subseq_tendsto_pi then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.exists_subseq_tendsto_pi"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.exists_subseq_tendsto_pi ``Submission.DifferentialGeometry.CheegerGromovCompactness.exists_subseq_tendsto_pi

theorem exists_subseq_eventually_eq {ι : Type*} [Countable ι] (b : ι → ℕ → Bool) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, ∃ v : Bool, ∀ᶠ k in _root_.Filter.atTop, b i (φ k) = v := by
  set x : ℕ → (ι → Bool) := fun k i => b i k with hx
  obtain ⟨a, -, φ, hφ, ha⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (ι → Bool))).tendsto_subseq
      (x := x) (fun k => Set.mem_univ _)
  refine ⟨φ, hφ, fun i => ⟨a i, ?_⟩⟩
  have h1 : _root_.Filter.Tendsto (fun k => x (φ k) i) _root_.Filter.atTop (𝓝 (a i)) := by
    exact (tendsto_pi_nhds.mp ha) i
  rw [nhds_discrete Bool] at h1
  exact tendsto_pure.mp h1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.exists_subseq_eventually_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.exists_subseq_eventually_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.exists_subseq_eventually_eq ``Submission.DifferentialGeometry.CheegerGromovCompactness.exists_subseq_eventually_eq

theorem exists_strictMono_ge (T : ℕ → ℕ) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ j, T j ≤ σ j := by
  classical
  refine ⟨fun j => j + Finset.sup (Finset.range (j + 1)) T, ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    change n + Finset.sup (Finset.range (n + 1)) T
        < (n + 1) + Finset.sup (Finset.range (n + 1 + 1)) T
    have hsub : Finset.range (n + 1) ⊆ Finset.range (n + 1 + 1) :=
      Finset.range_mono (Nat.le_succ (n + 1))
    have hmono : Finset.sup (Finset.range (n + 1)) T
        ≤ Finset.sup (Finset.range (n + 1 + 1)) T :=
      Finset.sup_mono hsub
    calc n + Finset.sup (Finset.range (n + 1)) T
        ≤ n + Finset.sup (Finset.range (n + 1 + 1)) T := Nat.add_le_add_left hmono n
      _ < (n + 1) + Finset.sup (Finset.range (n + 1 + 1)) T := by omega
  · intro j
    change T j ≤ j + Finset.sup (Finset.range (j + 1)) T
    exact le_trans (Finset.le_sup (Finset.self_mem_range_succ j)) (Nat.le_add_left _ j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.exists_strictMono_ge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.exists_strictMono_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.exists_strictMono_ge ``Submission.DifferentialGeometry.CheegerGromovCompactness.exists_strictMono_ge

end CheegerGromovCompactness
end DifferentialGeometry
