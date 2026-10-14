import Submission.DifferentialGeometry.Analysis.Matrix.PositiveRankOne

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Filter
open scoped _root_.BigOperators _root_.ContDiff _root_.Topology _root_.Matrix.Norms.Elementwise

namespace DifferentialGeometry.Analysis

theorem exists_contDiffOn_positive_rank_one_decomposition
    {P ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype ι]
    {A : P → Matrix ι ι ℝ} {x : P} {n : ℕ}
    (hA : ContDiffAt ℝ n A x)
    (hsymm : ∀ᶠ y in 𝓝 x, (A y).IsSymm) (hpos : (A x).PosDef) :
    ∃ (N : ℕ) (v : Fin N → ι → ℝ) (a : Fin N → P → ℝ) (U : Set P),
      IsOpen U ∧ x ∈ U ∧
      (∀ k, ContDiffOn ℝ n (a k) U) ∧
      (∀ y ∈ U, ∀ k, 0 < a k y) ∧
      ∀ y ∈ U, ∀ i j, A y i j = ∑ k, a k y * v k i * v k j := by
  obtain ⟨N, v, b, hb, hpositive, hrep⟩ :=
    exists_contDiff_positive_rank_one_decomposition hpos
  obtain ⟨W, hW, hAW⟩ := hA.contDiffOn le_rfl (by simp)
  have hnear : ∀ᶠ y in 𝓝 x, ∀ k, 0 < b k (A y) :=
    hA.continuousAt.tendsto.eventually hpositive
  have hgood : ∀ᶠ y in 𝓝 x, y ∈ W ∧ (∀ k, 0 < b k (A y)) ∧ (A y).IsSymm := by
    filter_upwards [hW, hnear, hsymm] with y hy hp hs
    exact ⟨hy, hp, hs⟩
  obtain ⟨U, hU, hopen, hx⟩ := mem_nhds_iff.mp hgood
  refine ⟨N, v, fun k y ↦ b k (A y), U, hopen, hx, ?_, ?_, ?_⟩
  · intro k
    exact (contDiff_infty.mp (hb k) n).comp_contDiffOn
      (hAW.mono fun y hy ↦ (hU hy).1)
  · intro y hy k
    exact (hU hy).2.1 k
  · intro y hy i j
    exact hrep (A y) (hU hy).2.2 i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_contDiffOn_positive_rank_one_decomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_contDiffOn_positive_rank_one_decomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_contDiffOn_positive_rank_one_decomposition ``Submission.DifferentialGeometry.Analysis.exists_contDiffOn_positive_rank_one_decomposition

end DifferentialGeometry.Analysis
