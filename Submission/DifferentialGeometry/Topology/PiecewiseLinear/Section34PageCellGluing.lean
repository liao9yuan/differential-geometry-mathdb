import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedCellCapTrace
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34UntwistedCircleCellGluing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_untwisted_diagram_of_cyclic_page_cells
    {G : ℕ → (ℝ × ℝ) × ℝ → E} {B : ℕ → Set E} {P : Fin 4 → Set E} {J : Set E}
    {m : ℕ} (hm : 2 ≤ m)
    (hG : ∀ k ≤ m, IsPLHomeomorphOn (G k) (spliceSquare ×ˢ _root_.Set.Icc (0 : ℝ) 1) (B k))
    (hcap : ∀ k < m, G k '' (spliceSquare ×ˢ ({1} : Set ℝ)) =
      G (k + 1) '' (spliceSquare ×ˢ ({0} : Set ℝ)))
    (hadj : ∀ k < m, B k ∩ B (k + 1) = G k '' (spliceSquare ×ˢ ({1} : Set ℝ)))
    (hadjc : B m ∩ B 0 = G 0 '' (spliceSquare ×ˢ ({0} : Set ℝ)))
    (hfar : ∀ j k, j + 1 < k → k ≤ m → (j ≠ 0 ∨ k ≠ m) → Disjoint (B j) (B k))
    (hclose : G m '' (spliceSquare ×ˢ ({1} : Set ℝ)) =
      G 0 '' (spliceSquare ×ˢ ({0} : Set ℝ)))
    (hpages : ∀ k ≤ m, ∀ i,
      G k '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ _root_.Set.Icc (0 : ℝ) 1) = B k ∩ P i)
    (hcore : ∀ k ≤ m, G k '' (({0} : Set (ℝ × ℝ)) ×ˢ _root_.Set.Icc (0 : ℝ) 1) = B k ∩ J) :
    ∃ f : (ℝ × ℝ) × ℝ → E,
      IsCylindricalDiagram f spliceSquare (⋃ k ≤ m, B k) ∧
      (∀ x ∈ spliceSquare, f (x, 0) = f (x, 1)) ∧
      (∀ x ∈ spliceSquare, f (x, 0) = G 0 (x, 0)) ∧
      (∀ i, f '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
        (⋃ k ≤ m, B k) ∩ P i) ∧
      f '' (({0} : Set (ℝ × ℝ)) ×ˢ _root_.Set.Icc (0 : ℝ) 1) = (⋃ k ≤ m, B k) ∩ J := by
  have hadjdata (k : ℕ) (hk : k < m) :=
    splice_cap_arms_match_of_page_traces (hG k hk.le) (hG (k + 1) hk) (hcap k hk)
      (hpages k hk.le) (hpages (k + 1) hk)
  have hclosedata := splice_cap_arms_match_of_page_traces (hG m le_rfl)
    (hG 0 (Nat.zero_le m)) hclose (hpages m le_rfl) (hpages 0 (Nat.zero_le m))
  obtain ⟨f, hf, hends, hzero, hstrips, haxis⟩ :=
    exists_untwisted_diagram_of_ordered_cyclic_cells hm hG hcap
      (fun k hk => (hadjdata k hk).1) (fun k hk => (hadjdata k hk).2)
      hadj hadjc hfar hclose hclosedata.1 hclosedata.2
  refine ⟨f, hf, hends, hzero, ?_, ?_⟩
  · intro i
    rw [hstrips i]
    simp_rw [_root_.Set.iUnion_inter]
    apply _root_.Set.iUnion_congr
    intro k
    apply _root_.Set.iUnion_congr
    intro hk
    exact hpages k hk i
  · rw [haxis]
    simp_rw [_root_.Set.iUnion_inter]
    apply _root_.Set.iUnion_congr
    intro k
    apply _root_.Set.iUnion_congr
    intro hk
    exact hcore k hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_untwisted_diagram_of_cyclic_page_cells then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_untwisted_diagram_of_cyclic_page_cells"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_untwisted_diagram_of_cyclic_page_cells ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_untwisted_diagram_of_cyclic_page_cells

end DifferentialGeometry.Topology.PiecewiseLinear
