import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34ExpandedSquareCrossingCharts
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.EssentialPolygonProductCoordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_swapped_axis_charts_of_expanded_square_paths
    {A B : Set (ℝ × ℝ)} {γ : Fin 2 → ℝ → ℝ × ℝ} {c d : ℝ}
    (hc : 0 < c) (hcd : c ≤ 2 * d)
    (hγ : ∀ k, IsPLHomeomorphOn (γ k) (_root_.Set.Icc (-d) d) (γ k '' _root_.Set.Icc (-d) d))
    (hγbd : ∀ k, γ k '' _root_.Set.Icc (-d) d ⊆ frontier (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hdis : Disjoint (γ 0 '' _root_.Set.Icc (-d) d) (γ 1 '' _root_.Set.Icc (-d) d))
    (hA : A ⊆ frontier (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hAB : A ∩ B = {γ 0 0, γ 1 0})
    (hpos : ∀ k, γ k '' _root_.Set.Icc 0 d ⊆ A) (hneg : ∀ k, γ k '' _root_.Set.Icc (-d) 0 ⊆ B) :
    let ηX := fun (k : Fin 2) (r : ℝ) => section34SquareShellFlatten c (γ k (-r / 2), r)
    let ηY := fun (k : Fin 2) (r : ℝ) => section34SquareShellFlatten c (γ k (r / 2), r)
    let X := A ∪ (ηX 0 '' _root_.Set.Icc 0 c ∪ ηX 1 '' _root_.Set.Icc 0 c)
    let Y := B ∪ (ηY 0 '' _root_.Set.Icc 0 c ∪ ηY 1 '' _root_.Set.Icc 0 c)
    ∀ k, ∃ (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) (ε : ℝ),
      0 < ε ∧ IsPLHomeomorphOn e e.source e.target ∧ e (0, 0) = γ k 0 ∧
      _root_.Set.Ioo (-ε) ε ×ˢ _root_.Set.Ioo (-ε) ε ⊆ e.source ∧
      (∀ p ∈ _root_.Set.Ioo (-ε) ε ×ˢ _root_.Set.Ioo (-ε) ε, e p ∈ X ↔ p.2 = 0) ∧
      ∀ s ∈ _root_.Set.Ioo (-ε) ε, e (0, s) ∈ Y := by
  let γ' := fun (k : Fin 2) (t : ℝ) => γ k (-t)
  have hn : IsPLHomeomorphOn (fun t : ℝ => -t) (_root_.Set.Icc (-d) d) (_root_.Set.Icc (-d) d) := by
    simpa only [neg_one_mul, add_zero] using
      isPLHomeomorphOn_mul_add_Icc_of_neg (m := (-1 : ℝ)) (c := 0)
        (a := -d) (b := d) (a' := -d) (b' := d)
        (by norm_num) (by ring) (by ring)
  have himage (k) : γ' k '' _root_.Set.Icc (-d) d = γ k '' _root_.Set.Icc (-d) d := by
    change (γ k ∘ fun t => -t) '' _root_.Set.Icc (-d) d = _
    rw [_root_.Set.image_comp, hn.image_eq]
  have hγ' (k) : IsPLHomeomorphOn (γ' k) (_root_.Set.Icc (-d) d) (γ' k '' _root_.Set.Icc (-d) d) := by
    rw [himage]
    exact hn.trans (hγ k)
  have hpos' (k) : γ' k '' _root_.Set.Icc 0 d ⊆ B := by
    rintro _ ⟨t, ht, rfl⟩
    exact hneg k ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
  have hneg' (k) : γ' k '' _root_.Set.Icc (-d) 0 ⊆ A := by
    rintro _ ⟨t, ht, rfl⟩
    exact hpos k ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
  have h := exists_axis_charts_of_expanded_square_paths hc hcd hγ'
    (fun k => (himage k).symm ▸ hγbd k)
    (by simpa only [himage] using hdis) hA
    (by simpa only [γ', neg_zero, _root_.Set.inter_comm] using hAB) hpos' hneg'
  simpa only [γ', neg_zero, neg_div, neg_neg] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_swapped_axis_charts_of_expanded_square_paths then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_swapped_axis_charts_of_expanded_square_paths"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_swapped_axis_charts_of_expanded_square_paths ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_swapped_axis_charts_of_expanded_square_paths

end DifferentialGeometry.Topology.PiecewiseLinear
