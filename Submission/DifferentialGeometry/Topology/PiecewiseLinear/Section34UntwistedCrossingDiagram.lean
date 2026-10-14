import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedCylinderUntwisting
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34FourSpokePseudoIsotopySquare

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsCylindricalDiagram.exists_untwisted_four_spoke_diagram
    {g : (ℝ × ℝ) × ℝ → E} {S : Set E} (hg : IsCylindricalDiagram g spliceSquare S)
    {u : ℝ × ℝ → ℝ × ℝ} (hu : IsPLHomeomorphOn u spliceSquare spliceSquare)
    (hends : ∀ x ∈ spliceSquare, g (x, 0) = g (u x, 1))
    (hspokes : ∀ i, u '' segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) =
      segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i))
    (hleaves : ∀ i, u (fourSpokeModelLeaf i) = fourSpokeModelLeaf i) :
    ∃ f : (ℝ × ℝ) × ℝ → E, IsCylindricalDiagram f spliceSquare S ∧
      (∀ x ∈ spliceSquare, f (x, 0) = f (x, 1)) ∧
      (∀ x ∈ spliceSquare, f (x, 0) = g (x, 0)) ∧
      (∀ i, f '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
        g '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ _root_.Set.Icc (0 : ℝ) 1)) ∧
      (∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, f (0, t) = g (0, t)) ∧
      ∀ i, ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, f (fourSpokeModelLeaf i, t) = g (fourSpokeModelLeaf i, t) := by
  obtain ⟨Φ, hΦ, hΦ0, hΦ1, hΦT, hΦc, hΦv⟩ :=
    exists_PL_splice_square_pseudoisotopy_of_preserves_spokes hu hspokes hleaves
  obtain ⟨hnew, hnewends, hnew0, hnewimages⟩ :=
    hg.untwist_with_marked_pseudoisotopy hu hends hΦ hΦ0 hΦ1
  exact ⟨g ∘ Φ, hnew, hnewends, hnew0,
    fun i => hnewimages _ (hΦT i), fun t ht => congrArg g (hΦc t ht),
    fun i t ht => congrArg g (hΦv i t ht)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_untwisted_four_spoke_diagram then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_untwisted_four_spoke_diagram"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_untwisted_four_spoke_diagram ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_untwisted_four_spoke_diagram

end DifferentialGeometry.Topology.PiecewiseLinear
