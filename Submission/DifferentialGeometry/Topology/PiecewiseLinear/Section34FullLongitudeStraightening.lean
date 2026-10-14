import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedLateralStraightening

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Classical in
theorem exists_prism_straightening_of_full_arc_family
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (D : Geometry.SimplicialComplex ℝ E) [Finite D.faces] (hD : IsPLBall 2 D.space)
    {γ : (boundaryComplex 2 D).space → ℝ → E × ℝ}
    (hdis : Pairwise (fun x y => Disjoint (γ x '' _root_.Set.Icc 0 1) (γ y '' _root_.Set.Icc 0 1)))
    (hcover : (⋃ x, γ x '' _root_.Set.Icc 0 1) = (boundaryComplex 2 D).space ×ˢ _root_.Set.Icc (0 : ℝ) 1)
    (hγ : ∀ x, IsPLHomeomorphOn (γ x) (_root_.Set.Icc 0 1) (γ x '' _root_.Set.Icc 0 1) ∧
      γ x 0 = ((x : E), 0) ∧ γ x 1 = ((x : E), 1) ∧
      γ x '' _root_.Set.Icc 0 1 ⊆ (boundaryComplex 2 D).space ×ˢ _root_.Set.Icc (0 : ℝ) 1 ∧
      (γ x '' _root_.Set.Icc 0 1) ∩ ((boundaryComplex 2 D).space ×ˢ ({0} : Set ℝ)) =
        {((x : E), 0)} ∧
      (γ x '' _root_.Set.Icc 0 1) ∩ ((boundaryComplex 2 D).space ×ˢ ({1} : Set ℝ)) =
        {((x : E), 1)})
    {x y : (boundaryComplex 2 D).space} (hxy : x ≠ y) :
    ∃ Φ : E × ℝ → E × ℝ,
      IsPLHomeomorphOn Φ (D.space ×ˢ _root_.Set.Icc (0 : ℝ) 1) (D.space ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      _root_.Set.EqOn Φ id (D.space ×ˢ ({0, 1} : Set ℝ)) ∧
      ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, Φ ((x : E), t) = γ x t ∧ Φ ((y : E), t) = γ y t := by
  obtain ⟨r, hr⟩ := hD
  have hbd := hr.image_stdSimplexBoundary_eq_boundaryComplex D rfl
  have hstraight := @exists_lateral_straightening_of_spanning_family E _ _ _ D.space r hr
  rw [hbd] at hstraight
  obtain ⟨H, hH, hfix, hmap⟩ := hstraight
    (fun z => ((isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn (hγ z).1).isConnected.isPreconnected)
    (fun z => (hγ z).2.2.2.1) (fun z => (hγ z).2.2.2.2.1)
    (fun z => (hγ z).2.2.2.2.2) hdis hcover hxy (hγ x).1 (hγ y).1
    (hγ x).2.1 (hγ x).2.2.1 (hγ y).2.1 (hγ y).2.2.1
  obtain ⟨Φ, hΦ, hΦH, hΦfix⟩ :=
    exists_prism_extension_fixed_caps_of_lateral_map D ⟨r, hr⟩ hH hfix
  exact ⟨Φ, hΦ, hΦfix, fun t ht =>
    ⟨(hΦH ⟨x.2, ht⟩).trans (hmap t ht).1,
      (hΦH ⟨y.2, ht⟩).trans (hmap t ht).2⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_prism_straightening_of_full_arc_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_prism_straightening_of_full_arc_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_prism_straightening_of_full_arc_family ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_prism_straightening_of_full_arc_family

end DifferentialGeometry.Topology.PiecewiseLinear
