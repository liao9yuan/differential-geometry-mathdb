import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CylindricalDiagram

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.precomp_fixed_caps
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {P : Set E} {S : Set F}
    {g : E × ℝ → F} (hg : IsCylindricalDiagram g P S) {H : E × ℝ → E × ℝ}
    (hH : IsPLHomeomorphOn H (P ×ˢ _root_.Set.Icc (0 : ℝ) 1) (P ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hfix : _root_.Set.EqOn H id (P ×ˢ ({0, 1} : Set ℝ))) :
    IsCylindricalDiagram (g ∘ H) P S := by
  have himage (a : ℝ) (ha : a ∈ ({0, 1} : Set ℝ)) :
      H '' (P ×ˢ {a}) = P ×ˢ {a} := by
    have heq : _root_.Set.EqOn H id (P ×ˢ {a}) := fun x hx => hfix ⟨hx.1, hx.2.symm ▸ ha⟩
    exact heq.image_eq.trans (_root_.Set.image_id _)
  have hlevel (a : ℝ) (ha : a ∈ ({0, 1} : Set ℝ)) {x : E × ℝ}
      (hx : x ∈ P ×ˢ _root_.Set.Icc (0 : ℝ) 1) (hxa : (H x).2 = a) : x.2 = a := by
    have hmem := hH.bijOn.mapsTo hx
    have hfx : H (H x) = H x := hfix ⟨hmem.1, hxa.symm ▸ ha⟩
    exact (congrArg Prod.snd (hH.bijOn.injOn hx hmem hfx.symm)).trans hxa
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hg.isPiecewiseAffineOn.comp hH.isPiecewiseAffineOn
    rwa [inter_eq_left.mpr (show P ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ H ⁻¹' (P ×ˢ _root_.Set.Icc 0 1) from
      hH.bijOn.mapsTo)] at h
  · rw [_root_.Set.image_comp, hH.image_eq, hg.image_eq]
  · rw [_root_.Set.image_comp, _root_.Set.image_comp, himage 0 (by simp), himage 1 (by simp)]
    exact hg.image_top_eq_bottom
  · intro x hx y hy hxy
    rcases hg.eq_or_endpoints (H x) (hH.bijOn.mapsTo hx) (H y) (hH.bijOn.mapsTo hy) hxy
      with heq | hends | hends
    · exact Or.inl (hH.bijOn.injOn hx hy heq)
    · exact Or.inr (Or.inl
        ⟨hlevel 0 (by simp) hx hends.1, hlevel 1 (by simp) hy hends.2⟩)
    · exact Or.inr (Or.inr
        ⟨hlevel 1 (by simp) hx hends.1, hlevel 0 (by simp) hy hends.2⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.precomp_fixed_caps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.precomp_fixed_caps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.precomp_fixed_caps ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.precomp_fixed_caps

theorem IsCylindricalDiagram.precomp_fixed_caps_with_ends
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {P : Set E} {S : Set F}
    {g : E × ℝ → F} (hg : IsCylindricalDiagram g P S)
    (hends : ∀ x ∈ P, g (x, 0) = g (x, 1)) {H : E × ℝ → E × ℝ}
    (hH : IsPLHomeomorphOn H (P ×ˢ _root_.Set.Icc (0 : ℝ) 1) (P ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hfix : _root_.Set.EqOn H id (P ×ˢ ({0, 1} : Set ℝ))) :
    IsCylindricalDiagram (g ∘ H) P S ∧
      (∀ x ∈ P, (g ∘ H) (x, 0) = (g ∘ H) (x, 1)) ∧
      (g ∘ H) '' (P ×ˢ ({0} : Set ℝ)) = g '' (P ×ˢ ({0} : Set ℝ)) := by
  have heq : _root_.Set.EqOn (g ∘ H) g (P ×ˢ ({0, 1} : Set ℝ)) :=
    fun x hx => congrArg g (hfix hx)
  refine ⟨hg.precomp_fixed_caps hH hfix, ?_, ?_⟩
  · intro x hx
    have h0 : (x, (0 : ℝ)) ∈ P ×ˢ ({0, 1} : Set ℝ) := ⟨hx, Or.inl rfl⟩
    have h1 : (x, (1 : ℝ)) ∈ P ×ˢ ({0, 1} : Set ℝ) := ⟨hx, Or.inr rfl⟩
    exact (heq h0).trans ((hends x hx).trans (heq h1).symm)
  · have hsub : P ×ˢ ({0} : Set ℝ) ⊆ P ×ˢ ({0, 1} : Set ℝ) :=
      fun x hx => ⟨hx.1, Or.inl hx.2⟩
    exact (heq.mono hsub).image_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.precomp_fixed_caps_with_ends then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.precomp_fixed_caps_with_ends"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.precomp_fixed_caps_with_ends ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.precomp_fixed_caps_with_ends

end DifferentialGeometry.Topology.PiecewiseLinear
