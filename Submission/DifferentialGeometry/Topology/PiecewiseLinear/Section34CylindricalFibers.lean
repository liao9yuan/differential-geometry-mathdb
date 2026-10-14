import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalCancellation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.FourArcSphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsCylindricalDiagram.isPLSphere_fiber {f : E × ℝ → F} {P : Set E} {S : Set F}
    (hf : IsCylindricalDiagram f P S)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) {x : E} (hx : x ∈ P) :
    IsPLSphere 1 (f '' ({x} ×ˢ _root_.Set.Icc (0 : ℝ) 1)) := by
  let a : ℝ →ᵃ[ℝ] E × ℝ := (AffineMap.const ℝ ℝ x).prod ((1 / 2 : ℝ) • AffineMap.id ℝ ℝ)
  let b : ℝ →ᵃ[ℝ] E × ℝ := (AffineMap.const ℝ ℝ x).prod
    (AffineMap.const ℝ ℝ (1 : ℝ) - (1 / 2 : ℝ) • AffineMap.id ℝ ℝ)
  let α := f ∘ a
  let β := f ∘ b
  have ha (t : ℝ) : a t = (x, t / 2) := by simp [a, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hb (t : ℝ) : b t = (x, 1 - t / 2) := by
    simp [b, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hmapa : _root_.Set.MapsTo a (_root_.Set.Icc (0 : ℝ) 1) (P ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
    intro t ht
    rw [ha]
    exact ⟨hx, by linarith [ht.1], by linarith [ht.2]⟩
  have hmapb : _root_.Set.MapsTo b (_root_.Set.Icc (0 : ℝ) 1) (P ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
    intro t ht
    rw [hb]
    exact ⟨hx, by linarith [ht.2], by linarith [ht.1]⟩
  have hαpl : IsPiecewiseAffineOn α (_root_.Set.Icc 0 1) := by
    have h := hf.isPiecewiseAffineOn.comp
      (isPiecewiseAffineOn_of_affine_of_isHPolytope a (isHPolytope_Icc (a := (0 : ℝ)) (b := 1)))
    have heq : _root_.Set.Icc (0 : ℝ) 1 ∩ a ⁻¹' (P ×ˢ _root_.Set.Icc (0 : ℝ) 1) = _root_.Set.Icc (0 : ℝ) 1 :=
      inter_eq_left.mpr hmapa
    rwa [heq] at h
  have hβpl : IsPiecewiseAffineOn β (_root_.Set.Icc 0 1) := by
    have h := hf.isPiecewiseAffineOn.comp
      (isPiecewiseAffineOn_of_affine_of_isHPolytope b (isHPolytope_Icc (a := (0 : ℝ)) (b := 1)))
    have heq : _root_.Set.Icc (0 : ℝ) 1 ∩ b ⁻¹' (P ×ˢ _root_.Set.Icc (0 : ℝ) 1) = _root_.Set.Icc (0 : ℝ) 1 :=
      inter_eq_left.mpr hmapb
    rwa [heq] at h
  have hαinj : _root_.Set.InjOn α (_root_.Set.Icc 0 1) := by
    intro s hs t ht hst
    have h := hf.injOn_strip (a := 0) (b := 1 / 2) le_rfl (by norm_num)
      (Or.inr (by norm_num))
      (x₁ := a s) (x₂ := a t)
      (by rw [ha]; exact ⟨hx, by linarith [hs.1], by linarith [hs.2]⟩)
      (by rw [ha]; exact ⟨hx, by linarith [ht.1], by linarith [ht.2]⟩) hst
    have ht' := congrArg Prod.snd h
    rw [ha, ha] at ht'
    dsimp at ht'
    linarith
  have hβinj : _root_.Set.InjOn β (_root_.Set.Icc 0 1) := by
    intro s hs t ht hst
    have h := hf.injOn_strip (a := 1 / 2) (b := 1) (by norm_num) le_rfl
      (Or.inl (by norm_num))
      (x₁ := b s) (x₂ := b t)
      (by rw [hb]; exact ⟨hx, by linarith [hs.2], by linarith [hs.1]⟩)
      (by rw [hb]; exact ⟨hx, by linarith [ht.2], by linarith [ht.1]⟩) hst
    have ht' := congrArg Prod.snd h
    rw [hb, hb] at ht'
    dsimp at ht'
    linarith
  have hα := isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    hαpl hαinj.bijOn_image
  have hβ := isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    hβpl hβinj.bijOn_image
  have hzero : β 0 = α 0 := by
    change f (b 0) = f (a 0)
    rw [ha, hb]
    simpa using (hends x hx).symm
  have hone : β 1 = α 1 := by
    change f (b 1) = f (a 1)
    rw [ha, hb]
    norm_num
  have hmeet : (α '' _root_.Set.Icc 0 1) ∩ (β '' _root_.Set.Icc 0 1) = {α 0, α 1} := by
    apply Subset.antisymm
    · rintro _ ⟨⟨t, ht, rfl⟩, s, hs, hst⟩
      rcases hf.eq_or_endpoints _ (hmapa ht) _ (hmapb hs) hst.symm with h | h | h
      · have heq := congrArg Prod.snd h
        rw [ha, hb] at heq
        have ht1 : t = 1 := by dsimp at heq; linarith [ht.2, hs.2]
        exact Or.inr (congrArg α ht1)
      · have ht0 : t = 0 := by rw [ha] at h; dsimp at h; linarith [h.1]
        exact Or.inl (congrArg α ht0)
      · rw [ha] at h
        dsimp at h
        linarith [ht.2, h.1]
    · rintro z (rfl | rfl)
      · exact ⟨⟨0, by norm_num, rfl⟩, 0, by norm_num, hzero⟩
      · exact ⟨⟨1, by norm_num, rfl⟩, 1, by norm_num, hone⟩
  have hcover : (α '' _root_.Set.Icc 0 1) ∪ (β '' _root_.Set.Icc 0 1) = f '' ({x} ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
    apply Subset.antisymm
    · rintro z (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · exact ⟨a t, by rw [ha]; exact ⟨rfl, by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
      · exact ⟨b t, by rw [hb]; exact ⟨rfl, by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
    · rintro _ ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩
      have hyx : y = x := hy
      subst y
      by_cases hhalf : t ≤ 1 / 2
      · left
        refine ⟨2 * t, ⟨by linarith [ht.1], by linarith⟩, ?_⟩
        change f (a (2 * t)) = f (x, t)
        rw [ha]
        congr 2
        ring
      · right
        refine ⟨2 - 2 * t, ⟨by linarith [ht.2], by linarith⟩, ?_⟩
        change f (b (2 - 2 * t)) = f (x, t)
        rw [hb]
        congr 2
        ring
  exact hcover ▸ isPLSphere_one_union_of_isPLHomeomorphOn_Icc hα hβ hzero hone hmeet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isPLSphere_fiber then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isPLSphere_fiber"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isPLSphere_fiber ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isPLSphere_fiber

end DifferentialGeometry.Topology.PiecewiseLinear
