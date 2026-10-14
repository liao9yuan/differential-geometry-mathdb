import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CircleArcs
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Pasting

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open _root_.Classical in
theorem exists_piecewiseAffineOn_circle_of_paths
    {S : Set E} (hS : IsPLSphere 1 S) {p q : E} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q)
    {f g : ℝ → F} (hf : IsPiecewiseAffineOn f (_root_.Set.Icc 0 1))
    (hg : IsPiecewiseAffineOn g (_root_.Set.Icc 0 1)) (h0 : f 0 = g 0) (h1 : f 1 = g 1) :
    ∃ (A B : Set E) (γ δ : ℝ → E) (H : E → F),
      IsPLHomeomorphOn γ (_root_.Set.Icc 0 1) A ∧ IsPLHomeomorphOn δ (_root_.Set.Icc 0 1) B ∧
        γ 0 = p ∧ γ 1 = q ∧ δ 0 = p ∧ δ 1 = q ∧ A ∪ B = S ∧ A ∩ B = {p, q} ∧
          IsPiecewiseAffineOn H S ∧ (∀ t ∈ _root_.Set.Icc 0 1, H (γ t) = f t) ∧
            ∀ t ∈ _root_.Set.Icc 0 1, H (δ t) = g t := by
  obtain ⟨A, B, γ, δ, hγ, hδ, hγ0, hγ1, hδ0, hδ1, hunion, hinter⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hS hp hq hpq
  let a := Function.invFunOn γ (_root_.Set.Icc 0 1)
  let b := Function.invFunOn δ (_root_.Set.Icc 0 1)
  have ha : IsPiecewiseAffineOn (f ∘ a) A := by
    have h := hf.comp hγ.isPiecewiseAffineOn_invFunOn
    rwa [show A ∩ Function.invFunOn γ (_root_.Set.Icc 0 1) ⁻¹' _root_.Set.Icc 0 1 = A from
      inter_eq_left.mpr hγ.symm.bijOn.mapsTo] at h
  have hb : IsPiecewiseAffineOn (g ∘ b) B := by
    have h := hg.comp hδ.isPiecewiseAffineOn_invFunOn
    rwa [show B ∩ Function.invFunOn δ (_root_.Set.Icc 0 1) ⁻¹' _root_.Set.Icc 0 1 = B from
      inter_eq_left.mpr hδ.symm.bijOn.mapsTo] at h
  have ha0 : a p = 0 := hγ0 ▸ hγ.bijOn.invOn_invFunOn.1 (by norm_num)
  have ha1 : a q = 1 := hγ1 ▸ hγ.bijOn.invOn_invFunOn.1 (by norm_num)
  have hb0 : b p = 0 := hδ0 ▸ hδ.bijOn.invOn_invFunOn.1 (by norm_num)
  have hb1 : b q = 1 := hδ1 ▸ hδ.bijOn.invOn_invFunOn.1 (by norm_num)
  have hcommon : _root_.Set.EqOn (f ∘ a) (g ∘ b) (A ∩ B) := by
    rw [hinter]
    rintro x (rfl | rfl)
    · simpa only [Function.comp_apply, ha0, hb0] using h0
    · simpa only [Function.comp_apply, ha1, hb1] using h1
  let H := A.piecewise (f ∘ a) (g ∘ b)
  have hI : IsPLBall 1 (_root_.Set.Icc (0 : ℝ) 1) := isPLBall_Icc (by norm_num)
  have hH : IsPiecewiseAffineOn H S := by
    rw [← hunion]
    exact ha.piecewise_of_isClosed hb (hI.of_isPLHomeomorphOn hγ).isPolyhedron.isClosed
      (hI.of_isPLHomeomorphOn hδ).isPolyhedron.isClosed hcommon
  refine ⟨A, B, γ, δ, H, hγ, hδ, hγ0, hγ1, hδ0, hδ1, hunion, hinter, hH, ?_, ?_⟩
  · intro t ht
    rw [show H (γ t) = f (a (γ t)) from _root_.Set.piecewise_eq_of_mem A _ _ (hγ.bijOn.mapsTo ht)]
    exact congrArg f (hγ.bijOn.invOn_invFunOn.1 ht)
  · intro t ht
    have hright : H (δ t) = g (b (δ t)) := by
      by_cases hx : δ t ∈ A
      · rw [show H (δ t) = f (a (δ t)) from _root_.Set.piecewise_eq_of_mem A _ _ hx]
        exact hcommon ⟨hx, hδ.bijOn.mapsTo ht⟩
      · exact _root_.Set.piecewise_eq_of_notMem A _ _ hx
    rw [hright]
    exact congrArg g (hδ.bijOn.invOn_invFunOn.1 ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffineOn_circle_of_paths then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffineOn_circle_of_paths"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffineOn_circle_of_paths ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewiseAffineOn_circle_of_paths

end DifferentialGeometry.Topology.PiecewiseLinear
