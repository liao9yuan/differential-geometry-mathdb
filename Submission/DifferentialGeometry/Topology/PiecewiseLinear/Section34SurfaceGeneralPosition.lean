import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCombinatorialManifold.exists_relative_general_position_circles
    (K L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifold 2 K) (hL : IsCombinatorialManifold 2 L)
    {Ω : Set (EuclideanSpace ℝ (Fin 3))} (hΩ : IsOpen Ω) (hKΩ : K.space ⊆ Ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (H : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3))
      (N : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (n : ℕ) (J : Fin n → Set (EuclideanSpace ℝ (Fin 3))),
      IsPLHomeomorphOn H _root_.Set.univ _root_.Set.univ ∧ _root_.Set.EqOn H id Ωᶜ ∧
      (∀ x, _root_.Dist.dist (H x) x < ε) ∧ N.faces.Finite ∧ IsCombinatorialManifold 2 N ∧
      N.space = H '' K.space ∧ N.space ⊆ Ω ∧
      (∀ x ∈ N.space ∩ L.space, HasPLCrossingAt N.space L.space x) ∧
      (∀ i, IsPLSphere 1 (J i)) ∧ (Pairwise fun i j => Disjoint (J i) (J j)) ∧
      N.space ∩ L.space = ⋃ i, J i := by
  classical
  obtain ⟨a, h, -, hh, hclose, hfix, hspace, htrans⟩ :=
    exists_small_homeomorph_transverse_affineImage K L hΩ hKΩ hε
  let H : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3) :=
    { toFun := h
      invFun := Function.invFunOn h _root_.Set.univ
      left_inv := fun x => hh.bijOn.invOn_invFunOn.1 (_root_.Set.mem_univ x)
      right_inv := fun x => hh.bijOn.invOn_invFunOn.2 (_root_.Set.mem_univ x)
      continuous_toFun := continuousOn_univ.mp hh.isPiecewiseAffineOn.continuousOn
      continuous_invFun := continuousOn_univ.mp hh.isPiecewiseAffineOn_invFunOn.continuousOn }
  let N := affineImage K (AffineEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin 3)) a)
  have hNfin : N.faces.Finite := affineImage_faces_finite K _
  let _ : Finite N.faces := hNfin.to_subtype
  have hN : IsCombinatorialManifold 2 N :=
    hK.of_isPLHomeomorphOn (isPLHomeomorphOn_affineImage K _)
  have hNΩ : N.space ⊆ Ω := by
    rw [hspace]
    rintro _ ⟨x, hx, rfl⟩
    by_contra hn
    have heq : h x = x := hh.bijOn.injOn (_root_.Set.mem_univ (h x)) (_root_.Set.mem_univ x) (hfix hn)
    exact hn (heq.symm ▸ hKΩ hx)
  obtain ⟨hcross, ι, hι, C, hC, hdis, hcover⟩ :=
    exists_isPLSphere_cover_inter_of_transverse_faces (by simp) N L hN hL htrans
  let _ : Finite ι := hι
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  refine ⟨H, N, n, fun i => C (e.symm i), hh, hfix, hclose, hNfin, hN,
    hspace, hNΩ, hcross, fun i => hC (e.symm i), ?_, ?_⟩
  · intro i j hij
    exact hdis (fun heq => hij (e.symm.injective heq))
  · rw [hcover]
    exact e.symm.surjective.iUnion_comp C |>.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_relative_general_position_circles then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_relative_general_position_circles"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_relative_general_position_circles ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_relative_general_position_circles

end DifferentialGeometry.Topology.PiecewiseLinear
