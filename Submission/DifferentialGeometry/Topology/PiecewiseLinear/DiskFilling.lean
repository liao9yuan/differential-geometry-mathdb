/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homotopy.ConvexPlaneExtension
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.OpenTargetApproximation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Prism
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_continuous_convex_disk_extension
    {Q : Type*} [TopologicalSpace Q] [SimplyConnectedSpace Q]
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsCompact P) (hc : Convex ℝ P)
    (hi : (interior P).Nonempty) (f : C(frontier P, Q)) :
    ∃ F : C(P, Q), ∀ z : frontier P, F ⟨z.val, hP.isClosed.frontier_subset z.property⟩ = f z := by
  let e : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℂ :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).trans
      Complex.equivRealProdCLM.symm
  have hfront : e '' frontier P = frontier (e '' P) := e.toHomeomorph.image_frontier P
  have hbd : ∀ z ∈ frontier (e '' P), e.symm z ∈ frontier P := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hfront.symm.subset hz
    simpa only [e.symm_apply_apply] using hw
  let f' : C(frontier (e '' P), Q) :=
    ⟨fun z => f ⟨e.symm z, hbd z z.property⟩,
      f.continuous.comp ((e.symm.continuous.comp continuous_subtype_val).subtype_mk _)⟩
  obtain ⟨F, hF⟩ := exists_convex_plane_boundary_extension
    (hc.linear_image e.toLinearMap) (hP.image e.continuous).isClosed
    (hP.image e.continuous).isBounded
    (e.toHomeomorph.image_interior P ▸ hi.image e) f'
  let G : C(P, Q) := ⟨fun z => F ⟨e z, _root_.Set.mem_image_of_mem e z.property⟩,
    F.continuous.comp ((e.continuous.comp continuous_subtype_val).subtype_mk _)⟩
  refine ⟨G, fun z => ?_⟩
  have hz : e z ∈ frontier (e '' P) := hfront.subset (_root_.Set.mem_image_of_mem e z.property)
  exact (hF ⟨e z, hz⟩).trans (congrArg f (Subtype.ext (e.symm_apply_apply z)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_continuous_convex_disk_extension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.exists_continuous_convex_disk_extension target :: scope.openDecls } }

private theorem exists_piecewise_affine_convex_disk_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsPLBall 2 P) (hc : Convex ℝ P)
    {U : Set E} (hU : IsOpen U) [SimplyConnectedSpace U]
    {f : EuclideanSpace ℝ (Fin 2) → E} (hf : IsPiecewiseAffineOn f (frontier P))
    (hmap : _root_.Set.MapsTo f (frontier P) U) :
    ∃ g : EuclideanSpace ℝ (Fin 2) → E,
      IsPiecewiseAffineOn g P ∧ _root_.Set.EqOn g f (frontier P) ∧ _root_.Set.MapsTo g P U := by
  classical
  have hbd : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  let b : C(frontier P, U) :=
    ⟨fun z => ⟨f z, hmap z.property⟩, hf.continuousOn.domRestrict.subtype_mk _⟩
  obtain ⟨F, hF⟩ := exists_continuous_convex_disk_extension
    hP.isPolyhedron.isCompact hc hP.interior_nonempty b
  let v : EuclideanSpace ℝ (Fin 2) → E :=
    fun z => if hz : z ∈ P then (F ⟨z, hz⟩ : E) else 0
  have hv (z : P) : v z = (F z : E) := by simp only [v, dif_pos z.property]
  have hvcont : ContinuousOn v P := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp F.continuous).congr (fun z => (hv z).symm)
  have hvbd : _root_.Set.EqOn v f (frontier P) := fun z hz =>
    (hv ⟨z, hbd hz⟩).trans (congrArg (fun w : U => (w : E)) (hF ⟨z, hz⟩))
  obtain ⟨g, hg, hgv, hgmap⟩ := exists_isPiecewiseAffineOn_mapsTo_eqOn
    hP.isPolyhedron hP.isPLSphere_frontier.isPolyhedron hbd hU hvcont (hf.congr hvbd)
    (fun z hz => by rw [hv ⟨z, hz⟩]; exact (F ⟨z, hz⟩).property)
  exact ⟨g, hg, hgv.trans hvbd, hgmap⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewise_affine_convex_disk_extension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.exists_piecewise_affine_convex_disk_extension target :: scope.openDecls } }

theorem IsPLBall.exists_isPiecewiseAffineOn_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : IsPLBall 2 P)
    {U : Set E} (hU : IsOpen U) [SimplyConnectedSpace U]
    {f : EuclideanSpace ℝ (Fin 2) → E} (hf : IsPiecewiseAffineOn f (frontier P))
    (hmap : _root_.Set.MapsTo f (frontier P) U) :
    ∃ g : EuclideanSpace ℝ (Fin 2) → E,
      IsPiecewiseAffineOn g P ∧ _root_.Set.EqOn g f (frontier P) ∧ _root_.Set.MapsTo g P U := by
  let e : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 2) ℝ).symm
  let C := _root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1
  have he : IsPLHomeomorphOn e C (e '' C) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isPLBall_unit_square.isPolyhedron
      ((isPiecewiseAffineOn_of_affine e.toLinearMap.toAffineMap isOpen_univ).mono_of_isPolyhedron
        isPLBall_unit_square.isPolyhedron (_root_.Set.subset_univ _)) e.injective.injOn.bijOn_image
  have hQ : IsPLBall 2 (e '' C) := isPLBall_unit_square.of_isPLHomeomorphOn he
  have hQc : Convex ℝ (e '' C) :=
    ((convex_Icc (0 : ℝ) 1).prod (convex_Icc (0 : ℝ) 1)).linear_image e.toLinearMap
  obtain ⟨r, hr⟩ := hP
  obtain ⟨s, hs⟩ := hQ
  let φ := r ∘ Function.invFunOn s (stdSimplex ℝ (Fin 3))
  have hφ : IsPLHomeomorphOn φ (e '' C) P := hs.symm.trans hr
  have hP : IsPLBall 2 P := ⟨r, hr⟩
  have hQ : IsPLBall 2 (e '' C) := ⟨s, hs⟩
  have hbdQ := hQ.isPolyhedron.isClosed.frontier_subset
  have hbdP := hP.isPolyhedron.isClosed.frontier_subset
  have hfront := hφ.image_frontier rfl hQ.isPolyhedron.isClosed hP.isPolyhedron.isClosed
  have hfrontmap : _root_.Set.MapsTo φ (frontier (e '' C)) (frontier P) :=
    fun z hz => hfront.subset (_root_.Set.mem_image_of_mem φ hz)
  have hfφ : IsPiecewiseAffineOn (f ∘ φ) (frontier (e '' C)) := by
    have h := hf.comp (hφ.isPiecewiseAffineOn.mono_of_isPolyhedron
      hQ.isPLSphere_frontier.isPolyhedron hbdQ)
    have hsub : frontier (e '' C) ⊆ φ ⁻¹' frontier P := hfrontmap
    rwa [_root_.Set.inter_eq_self_of_subset_left hsub] at h
  obtain ⟨g, hg, hgeq, hgmap⟩ := exists_piecewise_affine_convex_disk_extension hQ hQc hU
    hfφ (hmap.comp hfrontmap)
  let ψ := Function.invFunOn φ (e '' C)
  have hψ : _root_.Set.MapsTo ψ P (e '' C) := hφ.symm.bijOn.mapsTo
  have hψfront : _root_.Set.MapsTo ψ (frontier P) (frontier (e '' C)) := by
    intro z hz
    exact (hφ.symm.image_frontier rfl hP.isPolyhedron.isClosed hQ.isPolyhedron.isClosed).subset
      (_root_.Set.mem_image_of_mem ψ hz)
  refine ⟨g ∘ ψ, ?_, ?_, hgmap.comp hψ⟩
  · have h := hg.comp hφ.symm.isPiecewiseAffineOn
    change IsPiecewiseAffineOn (g ∘ ψ) (P ∩ ψ ⁻¹' (e '' C)) at h
    have hsub : P ⊆ ψ ⁻¹' (e '' C) := hψ
    rwa [_root_.Set.inter_eq_self_of_subset_left hsub] at h
  · intro z hz
    change g (ψ z) = f z
    rw [hgeq (hψfront hz)]
    exact congrArg f (hφ.bijOn.invOn_invFunOn.2 (hbdP hz))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.exists_isPiecewiseAffineOn_extension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.exists_isPiecewiseAffineOn_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.exists_isPiecewiseAffineOn_extension ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.exists_isPiecewiseAffineOn_extension

end DifferentialGeometry.Topology.PiecewiseLinear
