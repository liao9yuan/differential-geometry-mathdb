/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import Submission.DifferentialGeometry.External.ClassificationOfSurfaces.Moise.PlaneComplex
import Mathlib.Topology.Piecewise

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Extending a homeomorphism of a closed planar patch

Moise's elementary free-triangle move is first constructed on a finite polygonal patch.  Since
the move fixes the patch frontier, it extends to an ambient homeomorphism by the identity.  This
file proves that pasting step independently of the particular triangulated patch.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

/-- Changing only the proof that a point belongs to an equal set does not change the point. -/
theorem coe_setCongr_apply {X : Type*} [TopologicalSpace X] {s t : Set X}
    (h : s = t) (z : s) : ((Homeomorph.setCongr h z : t) : X) = z := by
  subst t
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.coe_setCongr_apply then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.coe_setCongr_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.coe_setCongr_apply ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.coe_setCongr_apply

namespace TriangleMesh

variable (M : TriangleMesh)

/-- Repositioning a fixed abstract triangle mesh gives a canonical homeomorphism between the old
and new geometric supports, obtained by preserving barycentric coordinates. -/
noncomputable def repositionHomeomorph (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex))) :
    M.toPlaneComplex.support ≃ₜ
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.support :=
  (M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2).symm.trans
    ((M.reposition position' hposition_injective haffineIndependent
      htriangle_inter).toPlaneComplex.realizationHomeomorph
        (M.reposition position' hposition_injective haffineIndependent
          htriangle_inter).toPlaneComplex_isPure2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.repositionHomeomorph then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.repositionHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.repositionHomeomorph ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.repositionHomeomorph

@[simp] theorem repositionHomeomorph_apply_realization (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (x : GeometricRealization M.toPlaneComplex.Vertex M.toPlaneComplex.cells) :
    M.repositionHomeomorph position' hposition_injective haffineIndependent htriangle_inter
        (M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2 x) =
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.realizationHomeomorph
          (M.reposition position' hposition_injective haffineIndependent
            htriangle_inter).toPlaneComplex_isPure2 x := by
  exact congrArg
    ((M.reposition position' hposition_injective haffineIndependent
      htriangle_inter).toPlaneComplex.realizationHomeomorph
        (M.reposition position' hposition_injective haffineIndependent
          htriangle_inter).toPlaneComplex_isPure2)
    ((M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2).symm_apply_apply x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.repositionHomeomorph_apply_realization then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.repositionHomeomorph_apply_realization"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.repositionHomeomorph_apply_realization ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.repositionHomeomorph_apply_realization

theorem coe_repositionHomeomorph_apply_realization (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (x : GeometricRealization M.toPlaneComplex.Vertex M.toPlaneComplex.cells) :
    (M.repositionHomeomorph position' hposition_injective haffineIndependent htriangle_inter
        (M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2 x) : Plane) =
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.baryEval x.1 := by
  exact congrArg Subtype.val (M.repositionHomeomorph_apply_realization position'
    hposition_injective haffineIndependent htriangle_inter x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.coe_repositionHomeomorph_apply_realization then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.coe_repositionHomeomorph_apply_realization"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.coe_repositionHomeomorph_apply_realization ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.coe_repositionHomeomorph_apply_realization

theorem coe_repositionHomeomorph_apply (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (z : M.toPlaneComplex.support) :
    (M.repositionHomeomorph position' hposition_injective haffineIndependent
        htriangle_inter z : Plane) =
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.baryEval
          ((M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2).symm z).1 := by
  let x := (M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2).symm z
  have hz : z = M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2 x := by
    exact
      (M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2).apply_symm_apply z |>.symm
  change (M.repositionHomeomorph position' hposition_injective haffineIndependent
      htriangle_inter z : Plane) =
    (M.reposition position' hposition_injective haffineIndependent
      htriangle_inter).toPlaneComplex.baryEval x.1
  rw [hz, repositionHomeomorph_apply_realization]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.coe_repositionHomeomorph_apply then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.coe_repositionHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.coe_repositionHomeomorph_apply ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.coe_repositionHomeomorph_apply

theorem coe_repositionHomeomorph_trans_setCongr_apply
    (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (hsupport :
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.support = M.toPlaneComplex.support)
    (z : M.toPlaneComplex.support) :
    (((M.repositionHomeomorph position' hposition_injective haffineIndependent
        htriangle_inter).trans (Homeomorph.setCongr hsupport)) z : Plane) =
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.baryEval
          ((M.toPlaneComplex.realizationHomeomorph M.toPlaneComplex_isPure2).symm z).1 := by
  exact M.coe_repositionHomeomorph_apply position' hposition_injective haffineIndependent
    htriangle_inter z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.coe_repositionHomeomorph_trans_setCongr_apply then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.coe_repositionHomeomorph_trans_setCongr_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.coe_repositionHomeomorph_trans_setCongr_apply ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.coe_repositionHomeomorph_trans_setCongr_apply

end TriangleMesh

/-- Extend a homeomorphism of a closed planar patch by the identity outside the patch. -/
noncomputable def extendHomeomorphByIdentity {P : Set Plane} (hP : IsClosed P)
    (e : P ≃ₜ P)
    (hfrontier : ∀ x (hx : x ∈ frontier P), (e ⟨x, hP.frontier_subset hx⟩).1 = x) :
    Plane ≃ₜ Plane := by
  classical
  let f : Plane → Plane := fun x => if hx : x ∈ P then (e ⟨x, hx⟩).1 else x
  let g : Plane → Plane := fun x => if hx : x ∈ P then (e.symm ⟨x, hx⟩).1 else x
  have hgf : Function.LeftInverse g f := by
    intro x
    by_cases hx : x ∈ P
    · simp [f, g, hx]
    · simp [f, g, hx]
  have hfg : Function.RightInverse g f := by
    intro x
    by_cases hx : x ∈ P
    · simp [f, g, hx]
    · simp [f, g, hx]
  have hfrontierSymm :
      ∀ x (hx : x ∈ frontier P), (e.symm ⟨x, hP.frontier_subset hx⟩).1 = x := by
    intro x hx
    have he : e ⟨x, hP.frontier_subset hx⟩ = ⟨x, hP.frontier_subset hx⟩ := by
      apply Subtype.ext
      exact hfrontier x hx
    have := congrArg Subtype.val (e.symm_apply_eq.mpr he.symm)
    exact this
  have hfContinuousOn : ContinuousOn f P := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hcont : Continuous fun x : P => (e x).1 :=
      continuous_subtype_val.comp e.continuous
    convert hcont using 1
    funext x
    simp [f, x.property]
  have hgContinuousOn : ContinuousOn g P := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hcont : Continuous fun x : P => (e.symm x).1 :=
      continuous_subtype_val.comp e.symm.continuous
    convert hcont using 1
    funext x
    simp [g, x.property]
  have hfContinuous : Continuous f := by
    have hpaste : Set.piecewise P f id = f := by
      funext x
      by_cases hx : x ∈ P <;> simp [Set.piecewise, f, hx]
    rw [← hpaste]
    apply continuous_piecewise
    · intro x hx
      have hxP := hP.frontier_subset hx
      simp [f, hxP, hfrontier x hx]
    · simpa [hP.closure_eq] using hfContinuousOn
    · exact continuous_id.continuousOn
  have hgContinuous : Continuous g := by
    have hpaste : Set.piecewise P g id = g := by
      funext x
      by_cases hx : x ∈ P <;> simp [Set.piecewise, g, hx]
    rw [← hpaste]
    apply continuous_piecewise
    · intro x hx
      have hxP := hP.frontier_subset hx
      simp [g, hxP, hfrontierSymm x hx]
    · simpa [hP.closure_eq] using hgContinuousOn
    · exact continuous_id.continuousOn
  exact
    { toEquiv := Equiv.mk f g hgf hfg
      continuous_toFun := hfContinuous
      continuous_invFun := hgContinuous }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.extendHomeomorphByIdentity then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.extendHomeomorphByIdentity"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.extendHomeomorphByIdentity ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.extendHomeomorphByIdentity

theorem extendHomeomorphByIdentity_apply_mem {P : Set Plane} (hP : IsClosed P)
    (e : P ≃ₜ P)
    (hfrontier : ∀ x (hx : x ∈ frontier P), (e ⟨x, hP.frontier_subset hx⟩).1 = x)
    {x : Plane} (hx : x ∈ P) :
    extendHomeomorphByIdentity hP e hfrontier x = (e ⟨x, hx⟩).1 := by
  classical
  simp [extendHomeomorphByIdentity, hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.extendHomeomorphByIdentity_apply_mem then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.extendHomeomorphByIdentity_apply_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.extendHomeomorphByIdentity_apply_mem ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.extendHomeomorphByIdentity_apply_mem

theorem extendHomeomorphByIdentity_apply_not_mem {P : Set Plane} (hP : IsClosed P)
    (e : P ≃ₜ P)
    (hfrontier : ∀ x (hx : x ∈ frontier P), (e ⟨x, hP.frontier_subset hx⟩).1 = x)
    {x : Plane} (hx : x ∉ P) :
    extendHomeomorphByIdentity hP e hfrontier x = x := by
  classical
  simp [extendHomeomorphByIdentity, hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.extendHomeomorphByIdentity_apply_not_mem then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.extendHomeomorphByIdentity_apply_not_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.extendHomeomorphByIdentity_apply_not_mem ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.extendHomeomorphByIdentity_apply_not_mem

namespace TriangleMesh

variable (M : TriangleMesh)

/-- A repositioning with unchanged support and fixed support frontier extends to an ambient plane
homeomorphism. -/
noncomputable def ambientRepositionHomeomorph (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (hsupport :
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.support = M.toPlaneComplex.support)
    (hfrontier : ∀ x (hx : x ∈ frontier M.toPlaneComplex.support),
      (((M.repositionHomeomorph position' hposition_injective haffineIndependent
        htriangle_inter).trans (Homeomorph.setCongr hsupport))
          ⟨x, M.toPlaneComplex.isCompact_support.isClosed.frontier_subset hx⟩).1 = x) :
    Plane ≃ₜ Plane :=
  extendHomeomorphByIdentity M.toPlaneComplex.isCompact_support.isClosed
    ((M.repositionHomeomorph position' hposition_injective haffineIndependent
      htriangle_inter).trans (Homeomorph.setCongr hsupport)) hfrontier

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.ambientRepositionHomeomorph then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.ambientRepositionHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.ambientRepositionHomeomorph ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.ambientRepositionHomeomorph

theorem ambientRepositionHomeomorph_eqOn_compl (position' : M.Vertex → Plane)
    (hposition_injective : Function.Injective position')
    (haffineIndependent : ∀ t ∈ M.triangles,
      AffineIndependent ℝ fun v : t => position' v)
    (htriangle_inter : ∀ s ∈ M.triangles, ∀ t ∈ M.triangles,
      convexHull ℝ (position' '' s) ∩ convexHull ℝ (position' '' t) =
        convexHull ℝ (position' '' ((s ∩ t : Finset M.Vertex) : Set M.Vertex)))
    (hsupport :
      (M.reposition position' hposition_injective haffineIndependent
        htriangle_inter).toPlaneComplex.support = M.toPlaneComplex.support)
    (hfrontier : ∀ x (hx : x ∈ frontier M.toPlaneComplex.support),
      (((M.repositionHomeomorph position' hposition_injective haffineIndependent
        htriangle_inter).trans (Homeomorph.setCongr hsupport))
          ⟨x, M.toPlaneComplex.isCompact_support.isClosed.frontier_subset hx⟩).1 = x) :
    Set.EqOn
      (M.ambientRepositionHomeomorph position' hposition_injective haffineIndependent
        htriangle_inter hsupport hfrontier)
      id M.toPlaneComplex.supportᶜ := by
  intro x hx
  exact extendHomeomorphByIdentity_apply_not_mem _ _ _ hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.ambientRepositionHomeomorph_eqOn_compl then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.ambientRepositionHomeomorph_eqOn_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.ambientRepositionHomeomorph_eqOn_compl ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.ambientRepositionHomeomorph_eqOn_compl

end TriangleMesh

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
