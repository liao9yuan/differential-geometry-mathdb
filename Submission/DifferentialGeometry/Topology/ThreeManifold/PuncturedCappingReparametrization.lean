import Submission.DifferentialGeometry.Topology.ThreeManifold.PuncturedCapping
import Mathlib.Topology.Homeomorph.Quotient

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Metric _root_.Function

namespace DifferentialGeometry.Topology.SphericalCapping

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Sphere" => Metric.sphere (0 : E3) 1
local notation "Annulus" => Sphere × _root_.Set.Icc (1 / 4 : ℝ) 1

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)
  (B : T.Boundary → ClosedCell 3 ≃ₜ ClosedCell 3)
  (hsmall : ∀ b (x : ClosedCell 3), ‖x.val‖ ≤ 1 / 4 → B b x = x)
  (hboundary : ∀ b (z : Sphere), B b (sphereToClosedCell z) = sphereToClosedCell z)

private def capAnnuliReparametrization : (Σ _b : T.Boundary, Annulus) ≃ₜ
    (Σ _b : T.Boundary, Annulus) where
  toFun q := ⟨q.1, C.capAnnulusHomeomorph q.1 (B q.1) (hsmall q.1) q.2⟩
  invFun q := ⟨q.1, (C.capAnnulusHomeomorph q.1 (B q.1) (hsmall q.1)).symm q.2⟩
  left_inv q := by
    cases q with
    | mk b q =>
      exact congrArg (Sigma.mk b) ((C.capAnnulusHomeomorph b (B b) (hsmall b)).symm_apply_apply q)
  right_inv q := by
    cases q with
    | mk b q =>
      exact congrArg (Sigma.mk b) ((C.capAnnulusHomeomorph b (B b) (hsmall b)).apply_symm_apply q)
  continuous_toFun := continuous_sigma fun b =>
    continuous_sigmaMk.comp (C.capAnnulusHomeomorph b (B b) (hsmall b)).continuous
  continuous_invFun := continuous_sigma fun b =>
    continuous_sigmaMk.comp (C.capAnnulusHomeomorph b (B b) (hsmall b)).symm.continuous

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.capAnnuliReparametrization
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.capAnnuliReparametrization target :: scope.openDecls } }

include hboundary in
private theorem capAnnuliReparametrization_boundary (q : Σ _b : T.Boundary, Sphere) :
    C.capAnnuliReparametrization B hsmall (capAnnuliBoundaryInclusion q) =
      capAnnuliBoundaryInclusion q := by
  cases q with
  | mk b z =>
    change (⟨b, C.capAnnulusHomeomorph b (B b) (hsmall b) (z, ⟨1, by norm_num⟩)⟩ :
      Σ _b : T.Boundary, Annulus) = ⟨b, z, ⟨1, by norm_num⟩⟩
    rw [C.capAnnulusHomeomorph_outer b (B b) (hsmall b) (hboundary b) z]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.capAnnuliReparametrization_boundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.capAnnuliReparametrization_boundary target :: scope.openDecls } }

include hboundary in
private theorem capAnnuliReparametrization_rel
    (x y : (Σ _b : T.Boundary, Annulus) ⊕ _root_.Set.range C.coreInclusion) :
    adjunctionRel (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap x y ↔
      adjunctionRel (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        (((C.capAnnuliReparametrization B hsmall).sumCongr (Homeomorph.refl _)) x)
        (((C.capAnnuliReparametrization B hsmall).sumCongr (Homeomorph.refl _)) y) := by
  let e := (C.capAnnuliReparametrization B hsmall).sumCongr
    (Homeomorph.refl (_root_.Set.range C.coreInclusion))
  have hc (a : Σ _b : T.Boundary, Sphere) :
      e (Sum.inl (capAnnuliBoundaryInclusion a)) = Sum.inl (capAnnuliBoundaryInclusion a) :=
    congrArg Sum.inl (C.capAnnuliReparametrization_boundary B hsmall hboundary a)
  have hl (a : Σ _b : T.Boundary, Sphere) :
      e (Sum.inr (C.capAnnuliAttachingMap a)) = Sum.inr (C.capAnnuliAttachingMap a) := rfl
  constructor
  · rintro ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨a, Or.inl ⟨hc a, hl a⟩⟩
    · exact ⟨a, Or.inr ⟨hc a, hl a⟩⟩
  · rintro ⟨a, h | h⟩
    · exact ⟨a, Or.inl ⟨e.injective (h.1.trans (hc a).symm),
        e.injective (h.2.trans (hl a).symm)⟩⟩
    · exact ⟨a, Or.inr ⟨e.injective (h.1.trans (hc a).symm),
        e.injective (h.2.trans (hl a).symm)⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.capAnnuliReparametrization_rel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.capAnnuliReparametrization_rel target :: scope.openDecls } }

def puncturedCappingReparametrization : C.PuncturedCapping ≃ₜ C.PuncturedCapping :=
  Homeomorph.Quot.congr
    ((C.capAnnuliReparametrization B hsmall).sumCongr (Homeomorph.refl _))
    (C.capAnnuliReparametrization_rel B hsmall hboundary)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization ``Submission.DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization

@[simp] theorem puncturedCappingReparametrization_core (x : _root_.Set.range C.coreInclusion) :
    C.puncturedCappingReparametrization B hsmall hboundary
      (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap x) =
      adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_core ``Submission.DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_core

@[simp] theorem puncturedCappingReparametrization_annulus (b : T.Boundary) (q : Annulus) :
    C.puncturedCappingReparametrization B hsmall hboundary
      (adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap ⟨b, q⟩) =
      adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        ⟨b, C.capAnnulusHomeomorph b (B b) (hsmall b) q⟩ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_annulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_annulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_annulus ``Submission.DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_annulus

@[simp] theorem puncturedCappingReparametrization_symm_core (x : _root_.Set.range C.coreInclusion) :
    (C.puncturedCappingReparametrization B hsmall hboundary).symm
      (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap x) =
      adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_symm_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_symm_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_symm_core ``Submission.DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_symm_core

@[simp] theorem puncturedCappingReparametrization_symm_annulus (b : T.Boundary) (q : Annulus) :
    (C.puncturedCappingReparametrization B hsmall hboundary).symm
      (adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap ⟨b, q⟩) =
      adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        ⟨b, (C.capAnnulusHomeomorph b (B b) (hsmall b)).symm q⟩ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_symm_annulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_symm_annulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_symm_annulus ``Submission.DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_symm_annulus

theorem puncturedCappingReparametrization_inner (b : T.Boundary) (z : Sphere) :
    C.puncturedCappingReparametrization B hsmall hboundary
      (adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        ⟨b, z, ⟨1 / 4, by norm_num⟩⟩) =
      adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        ⟨b, z, ⟨1 / 4, by norm_num⟩⟩ := by
  rw [C.puncturedCappingReparametrization_annulus,
    C.capAnnulusHomeomorph_inner b (B b) (hsmall b) z]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_inner ``Submission.DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_inner

theorem puncturedCappingReparametrization_outer (b : T.Boundary) (z : Sphere) :
    C.puncturedCappingReparametrization B hsmall hboundary
      (adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        ⟨b, z, ⟨1, by norm_num⟩⟩) =
      adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        (C.capAnnuliAttachingMap ⟨b, z⟩) := by
  rw [C.puncturedCappingReparametrization_annulus,
    C.capAnnulusHomeomorph_outer b (B b) (hsmall b) (hboundary b) z]
  exact adjunction_coherence (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap ⟨b, z⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_outer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_outer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_outer ``Submission.DifferentialGeometry.Topology.SphericalCapping.puncturedCappingReparametrization_outer

def puncturedCappingComplementReparametrization :
    ((⋃ b, (C.capBallChart b).chart '' Metric.ball (0 : E3) 1)ᶜ : Set N.Carrier) ≃ₜ
      ((⋃ b, (C.capBallChart b).chart '' Metric.ball (0 : E3) 1)ᶜ : Set N.Carrier) :=
  C.puncturedCappingHomeomorph.symm.trans
    ((C.puncturedCappingReparametrization B hsmall hboundary).trans C.puncturedCappingHomeomorph)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization ``Submission.DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization

theorem puncturedCappingComplementReparametrization_homeomorph (x : C.PuncturedCapping) :
    C.puncturedCappingComplementReparametrization B hsmall hboundary
      (C.puncturedCappingHomeomorph x) =
      C.puncturedCappingHomeomorph (C.puncturedCappingReparametrization B hsmall hboundary x) := by
  simp only [puncturedCappingComplementReparametrization, Homeomorph.trans_apply,
    Homeomorph.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_homeomorph ``Submission.DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_homeomorph

theorem puncturedCappingComplementReparametrization_core (x : _root_.Set.range C.coreInclusion) :
    C.puncturedCappingComplementReparametrization B hsmall hboundary
      (C.puncturedCappingHomeomorph (adjunctionLower
        (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap x)) =
      C.puncturedCappingHomeomorph (adjunctionLower
        (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap x) := by
  rw [C.puncturedCappingComplementReparametrization_homeomorph,
    C.puncturedCappingReparametrization_core]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_core ``Submission.DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_core

theorem puncturedCappingComplementReparametrization_annulus (b : T.Boundary) (q : Annulus) :
    (C.puncturedCappingComplementReparametrization B hsmall hboundary
      (C.puncturedCappingHomeomorph (adjunctionCell (capAnnuliBoundaryInclusion (T := T))
        C.capAnnuliAttachingMap ⟨b, q⟩))).val =
      C.capAnnulusMap b (C.capAnnulusHomeomorph b (B b) (hsmall b) q) := by
  rw [C.puncturedCappingComplementReparametrization_homeomorph,
    C.puncturedCappingReparametrization_annulus, C.puncturedCappingHomeomorph_annulus]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_annulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_annulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_annulus ``Submission.DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_annulus

theorem puncturedCappingComplementReparametrization_eq_self_of_mem_core
    (x : ((⋃ b, (C.capBallChart b).chart '' Metric.ball (0 : E3) 1)ᶜ : Set N.Carrier))
    (hx : x.val ∈ _root_.Set.range C.coreInclusion) :
    C.puncturedCappingComplementReparametrization B hsmall hboundary x = x := by
  have heq : C.puncturedCappingHomeomorph (adjunctionLower
      (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap ⟨x.val, hx⟩) = x :=
    Subtype.ext rfl
  rw [← heq, C.puncturedCappingComplementReparametrization_core]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_eq_self_of_mem_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_eq_self_of_mem_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_eq_self_of_mem_core ``Submission.DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_eq_self_of_mem_core

theorem puncturedCappingComplementReparametrization_apply_of_eq_capAnnulusMap
    (b : T.Boundary) (q : Annulus)
    (x : ((⋃ b, (C.capBallChart b).chart '' Metric.ball (0 : E3) 1)ᶜ : Set N.Carrier))
    (hx : x.val = C.capAnnulusMap b q) :
    (C.puncturedCappingComplementReparametrization B hsmall hboundary x).val =
      C.cap b (B b ⟨q.2.val • q.1.val, by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [q.2.property.1]),
          norm_eq_of_mem_sphere, mul_one]
        exact q.2.property.2⟩) := by
  have heq : C.puncturedCappingHomeomorph (adjunctionCell
      (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap ⟨b, q⟩) = x :=
    Subtype.ext hx.symm
  rw [← heq, C.puncturedCappingComplementReparametrization_annulus]
  exact C.capAnnulusHomeomorph_apply b (B b) (hsmall b) q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_apply_of_eq_capAnnulusMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_apply_of_eq_capAnnulusMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_apply_of_eq_capAnnulusMap ``Submission.DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_apply_of_eq_capAnnulusMap

theorem puncturedCappingComplementReparametrization_inner (b : T.Boundary) (z : Sphere) :
    C.puncturedCappingComplementReparametrization B hsmall hboundary
      (C.puncturedCappingHomeomorph (adjunctionCell (capAnnuliBoundaryInclusion (T := T))
        C.capAnnuliAttachingMap ⟨b, z, ⟨1 / 4, by norm_num⟩⟩)) =
      C.puncturedCappingHomeomorph (adjunctionCell (capAnnuliBoundaryInclusion (T := T))
        C.capAnnuliAttachingMap ⟨b, z, ⟨1 / 4, by norm_num⟩⟩) := by
  rw [C.puncturedCappingComplementReparametrization_homeomorph,
    C.puncturedCappingReparametrization_inner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_inner ``Submission.DifferentialGeometry.Topology.SphericalCapping.puncturedCappingComplementReparametrization_inner

end DifferentialGeometry.Topology.SphericalCapping
