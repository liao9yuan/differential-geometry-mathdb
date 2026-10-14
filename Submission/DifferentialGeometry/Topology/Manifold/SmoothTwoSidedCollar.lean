/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set _root_.Topology
open scoped _root_.Manifold _root_.ContDiff

noncomputable section

universe u v w x

namespace DifferentialGeometry.Topology

def symmetricOpenInterval (a : ℝ) : TopologicalSpace.Opens ℝ :=
  ⟨Set.Ioo (-a) a, isOpen_Ioo⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.symmetricOpenInterval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.symmetricOpenInterval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.symmetricOpenInterval ``Submission.DifferentialGeometry.Topology.symmetricOpenInterval

structure SmoothTwoSidedCollar
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type x} [TopologicalSpace G]
    (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F G)
    {S : Type*} [TopologicalSpace S] [ChartedSpace H S]
    {M : Type*} [TopologicalSpace M] [ChartedSpace G M]
    (e : S → M) where
  radius : ℝ
  radius_pos : 0 < radius
  neighborhood : TopologicalSpace.Opens M
  toDiffeomorph :
    Diffeomorph (I.prod (modelWithCornersSelf ℝ ℝ)) J
      (S × symmetricOpenInterval radius) neighborhood ∞
  zero_eq : ∀ s,
    (toDiffeomorph (s, ⟨0, neg_lt_zero.mpr radius_pos, radius_pos⟩) : M) = e s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar

namespace SmoothTwoSidedCollar

variable
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type x} [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    {S : Type*} [TopologicalSpace S] [ChartedSpace H S]
    {M : Type*} [TopologicalSpace M] [ChartedSpace G M]
    {e : S → M} (h : SmoothTwoSidedCollar I J e)

instance transContinuousLinearEquiv_boundaryless
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [J.Boundaryless] (L : F ≃L[ℝ] F') :
    (J.transContinuousLinearEquiv L).Boundaryless where
  range_eq_univ := by
    rw [J.transContinuousLinearEquiv_range, J.range_eq_univ]
    exact Set.image_univ_of_surjective L.surjective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.transContinuousLinearEquiv_boundaryless then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.transContinuousLinearEquiv_boundaryless"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.transContinuousLinearEquiv_boundaryless ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.transContinuousLinearEquiv_boundaryless

def toFun : S × symmetricOpenInterval h.radius → M :=
  fun p => h.toDiffeomorph p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.toFun ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.toFun

theorem isOpenEmbedding_toFun : _root_.Topology.IsOpenEmbedding h.toFun :=
  h.neighborhood.2.isOpenEmbedding_subtypeVal.comp
    h.toDiffeomorph.toHomeomorph.isOpenEmbedding

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.isOpenEmbedding_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.isOpenEmbedding_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.isOpenEmbedding_toFun ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.isOpenEmbedding_toFun

@[simp]
theorem toFun_zero (s : S) :
    h.toFun (s, ⟨0, neg_lt_zero.mpr h.radius_pos, h.radius_pos⟩) = e s :=
  h.zero_eq s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.toFun_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.toFun_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.toFun_zero ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.toFun_zero

theorem contMDiff (h : SmoothTwoSidedCollar I J e) : ContMDiff I J ∞ e := by
  have he : e = fun s => h.toFun (s, ⟨0, neg_lt_zero.mpr h.radius_pos, h.radius_pos⟩) :=
    funext fun s => (h.toFun_zero s).symm
  rw [he]
  exact (contMDiff_subtype_val.comp h.toDiffeomorph.contMDiff).comp
    (contMDiff_id.prodMk contMDiff_const)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.contMDiff ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.contMDiff

theorem isEmbedding (h : SmoothTwoSidedCollar I J e) : _root_.Topology.IsEmbedding e := by
  have he : e = fun s => h.toFun (s, ⟨0, neg_lt_zero.mpr h.radius_pos, h.radius_pos⟩) :=
    funext fun s => (h.toFun_zero s).symm
  rw [he]
  exact h.isOpenEmbedding_toFun.isEmbedding.comp (isEmbedding_prodMkLeft _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.isEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.isEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.isEmbedding ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.isEmbedding

noncomputable def transAmbientModel {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (L : F ≃L[ℝ] F') : SmoothTwoSidedCollar I (J.transContinuousLinearEquiv L) e where
  radius := h.radius
  radius_pos := h.radius_pos
  neighborhood := h.neighborhood
  toDiffeomorph := h.toDiffeomorph.trans
    (ContinuousLinearEquiv.toTransContinuousLinearEquiv J h.neighborhood L)
  zero_eq := h.zero_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.transAmbientModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.transAmbientModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.transAmbientModel ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.transAmbientModel

@[simp]
theorem transAmbientModel_radius {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (L : F ≃L[ℝ] F') :
    (h.transAmbientModel L).radius = h.radius :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.transAmbientModel_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.transAmbientModel_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.transAmbientModel_radius ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.transAmbientModel_radius

@[simp]
theorem transAmbientModel_toFun {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (L : F ≃L[ℝ] F') (p : S × symmetricOpenInterval h.radius) :
    (h.transAmbientModel L).toFun p = h.toFun p :=
  by
    simp only [toFun, transAmbientModel]
    apply congrArg Subtype.val
    change (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞)
      J h.neighborhood L)
      (h.toDiffeomorph p) = h.toDiffeomorph p
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.transAmbientModel_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.transAmbientModel_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.transAmbientModel_toFun ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.transAmbientModel_toFun

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
variable {S' : Type*} [TopologicalSpace S'] [ChartedSpace H' S']

def reparametrize (d : Diffeomorph I' I S' S ∞) :
    SmoothTwoSidedCollar I' J (e ∘ d) where
  radius := h.radius
  radius_pos := h.radius_pos
  neighborhood := h.neighborhood
  toDiffeomorph :=
    (d.prodCongr (Diffeomorph.refl 𝓘(ℝ) (symmetricOpenInterval h.radius) ∞)).trans
      h.toDiffeomorph
  zero_eq := fun s ↦ h.zero_eq (d s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.reparametrize then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.reparametrize"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.reparametrize ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.reparametrize

@[simp] theorem reparametrize_radius (d : Diffeomorph I' I S' S ∞) :
    (h.reparametrize d).radius = h.radius := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.reparametrize_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.reparametrize_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.reparametrize_radius ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.reparametrize_radius

@[simp] theorem reparametrize_neighborhood (d : Diffeomorph I' I S' S ∞) :
    (h.reparametrize d).neighborhood = h.neighborhood := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.reparametrize_neighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.reparametrize_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.reparametrize_neighborhood ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.reparametrize_neighborhood

@[simp] theorem reparametrize_toFun (d : Diffeomorph I' I S' S ∞)
    (p : S' × symmetricOpenInterval h.radius) :
    (h.reparametrize d).toFun p = h.toFun (d p.1, p.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.reparametrize_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.reparametrize_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.reparametrize_toFun ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.reparametrize_toFun

end SmoothTwoSidedCollar

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.SmoothTwoSidedCollar

variable
    {E H F G S M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [TopologicalSpace S] [ChartedSpace H S] [Nonempty S]
    [TopologicalSpace M] [ChartedSpace G M]
    {e : S → M} (d : SmoothTwoSidedCollar I J e)

private def intervalInclusion :
    _root_.PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
      (S × symmetricOpenInterval d.radius) (S × ℝ) ∞ :=
  PartialDiffeomorph.prod (Diffeomorph.refl I S ∞).toPartialDiffeomorph
    (PartialDiffeomorph.subtypeVal (symmetricOpenInterval d.radius)
      ⟨⟨0, neg_lt_zero.mpr d.radius_pos, d.radius_pos⟩⟩)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.intervalInclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SmoothTwoSidedCollar.intervalInclusion target :: scope.openDecls } }

def toPartialDiffeomorph :
    _root_.PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) J (S × ℝ) M ∞ :=
  ((d.intervalInclusion.symm.trans d.toDiffeomorph.toPartialDiffeomorph).trans
    (PartialDiffeomorph.subtypeVal d.neighborhood
      ⟨d.toDiffeomorph (Classical.choice inferInstance,
        ⟨0, neg_lt_zero.mpr d.radius_pos, d.radius_pos⟩)⟩))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.toPartialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.toPartialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.toPartialDiffeomorph ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.toPartialDiffeomorph

@[simp] theorem toPartialDiffeomorph_apply (p : S × symmetricOpenInterval d.radius) :
    d.toPartialDiffeomorph (p.1, p.2.val) = d.toFun p := by
  change ((d.toDiffeomorph (d.intervalInclusion.symm (d.intervalInclusion p))) : M) = _
  exact congrArg (fun q : S × symmetricOpenInterval d.radius => (d.toDiffeomorph q : M))
    (d.intervalInclusion.toPartialEquiv.left_inv (show p ∈ d.intervalInclusion.source from ⟨trivial, trivial⟩))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.toPartialDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.toPartialDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.toPartialDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.toPartialDiffeomorph_apply

theorem toPartialDiffeomorph_symm_apply (p : d.neighborhood) :
    d.toPartialDiffeomorph.symm p.val =
      ((d.toDiffeomorph.symm p).1, (d.toDiffeomorph.symm p).2.val) := by
  let hN : Nonempty d.neighborhood := ⟨d.toDiffeomorph (Classical.choice inferInstance,
    ⟨0, neg_lt_zero.mpr d.radius_pos, d.radius_pos⟩)⟩
  let j := PartialDiffeomorph.subtypeVal (I := J) d.neighborhood hN
  change d.intervalInclusion (d.toDiffeomorph.symm (j.symm (j p))) = _
  exact congrArg (fun q : d.neighborhood => d.intervalInclusion (d.toDiffeomorph.symm q))
    (j.toPartialEquiv.left_inv (show p ∈ j.source from trivial))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.toPartialDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.toPartialDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.toPartialDiffeomorph_symm_apply ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.toPartialDiffeomorph_symm_apply

@[simp] theorem toPartialDiffeomorph_source :
    d.toPartialDiffeomorph.source = _root_.Set.univ ×ˢ _root_.Set.Ioo (-d.radius) d.radius := by
  ext q
  change q ∈ (((d.intervalInclusion.symm.toOpenPartialHomeomorph.trans
    d.toDiffeomorph.toPartialDiffeomorph.toOpenPartialHomeomorph).trans
    (PartialDiffeomorph.subtypeVal (I := J) d.neighborhood _).toOpenPartialHomeomorph).source) ↔ _
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source]
  change ((q ∈ d.intervalInclusion.target ∧ True) ∧ True) ↔ _
  simp only [intervalInclusion, PartialDiffeomorph.prod, PartialDiffeomorph.subtypeVal,
    Diffeomorph.toPartialDiffeomorph, symmetricOpenInterval, and_true, _root_.Set.mem_prod, _root_.Set.mem_univ, _root_.Set.mem_Ioo, true_and]
  erw [OpenPartialHomeomorph.prod_target]
  simp only [_root_.Set.mem_prod]
  erw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
  change (True ∧ (-d.radius < q.2 ∧ q.2 < d.radius)) ↔ _
  exact ⟨And.right, fun h => ⟨trivial, h⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.toPartialDiffeomorph_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.toPartialDiffeomorph_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.toPartialDiffeomorph_source ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.toPartialDiffeomorph_source

@[simp] theorem toPartialDiffeomorph_target : d.toPartialDiffeomorph.target = d.neighborhood := by
  ext x
  simp [toPartialDiffeomorph, intervalInclusion, PartialDiffeomorph.prod,
    PartialDiffeomorph.subtypeVal, Diffeomorph.toPartialDiffeomorph,
    _root_.PartialDiffeomorph.trans]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.toPartialDiffeomorph_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.toPartialDiffeomorph_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.toPartialDiffeomorph_target ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.toPartialDiffeomorph_target

omit [Nonempty S]

private def reverseInterval :
    Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (symmetricOpenInterval d.radius) (symmetricOpenInterval d.radius) ∞ where
  toFun t := ⟨-t.val, by constructor <;> linarith [t.property.1, t.property.2]⟩
  invFun t := ⟨-t.val, by constructor <;> linarith [t.property.1, t.property.2]⟩
  left_inv t := Subtype.ext (neg_neg t.val)
  right_inv t := Subtype.ext (neg_neg t.val)
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff (symmetricOpenInterval d.radius) _).mp
    contMDiff_subtype_val.neg
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff (symmetricOpenInterval d.radius) _).mp
    contMDiff_subtype_val.neg

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverseInterval
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverseInterval target :: scope.openDecls } }

def reverse : SmoothTwoSidedCollar I J e where
  radius := d.radius
  radius_pos := d.radius_pos
  neighborhood := d.neighborhood
  toDiffeomorph := ((Diffeomorph.refl I S ∞).prodCongr d.reverseInterval).trans d.toDiffeomorph
  zero_eq s := by
    change d.toFun (s, ⟨-(0 : ℝ), _⟩) = e s
    exact (congrArg (fun t : symmetricOpenInterval d.radius => d.toFun (s, t))
      (Subtype.ext (neg_zero : -(0 : ℝ) = 0))).trans (d.toFun_zero s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverse ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverse

@[simp] theorem reverse_radius : d.reverse.radius = d.radius := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverse_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverse_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverse_radius ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverse_radius

@[simp] theorem reverse_neighborhood : d.reverse.neighborhood = d.neighborhood := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverse_neighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverse_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverse_neighborhood ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverse_neighborhood

@[simp] theorem reverse_toFun (p : S × symmetricOpenInterval d.radius) :
    d.reverse.toFun p = d.toFun (p.1, ⟨-p.2.val, by
      constructor <;> linarith [p.2.property.1, p.2.property.2]⟩) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverse_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverse_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverse_toFun ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverse_toFun

theorem reverse_symm_toDiffeomorph (p : d.neighborhood) :
    d.reverse.toDiffeomorph.symm p =
      ((d.toDiffeomorph.symm p).1, ⟨-(d.toDiffeomorph.symm p).2.val, by
        change -(d.radius) < -(d.toDiffeomorph.symm p).2.val ∧ -(d.toDiffeomorph.symm p).2.val < d.radius
        constructor <;> linarith [(d.toDiffeomorph.symm p).2.property.1,
          (d.toDiffeomorph.symm p).2.property.2]⟩) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverse_symm_toDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverse_symm_toDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverse_symm_toDiffeomorph ``Submission.DifferentialGeometry.Topology.SmoothTwoSidedCollar.reverse_symm_toDiffeomorph

end DifferentialGeometry.Topology.SmoothTwoSidedCollar
