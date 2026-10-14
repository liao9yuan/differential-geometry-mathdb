import Submission.DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormProjective
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Descent
import Mathlib.Topology.Homeomorph.Quotient
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardDiscardedModels
import Submission.DifferentialGeometry.Topology.Manifold.OrientationDiffeomorphTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.SphericalSpaceFormGroup

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalSpaceFormGroup.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalSpaceFormGroup.E3 target :: scope.openDecls } }
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalSpaceFormGroup.E4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalSpaceFormGroup.E4 target :: scope.openDecls } }
private abbrev S3 := Metric.sphere (0 : E4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalSpaceFormGroup.S3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalSpaceFormGroup.S3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.SphericalSpaceFormGroup.instFactEqNatFinrankRealE4HAddOfNat : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalSpaceFormGroup.instFactEqNatFinrankRealE4HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalSpaceFormGroup.instFactEqNatFinrankRealE4HAddOfNat target :: scope.openDecls } }

open private antipodalIsometry from
  Submission.DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormProjective

theorem antipodal_projection_eq_iff (x y : S3) :
    antipodal.projection x = antipodal.projection y ↔
      x = y ∨ (x : E4) = -(y : E4) := by
  rw [projection_eq_iff]
  constructor
  · rintro ⟨γ, hγ⟩
    have hmem : γ.val = 1 ∨ γ.val = antipodalIsometry := γ.property
    rcases hmem with h | h
    · left
      apply Subtype.ext
      have hv := congrArg Subtype.val hγ
      simpa only [DifferentialGeometry.Geometry.sphereDiffeo_coe, h,
        LinearIsometryEquiv.coe_one, id_eq] using hv
    · right
      have hv := congrArg Subtype.val hγ
      have hneg : -(x : E4) = (y : E4) := by
        simpa only [DifferentialGeometry.Geometry.sphereDiffeo_coe, h,
          antipodalIsometry, LinearIsometryEquiv.coe_neg] using hv
      exact (neg_eq_iff_eq_neg.mp hneg)
  · rintro (h | h)
    · subst y
      refine ⟨1, ?_⟩
      apply Subtype.ext
      simp only [DifferentialGeometry.Geometry.sphereDiffeo_coe,
        Subgroup.coe_one, LinearIsometryEquiv.coe_one, id_eq]
    · refine ⟨⟨antipodalIsometry, Or.inr rfl⟩, ?_⟩
      apply Subtype.ext
      change -(x : E4) = (y : E4)
      rw [h, neg_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalSpaceFormGroup.antipodal_projection_eq_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalSpaceFormGroup.antipodal_projection_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalSpaceFormGroup.antipodal_projection_eq_iff ``Submission.DifferentialGeometry.Topology.SphericalSpaceFormGroup.antipodal_projection_eq_iff

theorem exists_antipodal_diffeomorph_of_presentation
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace E3 Z]
    (p : S3 → Z) (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (hsurj : _root_.Function.Surjective p)
    (hfibers : ∀ x y : S3,
      p x = p y ↔ x = y ∨ (x : E4) = -(y : E4)) :
    ∃ e : antipodal.manifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ Z,
      (∀ x : S3, e (antipodal.projection x) = p x) ∧
      ∀ x : S3, e.symm (p x) = antipodal.projection x := by
  have hquot : _root_.Topology.IsQuotientMap p :=
    hp.isOpenMap.isQuotientMap hp.contMDiff.continuous hsurj
  have hker (x y : S3) : antipodal.orbitSetoid x y ↔ Setoid.ker p x y := by
    change antipodal.orbitSetoid x y ↔ p x = p y
    exact (show antipodal.orbitSetoid x y ↔
      antipodal.projection x = antipodal.projection y from Quotient.eq.symm).trans
        ((antipodal_projection_eq_iff x y).trans (hfibers x y).symm)
  let q : antipodal.Orbit ≃ₜ Quotient (Setoid.ker p) :=
    Homeomorph.Quotient.congrRight hker
  let pc : C(S3,Z) := ⟨p,hp.contMDiff.continuous⟩
  let d : antipodal.Orbit ≃ₜ Z := q.trans (_root_.Topology.IsQuotientMap.homeomorph (f := pc) hquot)
  have hd (x : S3) : d (antipodal.projection x) = p x := rfl
  obtain ⟨e, he⟩ :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_diffeomorph_of_homeomorph_comp_localDiffeomorph
      antipodal.projection antipodal.projection_isLocalDiffeomorph
      antipodal.projection_surjective p hp d hd
  have heq (x : S3) : e (antipodal.projection x) = p x := by
    rw [he]
    exact hd x
  refine ⟨e, heq, ?_⟩
  intro x
  exact (congrArg e.symm (heq x)).symm.trans (e.symm_apply_apply _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalSpaceFormGroup.exists_antipodal_diffeomorph_of_presentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalSpaceFormGroup.exists_antipodal_diffeomorph_of_presentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalSpaceFormGroup.exists_antipodal_diffeomorph_of_presentation ``Submission.DifferentialGeometry.Topology.SphericalSpaceFormGroup.exists_antipodal_diffeomorph_of_presentation

theorem exists_oriented_antipodal_diffeomorph_of_presentation
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace E3 Z] [IsManifold (𝓡 3) ∞ Z]
    (p : S3 → Z) (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (hsurj : Function.Surjective p)
    (hfibers : ∀ x y : S3,
      p x = p y ↔ x = y ∨ (x : E4) = -(y : E4)) :
    ∃ (o : ManifoldOrientation (𝓡 3) Z 3)
      (e : antipodal.manifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ Z),
      e.preservesOrientation antipodal.manifold.orientation o ∧
      (∀ x : S3, e (antipodal.projection x) = p x) ∧
      ∀ x : S3, e.symm (p x) = antipodal.projection x := by
  obtain ⟨e, he, hei⟩ := exists_antipodal_diffeomorph_of_presentation p hp hsurj hfibers
  obtain ⟨o, ho⟩ := Manifold.exists_manifoldOrientation_diffeomorph_map e
    antipodal.manifold.orientation
  refine ⟨o, e, ?_, he, hei⟩
  intro x
  rw [ho]
  dsimp only
  rw [e.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalSpaceFormGroup.exists_oriented_antipodal_diffeomorph_of_presentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalSpaceFormGroup.exists_oriented_antipodal_diffeomorph_of_presentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalSpaceFormGroup.exists_oriented_antipodal_diffeomorph_of_presentation ``Submission.DifferentialGeometry.Topology.SphericalSpaceFormGroup.exists_oriented_antipodal_diffeomorph_of_presentation

end DifferentialGeometry.Topology.SphericalSpaceFormGroup

namespace DifferentialGeometry.Topology

universe u

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.E3 target :: scope.openDecls } }
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.E4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.E4 target :: scope.openDecls } }
private abbrev S3 := Metric.sphere (0 : E4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.S3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.S3 target :: scope.openDecls } }

theorem isPoincareStandard_of_antipodal_presentation
    {Z : Type u} [TopologicalSpace Z] [ChartedSpace E3 Z]
    (p : S3 → Z) (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (hsurj : _root_.Function.Surjective p)
    (hfibers : ∀ x y : S3,
      p x = p y ↔ x = y ∨ (x : E4) = -(y : E4)) :
    isPoincareStandard Z := by
  obtain ⟨e, _, _⟩ := SphericalSpaceFormGroup.exists_antipodal_diffeomorph_of_presentation
    p hp hsurj hfibers
  let L := ClosedOrientedManifold.uliftOrientedDiffeomorph
    SphericalSpaceFormGroup.antipodal.manifold.toClosedOrientedManifold
  exact isPoincareStandard_of_diffeomorph (e.symm.trans L.val)
    isPoincareStandard_projectiveThreeSpaceLift

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPoincareStandard_of_antipodal_presentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPoincareStandard_of_antipodal_presentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPoincareStandard_of_antipodal_presentation ``Submission.DifferentialGeometry.Topology.isPoincareStandard_of_antipodal_presentation

end DifferentialGeometry.Topology
