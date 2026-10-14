import Submission.DifferentialGeometry.Topology.ProjectiveSpace.SphereAntipodalQuotient

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Set _root_.Topology
open scoped _root_.Manifold _root_.ContDiff

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Cylinder" => SphereTwo × ℝ

private local instance cylinderDiagonalQuotientDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDiagonalQuotientDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDiagonalQuotientDimension target :: scope.openDecls } }

def cylinderDiagonalSetoid : Setoid Cylinder where
  r p q := q = p ∨ q = -p
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      intro p q h
      rcases h with h | h
      · exact Or.inl h.symm
      · right
        rw [h, neg_neg]
    trans := by
      intro p q r hpq hqr
      rcases hpq with hpq | hpq
      · simpa only [hpq] using hqr
      · rcases hqr with hqr | hqr
        · exact Or.inr (hqr.trans hpq)
        · left
          simpa only [hpq, neg_neg] using hqr }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDiagonalSetoid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDiagonalSetoid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDiagonalSetoid ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinderDiagonalSetoid

abbrev CylinderDiagonalQuotient := Quotient cylinderDiagonalSetoid

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient

namespace CylinderDiagonalQuotient

def proj : Cylinder → CylinderDiagonalQuotient := Quotient.mk cylinderDiagonalSetoid

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.proj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.proj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.proj ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.proj

theorem proj_eq_iff (p q : Cylinder) : proj p = proj q ↔ q = p ∨ q = (-p.1, -p.2) :=
  Quotient.eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.proj_eq_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.proj_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.proj_eq_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.proj_eq_iff

theorem continuous_proj : Continuous proj := continuous_quotient_mk'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.continuous_proj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.continuous_proj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.continuous_proj ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.continuous_proj

theorem surjective_proj : Function.Surjective proj := Quotient.mk_surjective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.surjective_proj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.surjective_proj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.surjective_proj ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.surjective_proj

theorem isOpenMap_proj : IsOpenMap proj := by
  intro U hU
  apply (isQuotientMap_quotient_mk' (s := cylinderDiagonalSetoid)).isOpen_preimage.mp
  have hsaturation : proj ⁻¹' (proj '' U) = U ∪ (fun p : Cylinder => -p) ⁻¹' U := by
    ext p
    constructor
    · rintro ⟨q, hq, heq⟩
      rcases (proj_eq_iff q p).mp heq with h | h
      · left
        simpa only [h] using hq
      · right
        have hp : p = -q := h
        change -p ∈ U
        simpa only [hp, neg_neg] using hq
    · rintro (hp | hp)
      · exact ⟨p, hp, rfl⟩
      · refine ⟨-p, hp, (proj_eq_iff (-p) p).mpr (Or.inr ?_)⟩
        exact (neg_neg p).symm
  change IsOpen (proj ⁻¹' (proj '' U))
  rw [hsaturation]
  have hneg : Continuous (fun p : Cylinder => -p) :=
    (contMDiff_neg_sphere (n := 2) (m := ∞)).continuous.prodMap _root_.ContinuousNeg.continuous_neg
  exact hU.union (hU.preimage hneg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.isOpenMap_proj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.isOpenMap_proj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.isOpenMap_proj ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.isOpenMap_proj

theorem exists_homeomorph {M : Type*} [TopologicalSpace M]
    (pi : Cylinder → M) (hcontinuous : Continuous pi) (hopen : IsOpenMap pi)
    (hsurjective : Function.Surjective pi)
    (hfibres : ∀ p q : Cylinder, pi p = pi q ↔ q = p ∨ q = (-p.1, -p.2)) :
    ∃ d : CylinderDiagonalQuotient ≃ₜ M, ∀ p : Cylinder, d (proj p) = pi p := by
  let f : C(Cylinder, M) := ⟨pi, hcontinuous⟩
  have hquotient : _root_.Topology.IsQuotientMap f := hopen.isQuotientMap hcontinuous hsurjective
  have hker (p q : Cylinder) : cylinderDiagonalSetoid p q ↔ Setoid.ker f p q :=
    (hfibres p q).symm
  let e : CylinderDiagonalQuotient ≃ₜ Quotient (Setoid.ker f) :=
    Homeomorph.Quotient.congrRight hker
  exact ⟨e.trans hquotient.homeomorph, fun _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_homeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderDiagonalQuotient.exists_homeomorph

end CylinderDiagonalQuotient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
