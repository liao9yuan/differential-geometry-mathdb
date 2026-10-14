import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Homeomorph.Quotient

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

private local instance sphereAntipodalQuotientDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphereAntipodalQuotientDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphereAntipodalQuotientDimension target :: scope.openDecls } }

def sphereAntipodalSetoid : Setoid SphereTwo where
  r x y := y = x ∨ y = -x
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      intro x y h
      rcases h with h | h
      · exact Or.inl h.symm
      · right
        rw [h, neg_neg]
    trans := by
      intro x y z hxy hyz
      rcases hxy with hxy | hxy
      · simpa only [hxy] using hyz
      · rcases hyz with hyz | hyz
        · exact Or.inr (hyz.trans hxy)
        · left
          simpa only [hxy, neg_neg] using hyz }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphereAntipodalSetoid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphereAntipodalSetoid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphereAntipodalSetoid ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphereAntipodalSetoid

abbrev SphereAntipodalQuotient := Quotient sphereAntipodalSetoid

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient

namespace SphereAntipodalQuotient

def proj : SphereTwo → SphereAntipodalQuotient := Quotient.mk sphereAntipodalSetoid

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.proj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.proj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.proj ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.proj

theorem proj_eq_iff (x y : SphereTwo) : proj x = proj y ↔ y = x ∨ y = -x :=
  Quotient.eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.proj_eq_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.proj_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.proj_eq_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.proj_eq_iff

theorem continuous_proj : Continuous proj := continuous_quotient_mk'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.continuous_proj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.continuous_proj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.continuous_proj ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.continuous_proj

theorem surjective_proj : Function.Surjective proj := Quotient.mk_surjective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.surjective_proj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.surjective_proj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.surjective_proj ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.surjective_proj

theorem isOpenMap_proj : IsOpenMap proj := by
  intro U hU
  apply (isQuotientMap_quotient_mk' (s := sphereAntipodalSetoid)).isOpen_preimage.mp
  have hsaturation : proj ⁻¹' (proj '' U) = U ∪ (fun x : SphereTwo => -x) ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨y, hy, heq⟩
      rcases (proj_eq_iff y x).mp heq with h | h
      · left
        simpa only [h] using hy
      · right
        change -x ∈ U
        simpa only [h, neg_neg] using hy
    · rintro (hx | hx)
      · exact ⟨x, hx, rfl⟩
      · refine ⟨-x, hx, (proj_eq_iff (-x) x).mpr (Or.inr ?_)⟩
        exact (neg_neg x).symm
  change IsOpen (proj ⁻¹' (proj '' U))
  rw [hsaturation]
  exact hU.union (hU.preimage (contMDiff_neg_sphere (n := 2) (m := ∞)).continuous)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.isOpenMap_proj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.isOpenMap_proj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.isOpenMap_proj ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.isOpenMap_proj

theorem exists_homeomorph {M : Type*} [TopologicalSpace M]
    (pi : SphereTwo → M) (hcontinuous : Continuous pi) (hopen : IsOpenMap pi)
    (hsurjective : Function.Surjective pi)
    (hfibres : ∀ x y : SphereTwo, pi x = pi y ↔ y = x ∨ y = -x) :
    ∃ d : SphereAntipodalQuotient ≃ₜ M, ∀ x : SphereTwo, d (proj x) = pi x := by
  let f : C(SphereTwo, M) := ⟨pi, hcontinuous⟩
  have hquotient : _root_.Topology.IsQuotientMap f := hopen.isQuotientMap hcontinuous hsurjective
  have hker (x y : SphereTwo) : sphereAntipodalSetoid x y ↔ Setoid.ker f x y :=
    (hfibres x y).symm
  let e : SphereAntipodalQuotient ≃ₜ Quotient (Setoid.ker f) :=
    Homeomorph.Quotient.congrRight hker
  exact ⟨e.trans hquotient.homeomorph, fun _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.exists_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.exists_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.exists_homeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.exists_homeomorph

def productProjection (p : SphereTwo × ℝ) : SphereAntipodalQuotient × ℝ :=
  (proj p.1, p.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.productProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.productProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.productProjection ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.productProjection

theorem productProjection_eq_iff (p q : SphereTwo × ℝ) :
    productProjection p = productProjection q ↔ q = p ∨ q = (-p.1, p.2) := by
  constructor
  · intro h
    have hsphere : proj p.1 = proj q.1 := congrArg Prod.fst h
    have hline : p.2 = q.2 := congrArg (fun z : SphereAntipodalQuotient × ℝ => z.2) h
    rcases (proj_eq_iff p.1 q.1).mp hsphere with hfirst | hfirst
    · exact Or.inl (Prod.ext hfirst hline.symm)
    · exact Or.inr (Prod.ext hfirst hline.symm)
  · rintro (rfl | rfl)
    · rfl
    · exact Prod.ext ((proj_eq_iff p.1 (-p.1)).mpr (Or.inr rfl)) rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.productProjection_eq_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.productProjection_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.productProjection_eq_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.productProjection_eq_iff

theorem continuous_productProjection : Continuous productProjection :=
  continuous_proj.prodMap continuous_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.continuous_productProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.continuous_productProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.continuous_productProjection ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.continuous_productProjection

theorem isOpenMap_productProjection : IsOpenMap productProjection :=
  isOpenMap_proj.prodMap IsOpenMap.id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.isOpenMap_productProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.isOpenMap_productProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.isOpenMap_productProjection ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.isOpenMap_productProjection

theorem surjective_productProjection : Function.Surjective productProjection :=
  surjective_proj.prodMap Function.surjective_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.surjective_productProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.surjective_productProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.surjective_productProjection ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.surjective_productProjection

theorem exists_product_homeomorph {M : Type*} [TopologicalSpace M]
    (pi : SphereTwo × ℝ → M) (hcontinuous : Continuous pi) (hopen : IsOpenMap pi)
    (hsurjective : Function.Surjective pi)
    (hfibres : ∀ p q : SphereTwo × ℝ, pi p = pi q ↔ q = p ∨ q = (-p.1, p.2)) :
    ∃ d : (SphereAntipodalQuotient × ℝ) ≃ₜ M,
      ∀ p : SphereTwo × ℝ, d (productProjection p) = pi p := by
  let f : C(SphereTwo × ℝ, M) := ⟨pi, hcontinuous⟩
  let q : C(SphereTwo × ℝ, SphereAntipodalQuotient × ℝ) :=
    ⟨productProjection, continuous_productProjection⟩
  have hq : _root_.Topology.IsQuotientMap q := isOpenMap_productProjection.isQuotientMap
    continuous_productProjection surjective_productProjection
  have hf : _root_.Topology.IsQuotientMap f := hopen.isQuotientMap hcontinuous hsurjective
  have hker (x y : SphereTwo × ℝ) : Setoid.ker q x y ↔ Setoid.ker f x y :=
    (productProjection_eq_iff x y).trans (hfibres x y).symm
  let e : Quotient (Setoid.ker q) ≃ₜ Quotient (Setoid.ker f) :=
    Homeomorph.Quotient.congrRight hker
  refine ⟨(hq.homeomorph.symm.trans e).trans hf.homeomorph, ?_⟩
  intro p
  have hp : hq.homeomorph (Quotient.mk (Setoid.ker q) p) = q p := rfl
  change hf.homeomorph (e (hq.homeomorph.symm (q p))) = pi p
  rw [← hp, hq.homeomorph.symm_apply_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.exists_product_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.exists_product_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.exists_product_homeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.exists_product_homeomorph

end SphereAntipodalQuotient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
