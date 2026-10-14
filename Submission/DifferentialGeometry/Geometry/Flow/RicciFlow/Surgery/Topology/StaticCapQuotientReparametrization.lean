import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCapWitnessProducer
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Homeomorph.Quotient

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Submission.Set _root_.Function

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable (δ : ℝ) (ζ a : Sphere 2 ≃ₜ Sphere 2) (B : ThreeBall ≃ₜ ThreeBall)
  (hboundary : ∀ y, B (sphereToThreeBall y) = sphereToThreeBall (a y))

include hboundary in
private theorem staticCapGluingRel_reparametrize_iff
    (x y : neckRetainedCollar δ ⊕ ThreeBall) :
    staticCapGluingRel δ (a.trans ζ) x y ↔
      staticCapGluingRel δ ζ
        (Homeomorph.sumCongr (Homeomorph.refl (neckRetainedCollar δ)) B x)
        (Homeomorph.sumCongr (Homeomorph.refl (neckRetainedCollar δ)) B y) := by
  let e := Homeomorph.sumCongr (Homeomorph.refl (neckRetainedCollar δ)) B
  constructor
  · rintro ⟨z, hz, rfl, rfl⟩
    refine ⟨a z, hz, ?_, rfl⟩
    exact congrArg Sum.inr (hboundary z)
  · rintro ⟨z, hz, hx, hy⟩
    refine ⟨a.symm z, hz, ?_, ?_⟩
    · apply e.injective
      change e x = Sum.inr (B (sphereToThreeBall (a.symm z)))
      rw [hboundary, a.apply_symm_apply]
      exact hx
    · apply e.injective
      change e y = Sum.inl (⟨(ζ (a (a.symm z)), 0), le_rfl, hz⟩ : neckRetainedCollar δ)
      rw [a.apply_symm_apply]
      exact hy

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapGluingRel_reparametrize_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapGluingRel_reparametrize_iff target :: scope.openDecls } }

def staticCapQuotientReparametrization :
    StaticCapQuotient δ (a.trans ζ) ≃ₜ StaticCapQuotient δ ζ :=
  (quotientEqvGenHomeomorph (staticCapGluingRel δ (a.trans ζ))).symm.trans
    ((Homeomorph.Quot.congr (Homeomorph.sumCongr (Homeomorph.refl (neckRetainedCollar δ)) B)
      (staticCapGluingRel_reparametrize_iff δ ζ a B hboundary)).trans
      (quotientEqvGenHomeomorph (staticCapGluingRel δ ζ)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientReparametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientReparametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientReparametrization ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientReparametrization

@[simp] theorem staticCapQuotientReparametrization_retained (x : neckRetainedCollar δ) :
    staticCapQuotientReparametrization δ ζ a B hboundary (Quotient.mk _ (Sum.inl x)) =
      Quotient.mk _ (Sum.inl x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientReparametrization_retained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientReparametrization_retained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientReparametrization_retained ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientReparametrization_retained

@[simp] theorem staticCapQuotientReparametrization_cap (x : ThreeBall) :
    staticCapQuotientReparametrization δ ζ a B hboundary (Quotient.mk _ (Sum.inr x)) =
      Quotient.mk _ (Sum.inr (B x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientReparametrization_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientReparametrization_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientReparametrization_cap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientReparametrization_cap

@[simp] theorem staticCapQuotientReparametrization_symm_retained (x : neckRetainedCollar δ) :
    (staticCapQuotientReparametrization δ ζ a B hboundary).symm (Quotient.mk _ (Sum.inl x)) =
      Quotient.mk _ (Sum.inl x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientReparametrization_symm_retained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientReparametrization_symm_retained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientReparametrization_symm_retained ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientReparametrization_symm_retained

@[simp] theorem staticCapQuotientReparametrization_symm_cap (x : ThreeBall) :
    (staticCapQuotientReparametrization δ ζ a B hboundary).symm (Quotient.mk _ (Sum.inr x)) =
      Quotient.mk _ (Sum.inr (B.symm x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientReparametrization_symm_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientReparametrization_symm_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientReparametrization_symm_cap ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.staticCapQuotientReparametrization_symm_cap

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
