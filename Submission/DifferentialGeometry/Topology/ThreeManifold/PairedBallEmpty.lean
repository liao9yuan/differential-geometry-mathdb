import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallGluing
import Submission.DifferentialGeometry.Topology.Homeomorph.Sigma
import Submission.DifferentialGeometry.Topology.Homeomorph.QuotientDescent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Metric _root_.Submission.Metric

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.E3 target :: scope.openDecls } }
variable {V : Type v} {E : Type w} [IsEmpty E]
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (t : Bool) →
    OrientedBallChart (N (endpoint e t)).toClosedOrientedManifold)

def puncturedFactorHomeomorphOfIsEmpty (v : V) :
    PuncturedFactor N endpoint chart v ≃ₜ (N v).Carrier := by
  let h (x : (N v).Carrier) : (⟨v, x⟩ : Σ v, (N v).Carrier) ∉
      ⋃ p, flagMap N endpoint chart p '' _root_.Metric.ball (0 : E3) 1 := by
    intro hx
    obtain ⟨p, _⟩ := mem_iUnion.mp hx
    exact isEmptyElim p.1
  exact
    { toFun := Subtype.val
      invFun := fun x => ⟨x, h x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk h }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.puncturedFactorHomeomorphOfIsEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.puncturedFactorHomeomorphOfIsEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.puncturedFactorHomeomorphOfIsEmpty ``Submission.DifferentialGeometry.Topology.PairedBallGluing.puncturedFactorHomeomorphOfIsEmpty

@[simp] theorem puncturedFactorHomeomorphOfIsEmpty_apply (v : V)
    (x : PuncturedFactor N endpoint chart v) :
    puncturedFactorHomeomorphOfIsEmpty N endpoint chart v x = x.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.puncturedFactorHomeomorphOfIsEmpty_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.puncturedFactorHomeomorphOfIsEmpty_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.puncturedFactorHomeomorphOfIsEmpty_apply ``Submission.DifferentialGeometry.Topology.PairedBallGluing.puncturedFactorHomeomorphOfIsEmpty_apply

def quotientHomeomorphOfIsEmpty
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' _root_.Metric.closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' _root_.Metric.closedBall (0 : E3) 2))
    (attachment : E → BoundaryAttachment) :
    Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e (attachment e) x y) ≃ₜ
      (Σ v, (N v).Carrier) :=
  (Homeomorph.Quot.emptyRelation _ (fun _ _ ⟨e, _⟩ => isEmptyElim e)).trans
    (Homeomorph.sigmaCongrRight (puncturedFactorHomeomorphOfIsEmpty N endpoint chart))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.quotientHomeomorphOfIsEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.quotientHomeomorphOfIsEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.quotientHomeomorphOfIsEmpty ``Submission.DifferentialGeometry.Topology.PairedBallGluing.quotientHomeomorphOfIsEmpty

@[simp] theorem quotientHomeomorphOfIsEmpty_mk
    (hdisj : Pairwise fun p q =>
      Disjoint (flagMap N endpoint chart p '' _root_.Metric.closedBall (0 : E3) 2)
        (flagMap N endpoint chart q '' _root_.Metric.closedBall (0 : E3) 2))
    (attachment : E → BoundaryAttachment) (v : V) (x : PuncturedFactor N endpoint chart v) :
    quotientHomeomorphOfIsEmpty N endpoint chart hdisj attachment (Quot.mk _ ⟨v, x⟩) =
      ⟨v, x.val⟩ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.quotientHomeomorphOfIsEmpty_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.quotientHomeomorphOfIsEmpty_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.quotientHomeomorphOfIsEmpty_mk ``Submission.DifferentialGeometry.Topology.PairedBallGluing.quotientHomeomorphOfIsEmpty_mk

end DifferentialGeometry.Topology.PairedBallGluing
