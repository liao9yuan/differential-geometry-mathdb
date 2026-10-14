import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientation
import Submission.DifferentialGeometry.Topology.Manifold.OrientationLinearVariation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Filter _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem preferredChartTangentEquiv_eq_coordChange (p x : M)
    (hx : x ∈ (chartAt H p).source) :
    (preferredChartTangentEquiv I p x hx : E →L[ℝ] E) = tangentCoordChange I x p x := by
  have h₁ := TangentBundle.continuousLinearMapAt_trivializationAt (I := I) hx
  have h₂ := TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) hx
  exact h₁.symm.trans h₂

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.preferredChartTangentEquiv_eq_coordChange then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.preferredChartTangentEquiv_eq_coordChange"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.preferredChartTangentEquiv_eq_coordChange ``Submission.DifferentialGeometry.Topology.Manifold.preferredChartTangentEquiv_eq_coordChange

def preferredChartTransitionEquiv (p q : M)
    (x : ↥((chartAt H p).source ∩ (chartAt H q).source)) : E ≃L[ℝ] E :=
  (preferredChartTangentEquiv I p x.val x.property.1).symm.trans
    (preferredChartTangentEquiv I q x.val x.property.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.preferredChartTransitionEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.preferredChartTransitionEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.preferredChartTransitionEquiv ``Submission.DifferentialGeometry.Topology.Manifold.preferredChartTransitionEquiv

theorem preferredChartTransitionEquiv_apply (p q : M)
    (x : ↥((chartAt H p).source ∩ (chartAt H q).source)) (v : E) :
    preferredChartTransitionEquiv I p q x v = tangentCoordChange I p q x.val v := by
  let e := preferredChartTangentEquiv I p x.val x.property.1
  have hcomp := tangentCoordChange_comp (I := I) (w := x.val) (x := p) (y := q)
    (z := x.val) (v := e.symm v)
    (show x.val ∈ (extChartAt I x.val).source ∩ (extChartAt I p).source ∩
      (extChartAt I q).source from
      ⟨⟨by simp, by simpa only [extChartAt_source] using x.property.1⟩,
        by simpa only [extChartAt_source] using x.property.2⟩)
  have hp := congrArg (fun A : E →L[ℝ] E => A (e.symm v))
    (preferredChartTangentEquiv_eq_coordChange I p x.val x.property.1)
  have hq := congrArg (fun A : E →L[ℝ] E => A (e.symm v))
    (preferredChartTangentEquiv_eq_coordChange I q x.val x.property.2)
  have hp' : tangentCoordChange I x.val p x.val (e.symm v) = v :=
    hp.symm.trans (e.apply_symm_apply v)
  rw [hp'] at hcomp
  exact hq.trans hcomp.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.preferredChartTransitionEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.preferredChartTransitionEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.preferredChartTransitionEquiv_apply ``Submission.DifferentialGeometry.Topology.Manifold.preferredChartTransitionEquiv_apply

theorem continuous_preferredChartTransition (p q : M) :
    Continuous (fun x : ↥((chartAt H p).source ∩ (chartAt H q).source) =>
      (preferredChartTransitionEquiv I p q x : E →L[ℝ] E)) := by
  have h : Continuous (fun x : ↥((chartAt H p).source ∩ (chartAt H q).source) =>
      tangentCoordChange I p q x.val) := by
    apply ContinuousOn.comp_continuous (continuousOn_tangentCoordChange (I := I) p q)
      continuous_subtype_val
    intro x
    simpa only [extChartAt_source] using x.property
  apply h.congr
  intro x
  apply ContinuousLinearMap.ext
  intro v
  exact (preferredChartTransitionEquiv_apply I p q x v).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.continuous_preferredChartTransition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.continuous_preferredChartTransition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.continuous_preferredChartTransition ``Submission.DifferentialGeometry.Topology.Manifold.continuous_preferredChartTransition

theorem preferredChartTransition_orientation_locallyConstant (p q : M)
    (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    IsLocallyConstant (fun x : ↥((chartAt H p).source ∩ (chartAt H q).source) =>
      Orientation.map _ (preferredChartTransitionEquiv I p q x).toLinearEquiv o) :=
  orientation_map_isLocallyConstant _ (continuous_preferredChartTransition I p q) o

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.preferredChartTransition_orientation_locallyConstant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.preferredChartTransition_orientation_locallyConstant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.preferredChartTransition_orientation_locallyConstant ``Submission.DifferentialGeometry.Topology.Manifold.preferredChartTransition_orientation_locallyConstant

omit [FiniteDimensional ℝ E] in
theorem orientation_map_trans (e f : E ≃ₗ[ℝ] E)
    (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    Orientation.map _ (e.trans f) o = Orientation.map _ f (Orientation.map _ e o) := by
  induction o using Module.Ray.ind with
  | h o ho => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.orientation_map_trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.orientation_map_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.orientation_map_trans ``Submission.DifferentialGeometry.Topology.Manifold.orientation_map_trans

theorem preferredChartTransition_orientation (p q : M)
    (x : ↥((chartAt H p).source ∩ (chartAt H q).source))
    (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    Orientation.map _ (preferredChartTransitionEquiv I p q x).toLinearEquiv
        (Orientation.map _
          (preferredChartTangentEquiv I p x.val x.property.1).toLinearEquiv o) =
      Orientation.map _ (preferredChartTangentEquiv I q x.val x.property.2).toLinearEquiv o := by
  change Orientation.map _
    ((preferredChartTangentEquiv I p x.val x.property.1).toLinearEquiv.symm.trans
      (preferredChartTangentEquiv I q x.val x.property.2).toLinearEquiv)
    (Orientation.map _ (preferredChartTangentEquiv I p x.val x.property.1).toLinearEquiv o) = _
  rw [orientation_map_trans]
  rw [← Orientation.map_symm, Equiv.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.preferredChartTransition_orientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.preferredChartTransition_orientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.preferredChartTransition_orientation ``Submission.DifferentialGeometry.Topology.Manifold.preferredChartTransition_orientation
end DifferentialGeometry.Topology.Manifold
