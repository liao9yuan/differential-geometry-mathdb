import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.LocalMaps

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.SelfAttachment

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SelfAttachment.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SelfAttachment.E3 target :: scope.openDecls } }

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
  (c d : BallChart 3 (𝓡 3) M)
  (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (a : Sphere (n := 3) ≃ₜ Sphere (n := 3))

private def coreDefault : c.DoublePunctured d :=
  c.firstBoundaryMap d hcd (Classical.choice (ConnectedSumQuotient.nonempty_sphere_of_neZero (n := 3)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SelfAttachment.coreDefault
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SelfAttachment.coreDefault target :: scope.openDecls } }

def coreExtension (x : M) : Quotient c d hcd a := by
  classical
  exact if hx : x ∈ (c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1)ᶜ then
    coreInclusion c d hcd a ⟨x, hx⟩ else coreInclusion c d hcd a (coreDefault c d hcd)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.coreExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.coreExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.coreExtension ``Submission.DifferentialGeometry.Topology.SelfAttachment.coreExtension

omit [T2Space M] in
theorem coreExtension_apply (x : c.DoublePunctured d) : coreExtension c d hcd a x.val = coreInclusion c d hcd a x :=
  dif_pos x.property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.coreExtension_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.coreExtension_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.coreExtension_apply ``Submission.DifferentialGeometry.Topology.SelfAttachment.coreExtension_apply

theorem coreExtension_coreInterior : (fun x : coreInterior c d => coreExtension c d hcd a x.val) =
    coreInteriorInclusion c d hcd a := by
  funext x
  exact coreExtension_apply c d hcd a (coreInteriorToCore c d x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.coreExtension_coreInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.coreExtension_coreInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.coreExtension_coreInterior ``Submission.DifferentialGeometry.Topology.SelfAttachment.coreExtension_coreInterior

omit [T2Space M] in
theorem coreExtension_firstBoundary (z : Sphere (n := 3)) :
    coreExtension c d hcd a (c.chart z.val) = coreInclusion c d hcd a (c.firstBoundaryMap d hcd z) :=
  coreExtension_apply c d hcd a (c.firstBoundaryMap d hcd z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.coreExtension_firstBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.coreExtension_firstBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.coreExtension_firstBoundary ``Submission.DifferentialGeometry.Topology.SelfAttachment.coreExtension_firstBoundary

omit [T2Space M] in
theorem coreExtension_secondBoundary (z : Sphere (n := 3)) :
    coreExtension c d hcd a (d.chart z.val) = coreInclusion c d hcd a (c.secondBoundaryMap d hcd z) :=
  coreExtension_apply c d hcd a (c.secondBoundaryMap d hcd z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.coreExtension_secondBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.coreExtension_secondBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.coreExtension_secondBoundary ``Submission.DifferentialGeometry.Topology.SelfAttachment.coreExtension_secondBoundary

end DifferentialGeometry.Topology.SelfAttachment
