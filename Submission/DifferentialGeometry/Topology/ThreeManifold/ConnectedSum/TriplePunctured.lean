import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Collar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.BallChart

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.BallChart.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.BallChart.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.BallChart.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.BallChart.S2 target :: scope.openDecls } }

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] (e c d : BallChart 3 (𝓡 3) M)

abbrev TriplePunctured := {x : M // x ∉ e.chart '' Metric.ball 0 1 ∧
  x ∉ c.chart '' Metric.ball 0 1 ∧ x ∉ d.chart '' Metric.ball 0 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.TriplePunctured then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.TriplePunctured"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.TriplePunctured ``Submission.DifferentialGeometry.Topology.BallChart.TriplePunctured

def tripleToFirst (x : e.TriplePunctured c d) : e.Punctured := ⟨x.val, x.property.1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.tripleToFirst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.tripleToFirst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.tripleToFirst ``Submission.DifferentialGeometry.Topology.BallChart.tripleToFirst

def tripleToPair (x : e.TriplePunctured c d) : c.DoublePunctured d :=
  ⟨x.val, fun h => h.elim x.property.2.1 x.property.2.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.tripleToPair then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.tripleToPair"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.tripleToPair ``Submission.DifferentialGeometry.Topology.BallChart.tripleToPair

def firstRestriction : Set e.Punctured :=
  {x | x.val ∉ c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.firstRestriction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.firstRestriction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.firstRestriction ``Submission.DifferentialGeometry.Topology.BallChart.firstRestriction

def pairRestriction : Set (c.DoublePunctured d) := {x | x.val ∉ e.chart '' Metric.ball 0 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.pairRestriction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.pairRestriction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.pairRestriction ``Submission.DifferentialGeometry.Topology.BallChart.pairRestriction

theorem isClosed_firstRestriction : IsClosed (firstRestriction e c d) :=
  (c.isOpen_chart_image_ball.union d.isOpen_chart_image_ball).isClosed_compl.preimage continuous_subtype_val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.isClosed_firstRestriction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.isClosed_firstRestriction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.isClosed_firstRestriction ``Submission.DifferentialGeometry.Topology.BallChart.isClosed_firstRestriction

theorem isClosed_pairRestriction : IsClosed (pairRestriction e c d) :=
  e.isOpen_chart_image_ball.isClosed_compl.preimage continuous_subtype_val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.isClosed_pairRestriction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.isClosed_pairRestriction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.isClosed_pairRestriction ``Submission.DifferentialGeometry.Topology.BallChart.isClosed_pairRestriction

def firstRestrictionHomeomorph : firstRestriction e c d ≃ₜ e.TriplePunctured c d where
  toFun x := ⟨x.val.val, x.val.property, (not_or.mp x.property).1, (not_or.mp x.property).2⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, not_or.mpr x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.firstRestrictionHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.firstRestrictionHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.firstRestrictionHomeomorph ``Submission.DifferentialGeometry.Topology.BallChart.firstRestrictionHomeomorph

def pairRestrictionHomeomorph : pairRestriction e c d ≃ₜ e.TriplePunctured c d where
  toFun x := ⟨x.val.val, x.property, (not_or.mp x.val.property).1, (not_or.mp x.val.property).2⟩
  invFun x := ⟨⟨x.val, not_or.mpr x.property.2⟩, x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.pairRestrictionHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.pairRestrictionHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.pairRestrictionHomeomorph ``Submission.DifferentialGeometry.Topology.BallChart.pairRestrictionHomeomorph

variable (hec : Disjoint (e.chart '' Metric.closedBall 0 2) (c.chart '' Metric.closedBall 0 2))
  (hed : Disjoint (e.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))

def tripleBoundaryFirst (z : S2) : e.TriplePunctured c d :=
  ⟨e.chart z, (e.boundaryMap z).property, chart_sphere_not_mem_other_ball e c hec z,
    chart_sphere_not_mem_other_ball e d hed z⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.tripleBoundaryFirst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.tripleBoundaryFirst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.tripleBoundaryFirst ``Submission.DifferentialGeometry.Topology.BallChart.tripleBoundaryFirst

def tripleBoundarySecond (z : S2) : e.TriplePunctured c d :=
  ⟨c.chart z, chart_sphere_not_mem_other_ball c e hec.symm z, (c.boundaryMap z).property,
    chart_sphere_not_mem_other_ball c d hcd z⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.tripleBoundarySecond then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.tripleBoundarySecond"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.tripleBoundarySecond ``Submission.DifferentialGeometry.Topology.BallChart.tripleBoundarySecond

def tripleBoundaryThird (z : S2) : e.TriplePunctured c d :=
  ⟨d.chart z, chart_sphere_not_mem_other_ball d e hed.symm z,
    chart_sphere_not_mem_other_ball d c hcd.symm z, (d.boundaryMap z).property⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.tripleBoundaryThird then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.tripleBoundaryThird"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.tripleBoundaryThird ``Submission.DifferentialGeometry.Topology.BallChart.tripleBoundaryThird

theorem continuous_tripleBoundaryFirst : Continuous (tripleBoundaryFirst e c d hec hed) :=
  (e.chart.contMDiffOn_toFun.continuousOn.comp_continuous continuous_subtype_val
    (fun z => e.sphere_subset_source z.property)).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.continuous_tripleBoundaryFirst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.continuous_tripleBoundaryFirst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.continuous_tripleBoundaryFirst ``Submission.DifferentialGeometry.Topology.BallChart.continuous_tripleBoundaryFirst

theorem continuous_tripleBoundarySecond : Continuous (tripleBoundarySecond e c d hec hcd) :=
  (c.chart.contMDiffOn_toFun.continuousOn.comp_continuous continuous_subtype_val
    (fun z => c.sphere_subset_source z.property)).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.continuous_tripleBoundarySecond then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.continuous_tripleBoundarySecond"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.continuous_tripleBoundarySecond ``Submission.DifferentialGeometry.Topology.BallChart.continuous_tripleBoundarySecond

theorem continuous_tripleBoundaryThird : Continuous (tripleBoundaryThird e c d hed hcd) :=
  (d.chart.contMDiffOn_toFun.continuousOn.comp_continuous continuous_subtype_val
    (fun z => d.sphere_subset_source z.property)).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.continuous_tripleBoundaryThird then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.continuous_tripleBoundaryThird"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.continuous_tripleBoundaryThird ``Submission.DifferentialGeometry.Topology.BallChart.continuous_tripleBoundaryThird

theorem tripleToFirst_boundaryFirst (z : S2) :
    tripleToFirst e c d (tripleBoundaryFirst e c d hec hed z) = e.boundaryMap z := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.tripleToFirst_boundaryFirst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.tripleToFirst_boundaryFirst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.tripleToFirst_boundaryFirst ``Submission.DifferentialGeometry.Topology.BallChart.tripleToFirst_boundaryFirst

theorem tripleToPair_boundarySecond (z : S2) :
    tripleToPair e c d (tripleBoundarySecond e c d hec hcd z) = c.firstBoundaryMap d hcd z := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.tripleToPair_boundarySecond then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.tripleToPair_boundarySecond"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.tripleToPair_boundarySecond ``Submission.DifferentialGeometry.Topology.BallChart.tripleToPair_boundarySecond

theorem tripleToPair_boundaryThird (z : S2) :
    tripleToPair e c d (tripleBoundaryThird e c d hed hcd z) = c.secondBoundaryMap d hcd z := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.tripleToPair_boundaryThird then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.tripleToPair_boundaryThird"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.tripleToPair_boundaryThird ``Submission.DifferentialGeometry.Topology.BallChart.tripleToPair_boundaryThird

end DifferentialGeometry.Topology.BallChart
