import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Algebra.Order.Group.Pointwise.Interval

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Pointwise

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

def componentTimeShift (c : ConnectedComponents P.Carrier) :
    SolutionOn (I := ThreeModel) (M := P.componentOpen c)
      (RealTimeInterval.closedOpen 0 (s - a) (sub_pos.mpr G.lt)) := by
  let : CompactSpace (P.componentOpen c) := P.component_compact c
  exact (solutionOnRestrictOpen (G.flow.timeShift a) (P.componentOpen c)).timeRestrict _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.componentTimeShift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.componentTimeShift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.componentTimeShift ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.componentTimeShift

theorem componentTimeShift_metric (c : ConnectedComponents P.Carrier) (t : ℝ) :
    (G.componentTimeShift c).base.metric t =
      (G.flow.base.metric (t + a)).restrictOpen (P.componentOpen c) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.componentTimeShift_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.componentTimeShift_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.componentTimeShift_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.componentTimeShift_metric

theorem componentTimeShift_scalar (c : ConnectedComponents P.Carrier)
    (t : ℝ) (x : P.componentOpen c) :
    (G.componentTimeShift c).scalar t x = G.flow.scalar (t + a) x.val := by
  let : CompactSpace (P.componentOpen c) := P.component_compact c
  exact scalar_restrictOpen (G.flow.timeShift a) (P.componentOpen c) t x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.componentTimeShift_scalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.componentTimeShift_scalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.componentTimeShift_scalar ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.componentTimeShift_scalar

theorem isSolutionOn_componentTimeShift (c : ConnectedComponents P.Carrier) :
    IsSolutionOn (G.componentTimeShift c) := by
  let : CompactSpace (P.componentOpen c) := P.component_compact c
  apply isSolutionOn_timeRestrict _
  · rw [RealTimeInterval.timeShift_closedOpen_carrier]
    exact Subset.rfl
  · rw [RealTimeInterval.timeShift_closedOpen_regular]
    exact Subset.rfl
  · exact isSolutionOn_restrictOpen _ (isSolutionOn_timeShift G.equation a) (P.componentOpen c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.isSolutionOn_componentTimeShift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.isSolutionOn_componentTimeShift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.isSolutionOn_componentTimeShift ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.isSolutionOn_componentTimeShift

theorem componentTimeShift_scalar_left_derivative (c : ConnectedComponents P.Carrier)
    (t : ℝ) (x : P.componentOpen c) :
    derivWithin (fun u => (G.componentTimeShift c).scalar u x) (_root_.Set.Iic t) t =
      derivWithin (fun u => G.flow.scalar u x.val) (_root_.Set.Iic (t + a)) (t + a) := by
  simp only [G.componentTimeShift_scalar]
  rw [derivWithin_comp_add_const (fun u => G.flow.scalar u x.val)]
  congr 1
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    change a + y ≤ t + a
    have hy' : y ≤ t := hy
    linarith
  · intro hz
    refine ⟨z - a, ?_, by simp⟩
    change z - a ≤ t
    change z ≤ t + a at hz
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.componentTimeShift_scalar_left_derivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.componentTimeShift_scalar_left_derivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.componentTimeShift_scalar_left_derivative ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.componentTimeShift_scalar_left_derivative

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
