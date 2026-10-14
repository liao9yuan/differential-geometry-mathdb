import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PoincareControl
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

structure PoincareControlledExtinction (M : ClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) where
  history : FiniteSurgeryHistory.{u}
  time : ℝ
  time_pos : 0 < time
  initial : history.InitialIdentification M g
  controlled : history.poincareControlled
  extinct : history.extinctAt time

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction

namespace PoincareControlledExtinction

variable {M : ClosedOrientedManifold.{u} 3} {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}
  (W : PoincareControlledExtinction M g)

theorem time_eq : W.time = W.history.terminalTime := W.extinct.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.time_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.time_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.time_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.time_eq

theorem terminal_isEmpty : IsEmpty (W.history.stage (Fin.last W.history.eventCount)).Carrier :=
  W.extinct.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.terminal_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.terminal_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.terminal_isEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.terminal_isEmpty

def initialCutCapIdentification : W.history.cutCapTrace.InitialIdentification M :=
  W.initial.cutCapIdentification

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.initialCutCapIdentification then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.initialCutCapIdentification"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.initialCutCapIdentification ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.initialCutCapIdentification

theorem initialCutCapIdentification_map :
    W.initialCutCapIdentification.1 = W.initial.diffeomorph := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.initialCutCapIdentification_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.initialCutCapIdentification_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.initialCutCapIdentification_map ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.initialCutCapIdentification_map

theorem initial_metric_eq (x : M.Carrier) (v w : TangentSpace (𝓡 3) x) :
    (W.history.initialMetric 0).inner (W.initial.diffeomorph x)
      (mfderiv (𝓡 3) (𝓡 3) W.initial.diffeomorph x v)
      (mfderiv (𝓡 3) (𝓡 3) W.initial.diffeomorph x w) = g.inner x v w :=
  W.initial.metric_eq x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.initial_metric_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.initial_metric_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.initial_metric_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.initial_metric_eq

theorem controlled_extinct_trace :
    W.history.cutCapTrace.poincareControlled ∧ W.history.cutCapTrace.extinct :=
  W.history.extinct_poincareControlled_trace W.controlled W.extinct

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.controlled_extinct_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.controlled_extinct_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.controlled_extinct_trace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.controlled_extinct_trace

end PoincareControlledExtinction

end DifferentialGeometry.PDE.RicciFlow.Surgery
