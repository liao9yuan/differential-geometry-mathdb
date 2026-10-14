import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandard
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteHistory

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

namespace FiniteSurgeryHistory

def poincareControlled (H : FiniteSurgeryHistory.{u}) : Prop := H.cutCapTrace.poincareControlled

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.poincareControlled then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.poincareControlled"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.poincareControlled ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.poincareControlled

theorem poincareControlled_iff (H : FiniteSurgeryHistory.{u}) :
    H.poincareControlled ↔ H.controlledBy Topology.componentIsPoincareStandard := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.poincareControlled_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.poincareControlled_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.poincareControlled_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.poincareControlled_iff

theorem discarded_poincareStandard (H : FiniteSurgeryHistory.{u}) (h : H.poincareControlled)
    (i : Fin H.eventCount) (C : ConnectedComponents (H.event i).transition.discarded.Carrier) :
    Topology.isPoincareStandard ((H.event i).transition.discarded.component C).Carrier := h i C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.discarded_poincareStandard then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.discarded_poincareStandard"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.discarded_poincareStandard ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.discarded_poincareStandard

theorem extinct_poincareControlled_trace (H : FiniteSurgeryHistory.{u})
    (h : H.poincareControlled) {T : ℝ} (hext : H.extinctAt T) :
    H.cutCapTrace.poincareControlled ∧ H.cutCapTrace.extinct := ⟨h, H.extinct_trace hext⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.extinct_poincareControlled_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.extinct_poincareControlled_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.extinct_poincareControlled_trace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.extinct_poincareControlled_trace

end FiniteSurgeryHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery
