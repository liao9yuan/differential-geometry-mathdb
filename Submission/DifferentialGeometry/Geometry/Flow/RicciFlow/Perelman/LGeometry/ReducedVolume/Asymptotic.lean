import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Measure
import Mathlib.Topology.Order.MonotoneConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.ContDiff _root_.ENNReal _root_.Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}

def asymptoticReducedVolume (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (p : M) : ℝ≥0∞ :=
  ⨅ tau : Set.Ioi (0 : ℝ), redVolume S T p tau

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.asymptoticReducedVolume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.asymptoticReducedVolume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.asymptoticReducedVolume ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.asymptoticReducedVolume

theorem asymptoticReducedVolume_le_redVolume
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (p : M) {tau : ℝ} (htau : 0 < tau) :
    asymptoticReducedVolume S T p ≤ redVolume S T p tau :=
  iInf_le (fun r : Set.Ioi (0 : ℝ) => redVolume S T p r) ⟨tau, htau⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.asymptoticReducedVolume_le_redVolume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.asymptoticReducedVolume_le_redVolume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.asymptoticReducedVolume_le_redVolume ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.asymptoticReducedVolume_le_redVolume

theorem redVolume_tendsto_atTop_of_antitone
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (p : M)
    (hmono : AntitoneOn (redVolume S T p) (_root_.Set.Ioi 0)) :
    Tendsto (redVolume S T p) _root_.Filter.atTop (𝓝 (asymptoticReducedVolume S T p)) := by
  apply tendsto_comp_val_Ioi_atTop.mp
  exact tendsto_atTop_iInf (fun a b hab => hmono a.property b.property hab)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_tendsto_atTop_of_antitone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_tendsto_atTop_of_antitone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_tendsto_atTop_of_antitone ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_tendsto_atTop_of_antitone

end DifferentialGeometry.PDE.RicciFlow.Perelman
