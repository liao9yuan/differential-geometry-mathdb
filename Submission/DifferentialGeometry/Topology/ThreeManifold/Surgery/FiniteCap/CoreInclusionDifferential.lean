import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCoreSmoothEmbedding
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapBallSmooth
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionDifferential

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev CoreDerE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreDerE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreDerE3 target :: scope.openDecls } }
private abbrev CoreDerE2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreDerE2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreDerE2 target :: scope.openDecls } }
private abbrev CoreDerIR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreDerIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreDerIR target :: scope.openDecls } }
private abbrev CoreDerIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreDerIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreDerIC target :: scope.openDecls } }
private abbrev CoreDerIH := ModelProd CoreDerE2 (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreDerIH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreDerIH target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph CoreDerIC I ∞ (f i))
local notation "CoreDerQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

include hs in
theorem cutCore_ambientInclusion_mfderiv_bijective (p : cutCore f) :
    let : ChartedSpace CoreDerIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    Bijective (mfderiv CoreDerIR I (Subtype.val : cutCore f → M) p) := by
  let : ChartedSpace CoreDerIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  exact bijective_mfderiv_of_isImmersionAt CoreDerIR I _ p
    ((cutCore_ambientInclusion_isSmoothEmbedding I hdim hδ f hf hdisj hs).isImmersion.isImmersionAt p)
    (by simpa using hdim.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_ambientInclusion_mfderiv_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_ambientInclusion_mfderiv_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_ambientInclusion_mfderiv_bijective ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_ambientInclusion_mfderiv_bijective

include hs in
theorem finiteCoreInclusion_mfderiv_bijective (p : cutCore f) :
    let : ChartedSpace CoreDerIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : ChartedSpace CoreDerE3 CoreDerQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Bijective (mfderiv CoreDerIR (𝓡 3) (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj) p) := by
  let : ChartedSpace CoreDerIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : ChartedSpace CoreDerE3 CoreDerQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact bijective_mfderiv_of_isImmersionAt CoreDerIR (𝓡 3) _ p
    ((finiteCoreInclusion_isSmoothEmbedding I hdim hL hδ f hf hdisj hs).isImmersion.isImmersionAt p) (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInclusion_mfderiv_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInclusion_mfderiv_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInclusion_mfderiv_bijective ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInclusion_mfderiv_bijective

include hs in
theorem finiteCapInclusion_ball_mfderiv_bijective (b : ι × Bool)
    (x : {x : CoreDerE3 // ‖x‖ ≤ L}) :
    let : ChartedSpace (EuclideanHalfSpace 3) {x : CoreDerE3 // ‖x‖ ≤ L} := closedBallChartedSpace hL
    let : ChartedSpace CoreDerE3 CoreDerQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    _root_.Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      (fun y : {x : CoreDerE3 // ‖x‖ ≤ L} => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩) x) := by
  let : ChartedSpace (EuclideanHalfSpace 3) {x : CoreDerE3 // ‖x‖ ≤ L} := closedBallChartedSpace hL
  let : ChartedSpace CoreDerE3 CoreDerQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact bijective_mfderiv_of_isImmersionAt (𝓡∂ 3) (𝓡 3) _ x
    ((finiteCapInclusion_ball_isSmoothEmbedding I hdim hL hδ f hf hdisj hs b).isImmersion.isImmersionAt x) rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapInclusion_ball_mfderiv_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapInclusion_ball_mfderiv_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapInclusion_ball_mfderiv_bijective ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapInclusion_ball_mfderiv_bijective
end DifferentialGeometry.Topology.ThreeManifold.Surgery
