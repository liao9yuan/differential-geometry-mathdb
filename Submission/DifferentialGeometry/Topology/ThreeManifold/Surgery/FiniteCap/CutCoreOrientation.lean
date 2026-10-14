import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationPullback
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CoreInclusionDifferential

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
private abbrev CoreE2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreE2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreE2 target :: scope.openDecls } }
private abbrev CoreIR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreIR target :: scope.openDecls } }
private abbrev CoreIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreIC target :: scope.openDecls } }
private abbrev CoreIH := ModelProd CoreE2 (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreIH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreIH target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph CoreIC I ∞ (f i))

def cutCoreSmoothOrientation (o : SmoothOrientation I M) :
    let : ChartedSpace CoreIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold CoreIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    SmoothOrientation CoreIR (cutCore f) := by
  let : ChartedSpace CoreIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold CoreIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact pullbackSmoothOrientation CoreIR I (Subtype.val : cutCore f → M)
    (cutCore_ambientInclusion_isSmoothEmbedding I hdim hδ f hf hdisj hs).contMDiff
    (cutCore_ambientInclusion_mfderiv_bijective I hdim hδ f hf hdisj hs) o

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreSmoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreSmoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreSmoothOrientation ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreSmoothOrientation

theorem cutCoreSmoothOrientation_pushforward (o : SmoothOrientation I M) (p : cutCore f) :
    let : ChartedSpace CoreIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold CoreIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    tangentOrientationEquiv (differentialEquivOfBijective CoreIR I (Subtype.val : cutCore f → M)
      (cutCore_ambientInclusion_mfderiv_bijective I hdim hδ f hf hdisj hs) p).toLinearEquiv
        ((cutCoreSmoothOrientation I hdim hδ f hf hdisj hs o).val p) = o.val p.val := by
  let : ChartedSpace CoreIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold CoreIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact tangentOrientationEquiv_symm
    (differentialEquivOfBijective CoreIR I (Subtype.val : cutCore f → M)
      (cutCore_ambientInclusion_mfderiv_bijective I hdim hδ f hf hdisj hs) p).symm.toLinearEquiv
    (o.val p.val)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreSmoothOrientation_pushforward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreSmoothOrientation_pushforward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreSmoothOrientation_pushforward ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCoreSmoothOrientation_pushforward
end DifferentialGeometry.Topology.ThreeManifold.Surgery
