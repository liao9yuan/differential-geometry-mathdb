import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreOrientation
import Submission.DifferentialGeometry.Topology.Manifold.Attachment.RadialCollarOrientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment _root_.Submission.DifferentialGeometry.Geometry.Neck
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.E3 target :: scope.openDecls } }
private abbrev E2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.E2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.E2 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.S2 target :: scope.openDecls } }
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.IR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.IR target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.IC target :: scope.openDecls } }
private abbrev IH := ModelProd E2 (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.IH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.IH target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))

include hs in
theorem cuttingCollarMap_mfderiv_bijective (b : ι × Bool)
    (q : S2 × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :
    letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    Bijective (mfderiv IR IR (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b) q) := by
  let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  exact ((cuttingCollarMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b q).mfderivToContinuousLinearEquiv
    (by simp)).bijective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarMap_mfderiv_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarMap_mfderiv_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarMap_mfderiv_bijective ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarMap_mfderiv_bijective

def cuttingCollarSmoothOrientation (b : ι × Bool) (o : SmoothOrientation I M) :
    letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    letI := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
    SmoothOrientation IR (S2 × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) := by
  let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
  let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact pullbackSmoothOrientation IR IR
    (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b)
    (cuttingCollarMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b).contMDiff
    (cuttingCollarMap_mfderiv_bijective I hdim hδ f hf hdisj hs b)
    (cutCoreSmoothOrientation I hdim hδ f hf hdisj hs o)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarSmoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarSmoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarSmoothOrientation ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarSmoothOrientation

theorem cuttingCollarSmoothOrientation_apply (b : ι × Bool) (o : SmoothOrientation I M)
    (q : S2 × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :
    letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    letI := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
    let : ChartedSpace IH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : IsManifold IR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
    (cuttingCollarSmoothOrientation I hdim hδ f hf hdisj hs b o).val q =
      tangentOrientationEquiv (differentialEquivOfBijective IR IR
        (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b)
        (cuttingCollarMap_mfderiv_bijective I hdim hδ f hf hdisj hs b) q).symm.toLinearEquiv
          ((cutCoreSmoothOrientation I hdim hδ f hf hdisj hs o).val
            (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarSmoothOrientation_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarSmoothOrientation_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarSmoothOrientation_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollarSmoothOrientation_apply

theorem exists_radialOrientation_matching_cuttingCollar {L : ℝ} (hL : 0 < L)
    (b : ι × Bool) (o : SmoothOrientation I M) :
    letI := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    letI := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
    ∃ oE : Orientation ℝ E3 (Fin (Module.finrank ℝ E3)),
      (oE = (Module.finBasis ℝ E3).orientation ∨ oE = -(Module.finBasis ℝ E3).orientation) ∧
      ∀ q : S2 × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1)),
        (radialCollarSmoothOrientation hL (cuttingCollarWidth_pos (hδ b.1)) oE).val q =
          (cuttingCollarSmoothOrientation I hdim hδ f hf hdisj hs b o).val q := by
  let := halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let := halfClosedInterval_isManifold (cuttingCollarWidth_pos (hδ b.1))
  exact exists_radialCollarSmoothOrientation hL (cuttingCollarWidth_pos (hδ b.1))
    (cuttingCollarSmoothOrientation I hdim hδ f hf hdisj hs b o)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.exists_radialOrientation_matching_cuttingCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.exists_radialOrientation_matching_cuttingCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.exists_radialOrientation_matching_cuttingCollar ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.exists_radialOrientation_matching_cuttingCollar
end DifferentialGeometry.Topology.ThreeManifold.Surgery
