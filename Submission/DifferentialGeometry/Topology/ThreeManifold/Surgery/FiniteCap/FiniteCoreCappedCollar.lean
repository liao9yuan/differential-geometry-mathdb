import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionLiftSource
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionEqualDimension
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreCollarLocalDiffeomorph
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapNeighborhoodSmooth
import Submission.DifferentialGeometry.Topology.Manifold.Attachment.RadialEmbedding

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev CappedCollarE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CappedCollarE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CappedCollarE3 target :: scope.openDecls } }
private abbrev CappedCollarE2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CappedCollarE2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CappedCollarE2 target :: scope.openDecls } }
private abbrev CappedCollarS2 := Metric.sphere (0 : CappedCollarE3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CappedCollarS2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CappedCollarS2 target :: scope.openDecls } }
private abbrev CappedCollarIR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CappedCollarIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CappedCollarIR target :: scope.openDecls } }
private abbrev CappedCollarIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CappedCollarIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CappedCollarIC target :: scope.openDecls } }
private abbrev CappedCollarIH := ModelProd CappedCollarE2 (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CappedCollarIH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CappedCollarIH target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealCappedCollarE3HAddOfNat : Fact (Module.finrank ℝ CappedCollarE3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealCappedCollarE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealCappedCollarE3HAddOfNat target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph CappedCollarIC I ∞ (f i))
local notation "CoreCappedQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

include hs in
theorem finiteCoreInclusion_collar_isSmoothEmbedding (b : ι × Bool) :
    let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
      halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
    let : ChartedSpace CappedCollarE3 CoreCappedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    _root_.Manifold.IsSmoothEmbedding CappedCollarIR (𝓡 3) ∞
      (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj ∘
        cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b) := by
  let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
    halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let : ChartedSpace CappedCollarE3 CoreCappedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ CoreCappedQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let N := finiteCapNeighborhoodOpens hL hδ f hf hdisj b
  let D := finiteCapNeighborhoodDiffeomorph I hdim hL hδ f hf hdisj hs b
  let ρ := retainedRadialMap (B := cuttingCollarWidth (precision b.1)) hL
  have hρ : _root_.Manifold.IsSmoothEmbedding CappedCollarIR (𝓡 3) ∞ ρ :=
    isSmoothEmbedding_retainedRadialMap hL (cuttingCollarWidth_pos (hδ b.1))
  have hN : _root_.Manifold.IsSmoothEmbedding CappedCollarIR (𝓡 3) ∞ (D.symm ∘ ρ) :=
    isSmoothEmbedding_diffeomorph_comp CappedCollarIR (𝓡 3) ρ hρ D.symm
  have hQ : _root_.Manifold.IsSmoothEmbedding CappedCollarIR (𝓡 3) ∞ (Subtype.val ∘ (D.symm ∘ ρ)) :=
    isSmoothEmbedding_fromOpen CappedCollarIR (𝓡 3) N (D.symm ∘ ρ) hN
  have heq : Subtype.val ∘ (D.symm ∘ ρ) =
      finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj ∘
        cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b := by
    funext q
    let p : N := ⟨finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
      (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q), Or.inr ⟨q, rfl⟩⟩
    have hp : D p = ρ q := by
      apply Subtype.ext
      exact finiteCapNeighborhoodHomeomorph_collar hL hδ f hf hdisj b q
    change (D.symm (ρ q)).val = p.val
    rw [← hp, D.symm_apply_apply]
  exact heq ▸ hQ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInclusion_collar_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInclusion_collar_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInclusion_collar_isSmoothEmbedding ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInclusion_collar_isSmoothEmbedding

include hs in
theorem finiteCoreInclusion_isImmersionAt_collar (b : ι × Bool)
    (q : CappedCollarS2 × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :
    let : ChartedSpace CappedCollarIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
    let : ChartedSpace CappedCollarE3 CoreCappedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    _root_.Manifold.IsImmersionAtOfComplement Unit CappedCollarIR (𝓡 3) ∞
      (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj)
      (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q) := by
  let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) :=
    halfClosedIntervalChartedSpace (cuttingCollarWidth_pos (hδ b.1))
  let : ChartedSpace CappedCollarIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold CappedCollarIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  let : ChartedSpace CappedCollarE3 CoreCappedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  have h := (finiteCoreInclusion_collar_isSmoothEmbedding I hdim hL hδ f hf hdisj hs b).isImmersion.isImmersionAt q
  have hUnit := isImmersionAtOfComplement_unit_of_equalDimension CappedCollarIR (𝓡 3) _ q h (by simp)
  exact isImmersionAtOfComplement_lift_source CappedCollarIR (𝓡 3) _
    (isOpenEmbedding_cuttingCollarMap hδ f hf hdisj b)
    (cuttingCollarMap_isLocalDiffeomorph I hdim hδ f hf hdisj hs b) _ q hUnit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInclusion_isImmersionAt_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInclusion_isImmersionAt_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInclusion_isImmersionAt_collar ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInclusion_isImmersionAt_collar
end DifferentialGeometry.Topology.ThreeManifold.Surgery
