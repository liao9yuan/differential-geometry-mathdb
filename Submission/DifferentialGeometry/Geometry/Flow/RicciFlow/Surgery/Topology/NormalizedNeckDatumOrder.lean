import Submission.DifferentialGeometry.Geometry.Neck.OrderReduction
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.SphericalCutCore
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NormalizedNeckDatum
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoffRemainingFields

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck

universe u v

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.instFactEqNatFinrankRealThreeSpaceOfNat : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.instFactEqNatFinrankRealThreeSpaceOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.instFactEqNatFinrankRealThreeSpaceOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.instFactEqNatFinrankRealThreeSpaceHAddOfNat : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.instFactEqNatFinrankRealThreeSpaceHAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.instFactEqNatFinrankRealThreeSpaceHAddOfNat target :: scope.openDecls } }

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
  (U : Opens M) [SigmaCompactSpace U] {g : SmoothRiemannianMetric ThreeModel U}
  {ι : Type v} {δ₀ : ι → ℝ} {k : ι → ℕ}

theorem lowerOrder_oriented_rotatedDatum_family
    (N : ∀ i, NormalizedNeck g (δ₀ i) (k i))
    {δ : ℝ} (hδ : ∀ i, δ₀ i ≤ δ) (hδ1 : δ < 1)
    (e : ι → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    (he : ∀ i, sphereDiffeo (n := 2) (e i) spherePoint = (N i).sphereMark)
    (side : ι → Bool) {m : ℕ} (hm : ∀ i, m ≤ k i)
    {Q : ℝ} (hQ : ∀ i, (N i).scale = Q) :
    let d := fun i => (((N i).monoDelta (hδ i) hδ1).rotatedDatum (e i) (he i) (side i)).oriented
    let d₀ : ∀ i, normalizedDatum g (N i).center δ m := fun i => (d i).lowerOrder (hm i)
    (∀ i, (d₀ i).map = (d i).map) ∧
    (∀ i, (d₀ i).retainedSide = _root_.Bool.true) ∧
    (∀ i, metricScalarAt g (N i).center = Q) ∧
    (∀ i (σ : ℝ) (hσ : σ ^ 2 = 1), (d₀ i).offsetPoint hσ = (d i).offsetPoint hσ) ∧
    (∀ i, neckAmbientMap U (d₀ i) = neckAmbientMap U (d i)) ∧
    ∀ i, IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (neckAmbientMap U (d₀ i)) := by
  dsimp only
  refine ⟨fun _ => rfl,fun _ => rfl,?_,fun _ _ _ => rfl,fun _ => rfl,?_⟩
  · intro i
    exact (N i).scale_scalar.symm.trans (hQ i)
  · intro i
    exact isLocalDiffeomorph_neckAmbientMap U _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.lowerOrder_oriented_rotatedDatum_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.lowerOrder_oriented_rotatedDatum_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.lowerOrder_oriented_rotatedDatum_family ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.lowerOrder_oriented_rotatedDatum_family

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck
