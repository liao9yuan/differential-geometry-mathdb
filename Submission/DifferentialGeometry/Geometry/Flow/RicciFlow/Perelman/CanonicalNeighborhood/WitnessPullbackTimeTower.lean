import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ClosedWindowMetricFields
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PartialTensorPullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

private local instance pullbackTimeSourceC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.pullbackTimeSourceC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.pullbackTimeSourceC1 target :: scope.openDecls } }
private local instance pullbackTimeTargetC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.pullbackTimeTargetC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.pullbackTimeTargetC1 target :: scope.openDecls } }

omit [T2Space M] in
theorem exists_partial_pullback_time_tower
    (Phi : PartialDiffeomorph I I N M ∞)
    (A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (chi : N → ℝ) (hchi : ContMDiff I 𝓘(ℝ) ∞ chi)
    (hsupp : tsupport chi ⊆ Phi.source) (J : Set ℝ)
    (hA : ∀ q t, t ∈ J → ∀ x : M,
      HasDerivWithinAt (fun s => A q s x) (A (q + 1) t x) J t) :
    ∃ B : ℕ → ℝ → Tensor0SField (I := I) (M := N) (n := ∞) 2,
      (∀ q t, ∀ y ∈ Phi.source, ∀ v : Fin 2 → TangentSpace I y,
        B q t y v = chi y * A q t (Phi y) (fun j => mfderiv I I Phi y (v j))) ∧
      (∀ q t, ∀ y : N, y ∉ Phi.source → B q t y = 0) ∧
      ∀ q t, t ∈ J → ∀ y : N,
        HasDerivWithinAt (fun s => B q s y) (B (q + 1) t y) J t := by
  exact DifferentialGeometry.exists_partial_pullback_tensor_time_tower Phi
    ⟨Phi.source, Phi.open_source⟩ Subset.rfl A chi hchi hsupp J
    (fun q t ht x _hx => hA q t ht x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_partial_pullback_time_tower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_partial_pullback_time_tower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_partial_pullback_time_tower ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_partial_pullback_time_tower


theorem exists_closedWindow_pullback_metric_time_tower
    [I.Boundaryless] [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)]
    [BoundarylessManifold I M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : _root_.Set.Icc a b ⊆ D.carrier) (hreg : _root_.Set.Ioo a b ⊆ D.regular)
    (Phi : PartialDiffeomorph I I N M ∞)
    (chi : N → ℝ) (hchi : ContMDiff I 𝓘(ℝ) ∞ chi)
    (hsupp : tsupport chi ⊆ Phi.source) :
    ∃ B : ℕ → ℝ → Tensor0SField (I := I) (M := N) (n := ∞) 2,
      (∀ t, ∀ y ∈ Phi.source, ∀ v : Fin 2 → TangentSpace I y,
        B 0 t y v = chi y * (S.base.metric t).inner (Phi y)
          (mfderiv I I Phi y (v 0)) (mfderiv I I Phi y (v 1))) ∧
      (∀ q t, ∀ y : N, y ∉ Phi.source → B q t y = 0) ∧
      ∀ q t, t ∈ _root_.Set.Icc c b → ∀ y : N,
        HasDerivWithinAt (fun s => B q s y) (B (q + 1) t y) (_root_.Set.Icc c b) t := by
  obtain ⟨A, hzero, hA⟩ := exists_closedWindow_metric_time_fields S hS hac hcb hslab hreg
  obtain ⟨B, hvalue, hout, hderiv⟩ := exists_partial_pullback_time_tower Phi A chi hchi hsupp
    (_root_.Set.Icc c b) (fun q t ht x => (hA q t ht x).2)
  refine ⟨B, ?_, hout, hderiv⟩
  intro t y hy v
  rw [hvalue 0 t y hy v, hzero t, metricTensorField_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_closedWindow_pullback_metric_time_tower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_closedWindow_pullback_metric_time_tower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_closedWindow_pullback_metric_time_tower ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_closedWindow_pullback_metric_time_tower

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
