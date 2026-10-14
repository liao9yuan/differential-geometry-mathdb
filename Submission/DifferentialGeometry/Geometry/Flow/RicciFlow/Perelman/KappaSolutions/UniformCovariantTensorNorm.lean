import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.UniformTensorNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private local instance uniformCovTensorC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniformCovTensorC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniformCovTensorC1 target :: scope.openDecls } }


omit [BoundarylessManifold I M] in
theorem uniform_tensor02_covariant_norm_on_compact_closedWindow {D : RealTimeInterval}
    (L : SolutionOn (I := I) (M := M) D) (hL : IsSolutionOn L)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : _root_.Set.Icc a b ⊆ D.carrier) (hregular : _root_.Set.Ioo a b ⊆ D.regular)
    {J : Set ℝ} (hJ : IsCompact J) (hJb : J ⊆ _root_.Set.Icc c b)
    (A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2) (p : M)
    {U : Set E} (hU : IsOpen U) (hUt : U ⊆ (extChartAt I p).target)
    (hcoord : ∀ slots : Fin 2 → CoordinateIdx (𝕜 := ℝ) E,
      ∀ K : Set E, IsCompact K → K ⊆ U → ∀ r : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ r (fun z => A n t ((extChartAt I p).symm z)
          (fun j => chartBasisVecFiber (I := I) p (slots j) ((extChartAt I p).symm z))) y‖ ≤ ε)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (r : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ J, ∀ y ∈ K,
      tensor02CovDerivNormWith (I := I) r (A n t) (L.base.metric t) (L.base.metric t)
        ((extChartAt I p).symm y) ≤ ε := by
  exact uniform_tensor02_covariant_norm_on_compact_time_of_closed_interval
    L hL hac hcb hslab hregular hJ hJb A p hU hUt hcoord hK hKU r

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_tensor02_covariant_norm_on_compact_closedWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_tensor02_covariant_norm_on_compact_closedWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_tensor02_covariant_norm_on_compact_closedWindow ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.uniform_tensor02_covariant_norm_on_compact_closedWindow

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
