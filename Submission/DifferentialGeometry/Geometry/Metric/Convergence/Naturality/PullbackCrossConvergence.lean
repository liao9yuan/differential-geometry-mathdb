import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N]

private local instance crossMetricConvergenceSourceC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossMetricConvergenceSourceC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossMetricConvergenceSourceC1 target :: scope.openDecls } }

private local instance crossMetricConvergenceSourceC2 : IsManifold I 2 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossMetricConvergenceSourceC2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossMetricConvergenceSourceC2 target :: scope.openDecls } }

private local instance crossMetricConvergenceSourceTop :
    IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  simpa using (inferInstance : IsManifold I ∞ M)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossMetricConvergenceSourceTop
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossMetricConvergenceSourceTop target :: scope.openDecls } }

private local instance crossMetricConvergenceTargetC1 : IsManifold J 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossMetricConvergenceTargetC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossMetricConvergenceTargetC1 target :: scope.openDecls } }

private local instance crossMetricConvergenceTargetC2 : IsManifold J 2 N :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossMetricConvergenceTargetC2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossMetricConvergenceTargetC2 target :: scope.openDecls } }

private local instance crossMetricConvergenceTargetTop :
    IsManifold J ((∞ : WithTop ℕ∞) + 1) N := by
  simpa using (inferInstance : IsManifold J ∞ N)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossMetricConvergenceTargetTop
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.crossMetricConvergenceTargetTop target :: scope.openDecls } }

theorem metricDerivNormSupOn_pullbackCross_image
    (K : Set M) (p : ℕ) (gk gInf gRef : SmoothRiemannianMetric J N)
    (Phi : M ≃ₘ⟮I, J⟯ N) :
    metricDerivNormSupOn (I := I) K p
        (Diffeomorph.pullbackMetricCross gk Phi)
        (Diffeomorph.pullbackMetricCross gInf Phi)
        (Diffeomorph.pullbackMetricCross gRef Phi) =
      metricDerivNormSupOn (I := J) (Phi '' K) p gk gInf gRef := by
  unfold metricDerivNormSupOn
  apply congrArg _root_.SupSet.sSup
  ext r
  constructor
  · rintro ⟨a, ha, x, hx, hr⟩
    refine ⟨a, ha, Phi x, ⟨x, hx, rfl⟩, ?_⟩
    rw [← hr]
    exact (metricDerivNorm_pullbackCross (I := I) (J := J)
      gk gInf gRef Phi a x).symm
  · rintro ⟨a, ha, y, ⟨x, hx, rfl⟩, hr⟩
    refine ⟨a, ha, x, hx, ?_⟩
    rw [metricDerivNorm_pullbackCross (I := I) (J := J)]
    exact hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricDerivNormSupOn_pullbackCross_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricDerivNormSupOn_pullbackCross_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricDerivNormSupOn_pullbackCross_image ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricDerivNormSupOn_pullbackCross_image

theorem metricCPConvOn_pullbackCross
    (K : Set M) (p : ℕ) (gSeq : ℕ → SmoothRiemannianMetric J N)
    (gInf gRef : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (hconv : MetricCPConvergenceOn (I := J) (Phi '' K) p gSeq gInf gRef) :
    MetricCPConvergenceOn (I := I) K p
      (fun k => Diffeomorph.pullbackMetricCross (gSeq k) Phi)
      (Diffeomorph.pullbackMetricCross gInf Phi)
      (Diffeomorph.pullbackMetricCross gRef Phi) := by
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := hconv ε hε
  refine ⟨k₀, fun k hk => ?_⟩
  rw [metricDerivNormSupOn_pullbackCross_image]
  exact hk₀ k hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricCPConvOn_pullbackCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricCPConvOn_pullbackCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricCPConvOn_pullbackCross ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricCPConvOn_pullbackCross

theorem metricCInfConvOnCompacts_pullbackCross
    (gSeq : ℕ → SmoothRiemannianMetric J N)
    (gInf gRef : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (hconv : MetricCInfConvergenceOnCompacts (I := J) gSeq gInf gRef) :
    MetricCInfConvergenceOnCompacts (I := I)
      (fun k => Diffeomorph.pullbackMetricCross (gSeq k) Phi)
      (Diffeomorph.pullbackMetricCross gInf Phi)
      (Diffeomorph.pullbackMetricCross gRef Phi) := by
  intro K hK p
  exact metricCPConvOn_pullbackCross K p gSeq gInf gRef Phi
    (hconv (Phi '' K) (hK.image Phi.continuous) p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricCInfConvOnCompacts_pullbackCross then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricCInfConvOnCompacts_pullbackCross"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricCInfConvOnCompacts_pullbackCross ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricCInfConvOnCompacts_pullbackCross

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
