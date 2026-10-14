import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Restriction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Solution
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.Complete

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow (IsSolutionOn curvatureOperator_nonnegative_of_complete_ancient)
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Soliton
  (canonicalTimeDomain canonicalSolutionOn canonicalSolutionOn_metric_zero
    canonicalSolutionOn_isSolutionOn canonicalSolutionOn_complete)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

private theorem gradientRicciSoliton_curvatureOperator_nonnegative_of_connected
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) {σ : ℝ} (hσ : 0 ≤ σ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (hdim : Module.finrank ℝ E = 3) (x : M) :
    metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
  let D := RealTimeInterval.infiniteClosed 0 0 le_rfl
  have hD : D.carrier ⊆ canonicalTimeDomain σ := by
    intro t ht
    change 0 < 1 - σ * t
    have hmul : σ * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hσ ht
    linarith only [hmul]
  let S := canonicalSolutionOn (I := I) g f σ hcomplete hsol D
  have hS : IsSolutionOn S := canonicalSolutionOn_isSolutionOn g f σ hcomplete hsol D hD
  have hcompleteS : ∀ t ∈ _root_.Set.Iic 0, RiemannianMetricComplete (I := I) (S.base.metric t) :=
    fun t ht => canonicalSolutionOn_complete g f σ hcomplete hsol D hD ht
  have hcone := curvatureOperator_nonnegative_of_complete_ancient S hS
    (fun _ h => h) (fun _ h => h) hcompleteS hdim x
  change metricAlgebraicCurvatureTensorAt (I := I) (M := M) (S.base.metric 0) x ∈ _ at hcone
  simpa only [S, canonicalSolutionOn_metric_zero] using hcone

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperator_nonnegative_of_connected
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperator_nonnegative_of_connected target :: scope.openDecls } }

theorem gradientRicciSoliton_curvatureOperator_nonnegative
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) {σ : ℝ} (hσ : 0 ≤ σ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (hdim : Module.finrank ℝ E = 3) (x : M) :
    metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
  let : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  let U : TopologicalSpace.Opens M := ⟨connectedComponent x, isOpen_connectedComponent⟩
  let : SigmaCompactSpace U := isClosed_connectedComponent.sigmaCompactSpace
  let : ConnectedSpace U := Subtype.connectedSpace isConnected_connectedComponent
  let φ : U → M := Subtype.val
  let hφ : IsLocalDiffeomorph I I ∞ φ := isLocalDiffeomorph_subtype_val U
  let gU := localPullMetric g φ hφ
  let fU : C^∞⟮I, U; ℝ⟯ := ⟨fun y => f y.1,
    f.contMDiff.comp (contMDiff_subtype_val (I := I) (U := U))⟩
  have hgU : gU = g.restrictOpen U := localPullMetric_subtype_val g U
  have hcompleteU : RiemannianMetricComplete (I := I) gU := by
    rw [hgU]
    exact RiemannianMetricComplete.restrictOpen_of_isClosed g hcomplete U isClosed_connectedComponent
  have hsolU : gradientRicciSoliton (I := I) gU fU σ := by
    intro y v w
    change ricciTensor (localPullMetric g φ hφ) y v w +
      hessFun (localPullMetric g φ hφ) (f ∘ φ) y v w = _
    rw [ricciTensor_localPull, hessFun_localPull, localPullMetric_inner]
    exact hsol (φ y) _ _
  have hxU : x ∈ U := mem_connectedComponent
  have hnonneg := gradientRicciSoliton_curvatureOperator_nonnegative_of_connected
    gU fU hσ hcompleteU hsolU hdim ⟨x, hxU⟩
  rw [hgU] at hnonneg
  exact (metricAlgebraicCurvatureTensorAt_restrictOpen_mem_curvatureOperatorNonnegativeCone_iff
    g U ⟨x, hxU⟩).mp hnonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperator_nonnegative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperator_nonnegative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperator_nonnegative ``Submission.DifferentialGeometry.Geometry.gradientRicciSoliton_curvatureOperator_nonnegative

end DifferentialGeometry.Geometry

end
