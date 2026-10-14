import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ConnectedNoncollapse
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ComponentBallTransfer
import Submission.DifferentialGeometry.Geometry.Metric.ConnectedComponentInjectivity
import Submission.DifferentialGeometry.Bundle.FiberBundleHausdorff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.Geometry.Metric
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E F M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace F] {I : ModelWithCorners ℝ E F} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace F M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem fixed_terminal_ball_noncollapsed_complete
    (H K c : ℝ) (hH : 0 < H) (hK : 0 < K) (hc : 0 < c)
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (time : RealTimeInterval.FlowTime D) (hT : 0 < (time : ℝ)) (hTH : (time : ℝ) ≤ H)
    (hnonneg : D.carrier ⊆ _root_.Set.Ici (0 : ℝ))
    (hcarrier : _root_.Set.Icc (0 : ℝ) (time : ℝ) ⊆ D.carrier)
    (hregular : _root_.Set.Ioc (0 : ℝ) (time : ℝ) ⊆ D.regular)
    (hcomplete : ∀ t ∈ _root_.Set.Icc (0 : ℝ) (time : ℝ),
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hbounded : ∃ Q : ℝ, ∀ t ∈ _root_.Set.Icc (0 : ℝ) (time : ℝ), ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ Q)
    (hinit : ∀ z : M,
      Real.sqrt (normSq0S (I := I) (S.base.metric 0) z 4 (S.base.rm04 0 z)) ≤ K)
    (hInj : ∀ p : M, ENNReal.ofReal c ≤
      intrinsicInjectivityRadiusOf (I := I) (S.base.metric 0)
        (hcomplete 0 ⟨le_rfl, hT.le⟩) p)
    (B : FlowMetricBall S time)
    (hballSlab : _root_.Set.Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ) ⊆ D.carrier)
    (hRm : ∀ t ∈ _root_.Set.Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ), ∀ z ∈ B.set,
      B.radius ^ 4 * FlowMetricBall.rmNormSq S t z ≤ 1) :
    B.IsKappaNoncollapsed
      (boundedGeometryNoncollapseCoeff (Module.finrank ℝ E) H K c) := by
  let C := connectedComponentOpen (I := I) B.center
  let : SigmaCompactSpace C :=
    (isClosed_connectedComponent (x := B.center)).sigmaCompactSpace
  let : ConnectedSpace C := connectedComponentOpen_connectedSpace (I := I) B.center
  let : T2Space (TangentBundle I C) := inferInstance
  let SC : SolutionOn (I := I) (M := C) D := solutionOnRestrictOpen (I := I) S C
  let BC : FlowMetricBall SC time := FlowMetricBall.onConnectedComponent B
  have hSC : IsSolutionOn SC := isSolutionOn_restrict_connCompOpen S hS B.center
  have hcompleteC : ∀ t ∈ _root_.Set.Icc (0 : ℝ) (time : ℝ),
      RiemannianMetricComplete (I := I) (SC.base.metric t) := by
    intro t ht
    exact riemannianMetricComplete_restrictOpen_connCompOpen
      (I := I) (S.base.metric t) B.center (hcomplete t ht)
  have hnormC (t : ℝ) (x : C) :
      FlowMetricBall.rmNormSq SC t x = FlowMetricBall.rmNormSq S t (x : M) :=
    rmNormSq_restrict_connCompOpen S B.center t x
  have hboundedC : ∃ Q : ℝ, ∀ t ∈ _root_.Set.Icc (0 : ℝ) (time : ℝ), ∀ z : C,
      normSq0S (I := I) (SC.base.metric t) z 4 (SC.base.rm04 t z) ≤ Q := by
    obtain ⟨Q, hQ⟩ := hbounded
    refine ⟨Q, ?_⟩
    intro t ht z
    change FlowMetricBall.rmNormSq SC t z ≤ Q
    rw [hnormC]
    exact hQ t ht (z : M)
  have hinitC : ∀ z : C,
      Real.sqrt (normSq0S (I := I) (SC.base.metric 0) z 4 (SC.base.rm04 0 z)) ≤ K := by
    intro z
    change Real.sqrt (FlowMetricBall.rmNormSq SC 0 z) ≤ K
    rw [hnormC]
    exact hinit (z : M)
  have hInjC : ∀ p : C, ENNReal.ofReal c ≤
      intrinsicInjectivityRadiusOf (I := I) (SC.base.metric 0)
        (hcompleteC 0 ⟨le_rfl, hT.le⟩) p := by
    intro p
    exact (hInj (p : M)).trans
      (intrinsicInjectivityRadiusOf_le_restrictOpen_connCompOpen (I := I)
        (S.base.metric 0) (hcomplete 0 ⟨le_rfl, hT.le⟩) B.center p)
  obtain ⟨hballSlabC, hRmC⟩ :=
    FlowMetricBall.fixed_terminal_rm_control_onConnectedComponent B hballSlab hRm
  have hBC : BC.IsKappaNoncollapsed
      (boundedGeometryNoncollapseCoeff (Module.finrank ℝ E) H K c) :=
    fixed_terminal_ball_noncollapsed_connected H K c hH hK hc SC hSC time hT hTH
      hnonneg hcarrier hregular hcompleteC hboundedC hinitC hInjC BC hballSlabC hRmC
  exact (FlowMetricBall.onConnectedComponent_noncollapsed_iff B
    (boundedGeometryNoncollapseCoeff (Module.finrank ℝ E) H K c)).mp hBC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.fixed_terminal_ball_noncollapsed_complete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.fixed_terminal_ball_noncollapsed_complete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.fixed_terminal_ball_noncollapsed_complete ``Submission.DifferentialGeometry.PDE.RicciFlow.fixed_terminal_ball_noncollapsed_complete

end DifferentialGeometry.PDE.RicciFlow

end
