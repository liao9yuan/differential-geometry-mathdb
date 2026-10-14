import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientPullback
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NonnegativeCurvatureScalarNorm
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorNormFinrankNeZero
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Minimum.DimensionBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Naturality
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Submission.DifferentialGeometry.Topology.Manifold.ModelWithCorners

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance centerTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.centerTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.centerTopology target :: scope.openDecls } }
private local instance centerCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.centerCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.centerCharted target :: scope.openDecls } }
private local instance centerSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.centerSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.centerSmooth target :: scope.openDecls } }
private local instance centerT2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.centerT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.centerT2 target :: scope.openDecls } }
private local instance centerTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.centerTangentT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.centerTangentT2 target :: scope.openDecls } }
private local instance centerSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.centerSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.centerSigma target :: scope.openDecls } }

private theorem exists_redLength_le_half_finrank_of_innerProductSpace
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) {b tau : ℝ} (hb : b < 0) (htau : 0 < tau) :
    ∃ q : F.M, redLength F.S b p q tau ≤ (Module.finrank ℝ E : ℝ) / 2 := by
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _ht, x, hx⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) x (by decide : 0 < 4) (F.S.base.rm04 t x) hx⟩
  let _ : ConnectedSpace F.M := hF.connected
  let _ : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let _ : PseudoMetricSpace F.M :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  have hbmem : b ∈ D.carrier := by simpa only [hF.carrier_eq, _root_.Set.mem_Iic] using hb.le
  have hcomplete : RiemannianMetricComplete (I := I) (F.S.base.metric b) :=
    ⟨hF.complete b hbmem⟩
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  let K : ℝ := ((Module.finrank ℝ E : ℝ) ^ 2 * C) ^ 2
  have hreg : _root_.Set.Icc (b - (tau + 1)) b ⊆ D.regular := by
    intro t ht
    simpa only [hF.regular_eq, _root_.Set.mem_Iio] using ht.2.trans_lt hb
  have hRm : ∀ t ∈ _root_.Set.Icc (b - (tau + 1)) b, ∀ z : F.M,
      normSq0S (I := I) (F.S.base.metric t) z 4 (F.S.base.rm04 t z) ≤ K := by
    intro t ht z
    have htc : t ∈ D.carrier := D.regular_subset (hreg ht)
    have hnonnegC : 0 ≤ C := (hC t htc z).1.trans (hC t htc z).2
    have hop : metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) z ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
      apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
        (F.S.base.metric t) z).mpr
      intro n c a d
      simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
        hF.nonnegativeCurvatureOperator t htc z n c a d
    have hsqrt := sqrt_metricRm_normSq_le_finrank_sq_mul_scalar (I := I)
      (F.S.base.metric t) z hop
    have hscalar : metricScalarAt (I := I) (F.S.base.metric t) z ≤ C := (hC t htc z).2
    have hn2 : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 := sq_nonneg _
    have hs := hsqrt.trans (mul_le_mul_of_nonneg_left hscalar hn2)
    exact (Real.sqrt_le_left (mul_nonneg hn2 hnonnegC)).mp hs
  exact exists_redLen_le F.S F.isSolution K b (tau + 1) tau hcomplete
    htau (by linarith) hreg hRm p

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_redLength_le_half_finrank_of_innerProductSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_redLength_le_half_finrank_of_innerProductSpace target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance normedCenterTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normedCenterTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normedCenterTopology target :: scope.openDecls } }
private local instance normedCenterCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normedCenterCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normedCenterCharted target :: scope.openDecls } }
private local instance normedCenterSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normedCenterSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normedCenterSmooth target :: scope.openDecls } }
private local instance normedCenterT2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normedCenterT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normedCenterT2 target :: scope.openDecls } }
private local instance normedCenterSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normedCenterSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normedCenterSigma target :: scope.openDecls } }

theorem exists_redLength_le_half_finrank_of_ancient_of_neg
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) {b tau : ℝ} (hb : b < 0) (htau : 0 < tau) :
    ∃ q : F.M, redLength F.S b p q tau ≤ (Module.finrank ℝ E : ℝ) / 2 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean
  let J := I.transContinuousLinearEquiv e
  let Phi : F.M ≃ₘ⟮I, J⟯ F.M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I F.M e
  let G := F.pullback Phi.symm
  have hG : IsAncientKappaSolution kappa G := F.pullback_isAncientKappaSolution Phi.symm hF
  obtain ⟨q, hq⟩ :=
    exists_redLength_le_half_finrank_of_innerProductSpace G hG p hb htau
  refine ⟨q, ?_⟩
  have hcost := lCost_pullback F.S Phi.symm b p q tau
  change lCost (F.S.pullback Phi.symm) b p q tau = lCost F.S b p q tau at hcost
  change lCost (F.S.pullback Phi.symm) b p q tau / (2 * Real.sqrt tau) ≤ _ at hq
  change lCost F.S b p q tau / (2 * Real.sqrt tau) ≤ _
  rw [hcost] at hq
  simpa only [finrank_euclideanSpace, Fintype.card_fin] using hq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_redLength_le_half_finrank_of_ancient_of_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_redLength_le_half_finrank_of_ancient_of_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_redLength_le_half_finrank_of_ancient_of_neg ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_redLength_le_half_finrank_of_ancient_of_neg

theorem exists_eventually_redLength_le_half_finrank_of_ancient_of_neg
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) {b : ℝ} (hb : b < 0)
    (tau : ℕ → ℝ) (hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop) :
    ∃ q : ℕ → F.M, ∀ᶠ i in _root_.Filter.atTop,
      0 < tau i + b ∧ redLength F.S b p (q i) (tau i + b) ≤
        (Module.finrank ℝ E : ℝ) / 2 := by
  classical
  have hpoint (i : ℕ) : ∃ q : F.M, 0 < tau i + b →
      redLength F.S b p q (tau i + b) ≤ (Module.finrank ℝ E : ℝ) / 2 := by
    by_cases ht : 0 < tau i + b
    · obtain ⟨q, hq⟩ := exists_redLength_le_half_finrank_of_ancient_of_neg F hF p hb ht
      exact ⟨q, fun _ ↦ hq⟩
    · exact ⟨p, fun h ↦ (ht h).elim⟩
  choose q hq using hpoint
  refine ⟨q, ?_⟩
  filter_upwards [hescape.eventually_gt_atTop (-b)] with i hi
  have ht : 0 < tau i + b := by linarith
  exact ⟨ht, hq i ht⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_eventually_redLength_le_half_finrank_of_ancient_of_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_eventually_redLength_le_half_finrank_of_ancient_of_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_eventually_redLength_le_half_finrank_of_ancient_of_neg ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_eventually_redLength_le_half_finrank_of_ancient_of_neg

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
