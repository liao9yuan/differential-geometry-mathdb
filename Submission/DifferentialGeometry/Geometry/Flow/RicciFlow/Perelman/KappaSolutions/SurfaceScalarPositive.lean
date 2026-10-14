import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarPositive
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceRmAlgebra

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance surfaceScalarPositiveTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveTopology
local instance surfaceScalarPositiveCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveCharted
local instance surfaceScalarPositiveSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveSmooth
local instance surfaceScalarPositiveC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveC1
local instance surfaceScalarPositiveSigmaCompact : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveSigmaCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveSigmaCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveSigmaCompact ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveSigmaCompact
local instance surfaceScalarPositiveT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveT2
local instance surfaceScalarPositiveTangentT2 : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveTangentT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveTangentT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveTangentT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceScalarPositiveTangentT2

variable {kappa : ℝ}

omit [I.Boundaryless] in
theorem pointedSurface_rmNormSq_eq_scalar_sq (hdim : Module.finrank ℝ E = 2)
    (t : ℝ) (x : F.M) : F.rmNormSq (I := I) t x = F.S.scalar t x ^ 2 := by
  have h := metricRm_normSq_eq_scalar_sq_of_finrank_two (I := I)
    (F.S.base.metric t) hdim x
  simpa only [PointedFlowData.rmNormSq, FlowMetricBall.rmNormSq,
    SolutionOn.family, SolutionFamily.rm04, metricRm04_apply,
    SolutionOn.scalar, SolutionFamily.scalar] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedSurface_rmNormSq_eq_scalar_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedSurface_rmNormSq_eq_scalar_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedSurface_rmNormSq_eq_scalar_sq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedSurface_rmNormSq_eq_scalar_sq

omit [I.Boundaryless] in
private theorem surfaceAncient_operator_nonnegative
    (hF : IsAncientKappaSolution kappa F) {t : ℝ} (ht : t ∈ D.carrier) (x : F.M) :
    metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
  apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
  intro n c v w
  have h := hF.nonnegativeCurvatureOperator t ht x n c v w
  simpa only [algebraicCurvatureOperatorQuadraticEval,
    metricAlgebraicCurvatureTensorAt, tensor04StandardAt, SolutionFamily.rm04,
    metricRm04_apply] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceAncient_operator_nonnegative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceAncient_operator_nonnegative target :: scope.openDecls } }

omit [I.Boundaryless] in
private theorem surfaceAncient_complete
    (hF : IsAncientKappaSolution kappa F) {t : ℝ} (ht : t ∈ D.regular) :
    RiemannianMetricComplete (I := I) (F.S.base.metric t) := by
  refine ⟨?_⟩
  exact hF.complete t (D.regular_subset ht)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceAncient_complete
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceAncient_complete target :: scope.openDecls } }

omit [I.Boundaryless] in
theorem ancientKappaSurface_rmNormLeScalar (hdim : Module.finrank ℝ E = 2)
    (hF : IsAncientKappaSolution kappa F) :
    PointedFlowRmNormLeScalar (I := I) F 1 := by
  intro t ht x
  have ht0 : t ≤ 0 := by simpa only [hF.carrier_eq, Set.mem_Iic] using ht
  rw [pointedSurface_rmNormSq_eq_scalar_sq F hdim, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (ancientKappa_scalar_nonneg F hF ht0 x), one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_rmNormLeScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_rmNormLeScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_rmNormLeScalar ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_rmNormLeScalar

omit [I.Boundaryless] in
theorem ancientKappaSurface_rmNormSqBounded (hdim : Module.finrank ℝ E = 2)
    (hF : IsAncientKappaSolution kappa F) :
    ∃ C : ℝ, PointedFlowScalarBounded (I := I) F C ∧
      PointedFlowRmNormSqBounded (I := I) F (C ^ 2) := by
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  refine ⟨C, hC, ?_⟩
  simpa only [one_mul] using pointedFlowRmNormSqBounded_of_scalarBounded (I := I) F
    (by norm_num : (0 : ℝ) ≤ 1) hC (ancientKappaSurface_rmNormLeScalar F hdim hF)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_rmNormSqBounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_rmNormSqBounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_rmNormSqBounded ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_rmNormSqBounded

omit [I.Boundaryless] in
private theorem surfaceAncient_regularSlabBound (hdim : Module.finrank ℝ E = 2)
    (hF : IsAncientKappaSolution kappa F) :
    ∀ a b : ℝ, Set.Icc a b ⊆ D.regular →
      ∃ C : ℝ, ∀ t ∈ Set.Icc a b, ∀ x : F.M,
        normSq0S (I := I) (F.S.base.metric t) x 4 (F.S.base.rm04 t x) ≤ C := by
  obtain ⟨C, _, hC⟩ := ancientKappaSurface_rmNormSqBounded F hdim hF
  intro a b hslab
  refine ⟨C ^ 2, ?_⟩
  intro t ht x
  exact hC t (D.regular_subset (hslab ht)) x

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceAncient_regularSlabBound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.surfaceAncient_regularSlabBound target :: scope.openDecls } }

omit [I.Boundaryless] in
theorem pointedSurface_rmNormSq_eq_zero_of_scalar_eq_zero
    (hdim : Module.finrank ℝ E = 2) {t : ℝ} (x : F.M) (hx : F.S.scalar t x = 0) :
    F.rmNormSq (I := I) t x = 0 := by
  rw [pointedSurface_rmNormSq_eq_scalar_sq F hdim, hx, zero_pow (by decide : 2 ≠ 0)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedSurface_rmNormSq_eq_zero_of_scalar_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedSurface_rmNormSq_eq_zero_of_scalar_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedSurface_rmNormSq_eq_zero_of_scalar_eq_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedSurface_rmNormSq_eq_zero_of_scalar_eq_zero

theorem ancientKappaSurface_past_flat_of_scalar_eq_zero
    (hdim : Module.finrank ℝ E = 2) (hF : IsAncientKappaSolution kappa F)
    {s t : ℝ} (hst : s < t) (ht : t ≤ 0) (x : F.M) (hx : F.S.scalar t x = 0) :
    ∀ y : F.M, F.rmNormSq (I := I) s y = 0 := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let _ : ConnectedSpace F.M := hF.connected
  let m : ℝ := (s + t) / 2
  have hsm : s < m := by dsimp only [m]; linarith
  have hmt : m < t := by dsimp only [m]; linarith
  have hm : m < 0 := hmt.trans_le ht
  have hmonotone := ancientKappa_scalar_monotoneOn F hF x hm.le ht hmt.le
  change F.S.scalar m x ≤ F.S.scalar t x at hmonotone
  have hmx : F.S.scalar m x = 0 := by
    rw [hx] at hmonotone
    exact le_antisymm hmonotone (ancientKappa_scalar_nonneg F hF hm.le x)
  intro y
  have hHarnack := hamilton_ancient_trace_harnack_distance (I := I) F.S F.isSolution
    (fun r hr => surfaceAncient_complete F hF hr)
    (surfaceAncient_regularSlabBound F hdim hF)
    (fun r hr z => surfaceAncient_operator_nonnegative F hF (D.regular_subset hr) z)
    hsm (by
      intro r hr
      simpa only [hF.regular_eq, Set.mem_Iio] using hr.trans_lt hm)
    y x (by simp only [PreconnectedSpace.connectedComponent_eq_univ, Set.mem_univ])
  have hsy : F.S.scalar s y = 0 := by
    rw [hmx] at hHarnack
    have he := Real.exp_pos
      (-((riemannianEDistOf (I := I) (F.S.base.metric s) y x).toReal ^ 2 /
        (4 * (m - s))))
    have hn := ancientKappa_scalar_nonneg F hF (hst.le.trans ht) y
    nlinarith
  exact pointedSurface_rmNormSq_eq_zero_of_scalar_eq_zero F hdim y hsy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_past_flat_of_scalar_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_past_flat_of_scalar_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_past_flat_of_scalar_eq_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_past_flat_of_scalar_eq_zero

theorem ancientKappaSurface_scalar_pos (hdim : Module.finrank ℝ E = 2)
    (hF : IsAncientKappaSolution kappa F) {t : ℝ} (ht : t ≤ 0) (x : F.M) :
    0 < F.S.scalar t x := by
  apply lt_of_le_of_ne (ancientKappa_scalar_nonneg F hF ht x)
  intro hzero
  have hx : F.S.scalar t x = 0 := hzero.symm
  obtain ⟨tw, htw, y, hy⟩ := hF.notFlat
  have htw0 : tw ≤ 0 := by simpa only [hF.carrier_eq, Set.mem_Iic] using htw
  let a : ℝ := _root_.Min.min tw t - 1
  have hat : a < t := by
    dsimp only [a]
    linarith [min_le_right tw t]
  have hatw : a < tw := by
    dsimp only [a]
    linarith [min_le_left tw t]
  have ha0 : a < 0 := hat.trans_le ht
  have hflat := ancientKappaSurface_past_flat_of_scalar_eq_zero F hdim hF hat ht x hx
  obtain ⟨C, _, hC⟩ := ancientKappaSurface_rmNormSqBounded F hdim hF
  have hforward := complete_forward_flatness F ha0
    (by
      intro r hr
      simpa only [hF.carrier_eq, Set.mem_Iic] using hr.2)
    (by
      intro r hr
      simpa only [hF.regular_eq, Set.mem_Iio] using hr.2)
    (fun r hr => hF.complete r (by simpa only [hF.carrier_eq, Set.mem_Iic] using hr.2))
    ⟨C ^ 2, fun r hr z =>
      hC r (by simpa only [hF.carrier_eq, Set.mem_Iic] using hr.2) z⟩ hflat
  exact hy (hforward tw ⟨hatw.le, htw0⟩ y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_scalar_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_scalar_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_scalar_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaSurface_scalar_pos

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
