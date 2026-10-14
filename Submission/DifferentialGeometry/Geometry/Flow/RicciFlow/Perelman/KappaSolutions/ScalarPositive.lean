import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ForwardFlatness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RmNormFromEigenvalues
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientScalarMonotonicity

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
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {D : RealTimeInterval}
variable (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete Real E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

local instance scalarPositiveTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveTopology
local instance scalarPositiveCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveCharted
local instance scalarPositiveSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveSmooth
local instance scalarPositiveC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞)
    (by decide : (1 : WithTop ℕ∞) ≤ ∞)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveC1
local instance scalarPositiveSigmaCompact : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveSigmaCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveSigmaCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveSigmaCompact ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveSigmaCompact
local instance scalarPositiveT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveT2
local instance scalarPositiveTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveTangentT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveTangentT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveTangentT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.scalarPositiveTangentT2

variable {kappa : Real}

omit [I.Boundaryless] in
theorem ancientKappa_scalar_nonneg (hF : IsAncientKappaSolution kappa F)
    {t : Real} (ht : t ≤ 0) (x : F.M) : 0 ≤ F.S.scalar t x := by
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  exact (hC t (by simpa only [hF.carrier_eq, Set.mem_Iic] using ht) x).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_scalar_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_scalar_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_scalar_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_scalar_nonneg

omit [I.Boundaryless] in
private theorem ancientKappa_operator_nonnegative
    (hF : IsAncientKappaSolution kappa F) {t : Real} (ht : t ∈ D.carrier)
    (x : F.M) :
    metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
  apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
  intro n c v w
  have h := hF.nonnegativeCurvatureOperator t ht x n c v w
  simpa only [algebraicCurvatureOperatorQuadraticEval,
    metricAlgebraicCurvatureTensorAt, tensor04StandardAt, SolutionFamily.rm04,
    metricRm04_apply] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_operator_nonnegative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_operator_nonnegative target :: scope.openDecls } }

omit [I.Boundaryless] in
private theorem ancientKappa_complete
    (hF : IsAncientKappaSolution kappa F) {t : Real} (ht : t ∈ D.regular) :
    RiemannianMetricComplete (I := I) (F.S.base.metric t) := by
  refine ⟨?_⟩
  exact hF.complete t (D.regular_subset ht)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_complete
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_complete target :: scope.openDecls } }

omit [I.Boundaryless] in
theorem ancientKappa_rmNormLeScalar (hdim : Module.finrank Real E = 3)
    (hF : IsAncientKappaSolution kappa F) :
    PointedFlowRmNormLeScalar (I := I) F (Real.sqrt 3) := by
  intro t ht x
  have hnonnegative : curvatureOperatorLowerBoundAt (I := I) (F.S.base.metric t) x
      ⟨F.S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (F.S.base.metric t) x⟩ 0 := by
    intro n c v w
    have h := hF.nonnegativeCurvatureOperator t ht x n c v w
    simpa [algebraicCurvatureOperatorQuadraticEval,
      algebraicCurvatureIdentityQuadraticEval, tensor04StandardAt] using h
  have hbound := sqrt_rmNormSq_le_sqrt_three_mul_scalar_of_curvatureOperatorNonneg
    (I := I) F.S hdim t x hnonnegative
  simpa only [PointedFlowData.rmNormSq, FlowMetricBall.rmNormSq,
    SolutionOn.family] using hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_rmNormLeScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_rmNormLeScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_rmNormLeScalar ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_rmNormLeScalar

omit [I.Boundaryless] in
theorem ancientKappa_rmNormSqBounded (hdim : Module.finrank Real E = 3)
    (hF : IsAncientKappaSolution kappa F) :
    ∃ C : Real, PointedFlowScalarBounded (I := I) F C ∧
      PointedFlowRmNormSqBounded (I := I) F ((Real.sqrt 3 * C) ^ 2) := by
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  exact ⟨C, hC, pointedFlowRmNormSqBounded_of_scalarBounded (I := I) F
    (Real.sqrt_nonneg 3) hC (ancientKappa_rmNormLeScalar F hdim hF)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_rmNormSqBounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_rmNormSqBounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_rmNormSqBounded ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_rmNormSqBounded

omit [I.Boundaryless] in
theorem ancientKappa_rmNormSq_eq_zero_of_scalar_eq_zero
    (hF : IsAncientKappaSolution kappa F)
    {t : Real} (ht : t ≤ 0) (x : F.M) (hx : F.S.scalar t x = 0) :
    F.rmNormSq (I := I) t x = 0 := by
  have hbound := ancientKappa_rmNormLeScalar_finrank F hF t
    (by simpa only [hF.carrier_eq, Set.mem_Iic] using ht) x
  rw [hx, _root_.MulZeroClass.mul_zero] at hbound
  have hzero : Real.sqrt (F.rmNormSq (I := I) t x) = 0 :=
    le_antisymm hbound (Real.sqrt_nonneg _)
  have hsquare := Real.sq_sqrt (pointedFlow_rmNormSq_nonneg (I := I) F t x)
  rw [hzero, zero_pow (by decide : 2 ≠ 0)] at hsquare
  exact hsquare.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_rmNormSq_eq_zero_of_scalar_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_rmNormSq_eq_zero_of_scalar_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_rmNormSq_eq_zero_of_scalar_eq_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_rmNormSq_eq_zero_of_scalar_eq_zero

theorem ancientKappa_past_flat_of_scalar_eq_zero
    (hF : IsAncientKappaSolution kappa F)
    {s t : Real} (hst : s < t) (ht : t ≤ 0) (x : F.M)
    (hx : F.S.scalar t x = 0) :
    ∀ y : F.M, F.rmNormSq (I := I) s y = 0 := by
  let : NeZero (Module.finrank Real E) := by
    obtain ⟨r, _hr, y, hy⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric r) y (by decide : 0 < 4) (F.S.base.rm04 r y) hy⟩
  let : ConnectedSpace F.M := hF.connected
  let m : Real := (s + t) / 2
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
    (fun r hr => ancientKappa_complete F hF hr)
    (ancientKappa_regularSlabBound_finrank F hF)
    (fun r hr z => ancientKappa_operator_nonnegative F hF (D.regular_subset hr) z)
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
  exact ancientKappa_rmNormSq_eq_zero_of_scalar_eq_zero F hF (hst.le.trans ht) y hsy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_past_flat_of_scalar_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_past_flat_of_scalar_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_past_flat_of_scalar_eq_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_past_flat_of_scalar_eq_zero

theorem ancientKappa_scalar_pos
    (hF : IsAncientKappaSolution kappa F) {t : Real} (ht : t ≤ 0) (x : F.M) :
    0 < F.S.scalar t x := by
  apply lt_of_le_of_ne (ancientKappa_scalar_nonneg F hF ht x)
  intro hzero
  have hx : F.S.scalar t x = 0 := hzero.symm
  obtain ⟨tw, htw, y, hy⟩ := hF.notFlat
  have htw0 : tw ≤ 0 := by simpa only [hF.carrier_eq, Set.mem_Iic] using htw
  let a : Real := _root_.Min.min tw t - 1
  have hat : a < t := by
    dsimp only [a]
    linarith [min_le_right tw t]
  have hatw : a < tw := by
    dsimp only [a]
    linarith [min_le_left tw t]
  have ha0 : a < 0 := hat.trans_le ht
  have hflat := ancientKappa_past_flat_of_scalar_eq_zero F hF hat ht x hx
  obtain ⟨C, hC⟩ := ancientKappa_rmNormSqBounded_finrank F hF
  have hforward := complete_forward_flatness F ha0
    (by
      intro r hr
      simpa only [hF.carrier_eq, Set.mem_Iic] using hr.2)
    (by
      intro r hr
      simpa only [hF.regular_eq, Set.mem_Iio] using hr.2)
    (fun r hr => hF.complete r (by simpa only [hF.carrier_eq, Set.mem_Iic] using hr.2))
    ⟨C, fun r hr z =>
      hC r (by simpa only [hF.carrier_eq, Set.mem_Iic] using hr.2) z⟩ hflat
  exact hy (hforward tw ⟨hatw.le, htw0⟩ y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_scalar_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_scalar_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_scalar_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_scalar_pos

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
