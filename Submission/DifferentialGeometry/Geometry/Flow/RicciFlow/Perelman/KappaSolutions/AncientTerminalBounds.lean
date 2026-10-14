import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NonnegativeCurvatureScalarNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance ancientBoundsTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientBoundsTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientBoundsTopology target :: scope.openDecls } }
private local instance ancientBoundsCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientBoundsCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientBoundsCharted target :: scope.openDecls } }
private local instance ancientBoundsSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientBoundsSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientBoundsSmooth target :: scope.openDecls } }
private local instance ancientBoundsC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := (∞ : WithTop ℕ∞))
    (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientBoundsC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientBoundsC1 target :: scope.openDecls } }
private local instance ancientBoundsT2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientBoundsT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientBoundsT2 target :: scope.openDecls } }
private local instance ancientBoundsTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientBoundsTangentT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientBoundsTangentT2 target :: scope.openDecls } }
private local instance ancientBoundsSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientBoundsSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientBoundsSigma target :: scope.openDecls } }

theorem terminalTime_not_mem_regular
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
    (hcarrier : D.carrier = Set.Iic 0) :
    (0 : ℝ) ∉ D.regular := by
  intro h0
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp (D.regular_isOpen.mem_nhds h0)
  have hpos : (0 : ℝ) < eps / 2 := by linarith
  have hdist : _root_.Dist.dist (eps / 2) (0 : ℝ) < eps := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
    linarith
  have hreg : eps / 2 ∈ D.regular := hball hdist
  have hmem : eps / 2 ∈ D.carrier := D.regular_subset hreg
  rw [hcarrier] at hmem
  exact absurd (Set.mem_Iic.mp hmem) (not_le.mpr hpos)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalTime_not_mem_regular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalTime_not_mem_regular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalTime_not_mem_regular ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalTime_not_mem_regular

theorem ancientTimeInterval_terminal_not_regular :
    (0 : ℝ) ∉ ancientTimeInterval.regular :=
  terminalTime_not_mem_regular ancientTimeInterval rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTimeInterval_terminal_not_regular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTimeInterval_terminal_not_regular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTimeInterval_terminal_not_regular ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTimeInterval_terminal_not_regular

theorem ancientTimeInterval_slab_not_regular {tau : ℝ} (htau : 0 < tau) :
    ¬ (Set.Icc (0 - tau) 0 ⊆ ancientTimeInterval.regular) := by
  intro hslab
  exact ancientTimeInterval_terminal_not_regular (hslab ⟨by linarith, le_rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTimeInterval_slab_not_regular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTimeInterval_slab_not_regular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTimeInterval_slab_not_regular ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTimeInterval_slab_not_regular

theorem ancientTimeInterval_slab_not_regular_of_carrier
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval) {tau : ℝ}
    (hcarrier : D.carrier = Set.Iic 0) (htau : 0 < tau) :
    ¬ (Set.Icc (0 - tau) 0 ⊆ D.regular) := by
  intro hslab
  exact terminalTime_not_mem_regular D hcarrier (hslab ⟨by linarith, le_rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTimeInterval_slab_not_regular_of_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTimeInterval_slab_not_regular_of_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTimeInterval_slab_not_regular_of_carrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientTimeInterval_slab_not_regular_of_carrier

omit [I.Boundaryless] in
theorem ancientKappa_rmNormLeScalar_finrank {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) :
    PointedFlowRmNormLeScalar (I := I) F ((Module.finrank ℝ E : ℝ) ^ 2) := by
  intro t ht x
  have hoperator :
      metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    have h := hF.nonnegativeCurvatureOperator t ht x n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
      tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using h
  have hbound := sqrt_metricRm_normSq_le_finrank_sq_mul_scalar (I := I)
    (F.S.base.metric t) x hoperator
  simpa only [PointedFlowData.rmNormSq, SolutionOn.family, SolutionFamily.rm04,
    metricRm04_apply, SolutionOn.scalar, SolutionFamily.scalar] using hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_rmNormLeScalar_finrank then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_rmNormLeScalar_finrank"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_rmNormLeScalar_finrank ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_rmNormLeScalar_finrank

omit [I.Boundaryless] in
theorem ancientKappa_rmNormSqBounded_finrank {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) :
    ∃ K : ℝ, ∀ t ∈ D.carrier, ∀ x : F.M,
      normSq0S (I := I) (F.S.base.metric t) x 4 (F.S.base.rm04 t x) ≤ K := by
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  refine ⟨((Module.finrank ℝ E : ℝ) ^ 2 * C) ^ 2, ?_⟩
  intro t ht x
  have hle := ancientKappa_rmNormLeScalar_finrank (I := I) F hF t ht x
  have hscalar : F.S.scalar t x ≤ C := (hC t ht x).2
  have hsqrt : Real.sqrt (F.rmNormSq (I := I) t x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * C :=
    hle.trans (mul_le_mul_of_nonneg_left hscalar (sq_nonneg _))
  have hnonneg : 0 ≤ F.rmNormSq (I := I) t x := by
    simpa only [PointedFlowData.rmNormSq, SolutionOn.family] using
      normSq0S_nonneg (I := I) (F.S.base.metric t) x 4 (F.S.base.rm04 t x)
  have hsq : Real.sqrt (F.rmNormSq (I := I) t x) ^ 2 = F.rmNormSq (I := I) t x :=
    Real.sq_sqrt hnonneg
  have hfinal : F.rmNormSq (I := I) t x ≤
      ((Module.finrank ℝ E : ℝ) ^ 2 * C) ^ 2 := by
    nlinarith [Real.sqrt_nonneg (F.rmNormSq (I := I) t x)]
  simpa only [PointedFlowData.rmNormSq, SolutionOn.family, SolutionFamily.rm04,
    metricRm04_apply] using hfinal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_rmNormSqBounded_finrank then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_rmNormSqBounded_finrank"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_rmNormSqBounded_finrank ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_rmNormSqBounded_finrank

omit [I.Boundaryless] in
theorem ancientKappa_regularSlabBound_finrank {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (a b : ℝ)
    (hslab : Set.Icc a b ⊆ D.regular) :
    ∃ K : ℝ, ∀ t ∈ Set.Icc a b, ∀ z : F.M,
      normSq0S (I := I) (F.S.base.metric t) z 4 (F.S.base.rm04 t z) ≤ K := by
  obtain ⟨K, hK⟩ := ancientKappa_rmNormSqBounded_finrank (I := I) F hF
  exact ⟨K, fun t ht z => hK t (D.regular_subset (hslab ht)) z⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_regularSlabBound_finrank then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_regularSlabBound_finrank"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_regularSlabBound_finrank ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_regularSlabBound_finrank

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
