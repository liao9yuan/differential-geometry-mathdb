import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalDerivativeEstimates
import Submission.DifferentialGeometry.Geometry.Metric.Product.ScalarCurvature
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyBasic
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Set _root_.Submission.Set _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

section UniformCurvature

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance roundJetTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundJetTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundJetTopology target :: scope.openDecls } }
private local instance roundJetCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundJetCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundJetCharted target :: scope.openDecls } }
private local instance roundJetSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundJetSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundJetSmooth target :: scope.openDecls } }
private local instance roundJetC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundJetC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundJetC1 target :: scope.openDecls } }
private local instance roundJetC2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 2 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundJetC2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundJetC2 target :: scope.openDecls } }
private local instance roundJetT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundJetT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundJetT2 target :: scope.openDecls } }
private local instance roundJetSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundJetSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundJetSigma target :: scope.openDecls } }
private local instance roundJetTangentT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundJetTangentT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundJetTangentT2 target :: scope.openDecls } }


theorem klim_curvDerivNorm_le_of_rmNormSq_bound {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) {kappa : ℝ} (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 3) {K : ℝ} (hKpos : 0 < K)
    (hcurv : ∀ q : ℝ, q ≤ 0 → ∀ z : F.M, F.rmNormSq (I := I) q z ≤ K ^ 2)
    {s : ℝ} (hs : s ≤ 0) (m : ℕ) (y : F.M) :
    curvDerivNorm (I := I) m (F.S.base.metric s) y ≤
      shiLocalUniformBound 3 m K (Real.sqrt K) * K := by
  let _ : ConnectedSpace F.M := hK.connected
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos.2 hKpos
  have houter : Real.sqrt K / Real.sqrt K = 1 := div_self hsqrt.ne'
  have ha : s - 1 ≤ 0 := by linarith
  have hspan : s - (s - 1) = 1 := by ring
  have hacar : s - 1 ∈ D.carrier := by
    simpa only [hK.carrier_eq, Set.mem_Iic] using ha
  have hcomplete : RiemannianMetricComplete (I := I) (F.S.base.metric (s - 1)) :=
    ⟨MetricComplete.complete (I := I) (F.atTime (I := I) (s - 1))
      (hK.complete (s - 1) hacar)⟩
  have hball : IsCompact {z : F.M |
      riemannianEDistOf (I := I) (F.S.base.metric (s - 1)) y z ≤
        ENNReal.ofReal (Real.sqrt K / Real.sqrt K)} := by
    rw [houter]
    exact hcomplete.closedEBall_isCompact y 1
  have hlocal : ∀ q ∈ Set.Icc (s - 1) s, ∀ z : F.M,
      riemannianEDistOf (I := I) (F.S.base.metric (s - 1)) y z ≤
        ENNReal.ofReal (Real.sqrt K / Real.sqrt K) →
          curvDerivNormSq (I := I) 0 (F.S.base.metric q) z ≤ K ^ 2 := by
    intro q hq z _
    change F.rmNormSq (I := I) q z ≤ K ^ 2
    exact hcurv q (hq.2.trans hs) z
  have hcarrier : Set.Icc (s - 1) s ⊆ D.carrier := by
    intro q hq
    simpa only [hK.carrier_eq, Set.mem_Iic] using hq.2.trans hs
  have hregular : Set.Ico (s - 1) s ⊆ D.regular := by
    intro q hq
    simpa only [hK.regular_eq, Set.mem_Iio] using hq.2.trans_le hs
  have hcenter : riemannianEDistOf (I := I) (F.S.base.metric (s - 1)) y y ≤
      ENNReal.ofReal (Real.sqrt K / (2 * Real.sqrt K)) :=
    (riemannianEDistOf_self (I := I) (F.S.base.metric (s - 1)) y).le.trans bot_le
  have hb := shi_local_curvDerivNorm_terminal_of_solution_jets F.S F.isSolution
    hK.dimension_ge_two (a := s - 1) (b := s) (K := K) (R := Real.sqrt K)
    (by linarith) hKpos hsqrt hcarrier hregular y hball hlocal
    m s ⟨by linarith, le_rfl⟩ y hcenter
  change curvDerivNorm (I := I) m (F.S.base.metric s) y ≤
    shiLocalUniformBound 3 m K (Real.sqrt K) * K
  simpa only [hdim, hspan, mul_one, Real.sqrt_one, one_pow, div_one] using hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klim_curvDerivNorm_le_of_rmNormSq_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klim_curvDerivNorm_le_of_rmNormSq_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klim_curvDerivNorm_le_of_rmNormSq_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klim_curvDerivNorm_le_of_rmNormSq_bound


theorem exists_mixed_jet_bound_of_rmNormSq_bound
    (hdim : Module.finrank ℝ E = 3) {K : ℝ} (hKpos : 0 < K) (p q : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (kappa : ℝ) (D : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) D),
        KLim kappa F →
        (∀ s : ℝ, s ≤ 0 → ∀ z : F.M, F.rmNormSq (I := I) s z ≤ K ^ 2) →
        ∀ t : ℝ, t ≤ 0 → ∀ y : F.M,
          DifferentiableWithinAt ℝ (fun s => mixedCurvatureTensor F.S p q s y) (Set.Iic 0) t ∧
          mixedCurvatureNorm F.S p q t y ≤ C := by
  classical
  choose P hP using fun j : ℕ => exists_mixed_curvature_jet_polynomials 3 p j
  let B : ℕ → ℝ := fun j => shiLocalUniformBound 3 j K (Real.sqrt K) * K
  refine ⟨1 + curvatureJetPolynomialNormBound (P q) B, ?_, ?_⟩
  · exact add_pos_of_pos_of_nonneg zero_lt_one (Real.sqrt_nonneg _)
  intro kappa D F hK hcurv t ht y
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have hdim_y : Module.finrank ℝ (TangentSpace I y) = 3 := hdim
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) (F.S.base.metric t) y hdim_y
  have hON : ∀ i j, (F.S.base.metric t).inner y (basis i) (basis j) =
      if i = j then 1 else 0 := horth
  have hactual : DifferentiableWithinAt ℝ
        (fun s => mixedCurvatureTensor F.S p q s y) (Set.Iic 0) t ∧
      ∀ slots, component0S (I := I) basis (mixedCurvatureTensor F.S p q t y) slots =
        MvPolynomial.eval (curvatureJetPolynomialValues F.S (p + 2 * q) t basis) (P q slots) := by
    rcases lt_or_eq_of_le ht with htneg | rfl
    · have htr : t ∈ D.regular := by simpa only [hK.regular_eq, Set.mem_Iio] using htneg
      obtain ⟨hdiff, hcomp⟩ := hP q F.S F.isSolution t htr y basis
      exact ⟨hdiff.differentiableWithinAt, hcomp⟩
    · have hreg : Set.Ioo (-1 : ℝ) 0 ⊆ D.regular := by
        intro s hs
        simpa only [hK.regular_eq, Set.mem_Iio] using hs.2
      exact mixedCurvature_polynomial_terminal_of_regular F.S F.isSolution p
        (by norm_num : (-1 : ℝ) < 0) hK.carrier_eq hreg P y basis
        (fun j s hs => hP j F.S F.isSolution s (hreg hs) y basis) q
  refine ⟨hactual.1, ?_⟩
  have hbound := norm_le_curvatureJetPolynomialNormBound F.S t basis hON (P q)
    (mixedCurvatureTensor F.S p q t y) hactual.2 B
    (fun j _ => klim_curvDerivNorm_le_of_rmNormSq_bound F hK hdim hKpos hcurv ht j y)
  exact hbound.trans (le_add_of_nonneg_left zero_le_one)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_mixed_jet_bound_of_rmNormSq_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_mixed_jet_bound_of_rmNormSq_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_mixed_jet_bound_of_rmNormSq_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_mixed_jet_bound_of_rmNormSq_bound

end UniformCurvature

section RoundBranch

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

private local instance roundMixedJetsFlowC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, 0, 0} (I := I3) D) : IsManifold I3 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundMixedJetsFlowC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundMixedJetsFlowC1 target :: scope.openDecls } }

private instance roundMixedJetsSphere4 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundMixedJetsSphere4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundMixedJetsSphere4 target :: scope.openDecls } }

private theorem roundThreeSpace_finrank : Module.finrank ℝ ThreeSpace = 3 := by
  simp [ThreeSpace]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundThreeSpace_finrank
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundThreeSpace_finrank target :: scope.openDecls } }

private local instance roundThreeSpace_finrank_neZero :
    NeZero (Module.finrank ℝ ThreeSpace) :=
  ⟨by rw [roundThreeSpace_finrank]; norm_num⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundThreeSpace_finrank_neZero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.roundThreeSpace_finrank_neZero target :: scope.openDecls } }


theorem exists_roundSphereQuotient_metricScalarAt_const
    (Dq : RoundSphereQuotient.{0, u} (EuclideanSpace ℝ (Fin 4)) 3) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : Dq.Q, metricScalarAt (I := 𝓡 3) Dq.gQuot x = R := by
  classical
  obtain ⟨c, hc, hsec⟩ := Dq.gQuot_constPosSec
  refine ⟨6 * c, by linarith, fun x => ?_⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    simp
  have hb := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := 𝓡 3) Dq.gQuot x
  rw [hdim] at hb
  obtain ⟨bas, hbas⟩ := hb
  have hentry : ∀ i j : Fin 3,
      metricRm04StandardAt (I := 𝓡 3) Dq.gQuot x (bas j) (bas i) (bas i) (bas j) =
        c * ((if j = j then (1 : ℝ) else 0) * (if i = i then (1 : ℝ) else 0) -
          (if j = i then (1 : ℝ) else 0) * (if j = i then (1 : ℝ) else 0)) := by
    intro i j
    rw [hsec, hbas, hbas, hbas]
  rw [metricScalarAt_eq_sum_sum_rm04_of_orthonormal Dq.gQuot bas hbas]
  change (∑ i : Fin 3, ∑ j : Fin 3,
    metricRm04StandardAt (I := 𝓡 3) Dq.gQuot x (bas j) (bas i) (bas i) (bas j)) = 6 * c
  simp only [hentry, Fin.sum_univ_three]
  norm_num [(by decide : ¬((0 : Fin 3) = 1)), (by decide : ¬((0 : Fin 3) = 2)),
    (by decide : ¬((1 : Fin 3) = 0)), (by decide : ¬((1 : Fin 3) = 2)),
    (by decide : ¬((2 : Fin 3) = 0)), (by decide : ¬((2 : Fin 3) = 1))]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_roundSphereQuotient_metricScalarAt_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_roundSphereQuotient_metricScalarAt_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_roundSphereQuotient_metricScalarAt_const ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_roundSphereQuotient_metricScalarAt_const

variable (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)


theorem sphericalSpaceFormFlow_scalar_eq
    (hround : IsShrinkingSphericalSpaceFormFlow (I := I3) F)
    {t : ℝ} (ht : t ≤ 0) (y z : F.M) :
    F.S.scalar t y = F.S.scalar t z := by
  obtain ⟨T, hT, Dq, e, hmetric⟩ := hround
  obtain ⟨R, _, hR⟩ := exists_roundSphereQuotient_metricScalarAt_const Dq
  have hpos : 0 < 4 * (T - t) := by
    have : 0 < T - t := by linarith
    linarith
  have hm : F.S.base.metric t = scaleMetric (4 * (T - t)) hpos
      (Diffeomorph.pullbackMetricCross Dq.gQuot e) := hmetric t ht
  have key : ∀ w : F.M, F.S.scalar t w = (4 * (T - t))⁻¹ * R := by
    intro w
    have h0 : F.S.scalar t w = metricScalarAt (I := I3) (F.S.base.metric t) w := rfl
    rw [h0, hm, metricScalarAt_scaleMetric, metricScalar_cross, hR (e w)]
  rw [key y, key z]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphericalSpaceFormFlow_scalar_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphericalSpaceFormFlow_scalar_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphericalSpaceFormFlow_scalar_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphericalSpaceFormFlow_scalar_eq


theorem sphericalSpaceFormFlow_normalized_scalar_terminal_eq_one {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I3) kappa F)
    (hround : IsShrinkingSphericalSpaceFormFlow (I := I3) F)
    {t : ℝ} (ht : t ≤ 0) (x : F.M) (z : F.M) :
    (universalNormalizedFlow F hF ht x).S.scalar 0 z = 1 := by
  have hQ : 0 < F.S.scalar t x :=
    ancientKappa_scalar_pos F hF ht x
  have hval : (universalNormalizedFlow F hF ht x).S.scalar 0 z =
      (F.S.scalar t x)⁻¹ * F.S.scalar t z := by
    have h := congrFun (congrFun (curvatureNormalizedSolution_scalar F.S t (F.S.scalar t x)
      hQ (ht : t ∈ ancientTimeInterval.carrier)) 0) z
    simp only [parabolicTime_zero] at h
    exact h
  rw [hval, sphericalSpaceFormFlow_scalar_eq F hround ht z x]
  exact inv_mul_cancel₀ hQ.ne'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphericalSpaceFormFlow_normalized_scalar_terminal_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphericalSpaceFormFlow_normalized_scalar_terminal_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphericalSpaceFormFlow_normalized_scalar_terminal_eq_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sphericalSpaceFormFlow_normalized_scalar_terminal_eq_one


theorem exists_round_mixed_jet_bound (a b : ℕ) :
    ∃ C : ℝ, 0 < C ∧ RoundMixedJetBound.{u} a b C := by
  obtain ⟨C, hC, hbound⟩ := exists_mixed_jet_bound_of_rmNormSq_bound (I := I3)
    roundThreeSpace_finrank (K := 2) (by norm_num) a b
  refine ⟨C, hC, ?_⟩
  intro kappa F hF hround t ht x
  set Q : ℝ := F.S.scalar t x with hQdef
  have hQ : 0 < Q := ancientKappa_scalar_pos F hF ht x
  have hG : KLim kappa (universalNormalizedFlow F hF ht x) :=
    ancientKappaThree_toKLim (universalNormalizedFlow F hF ht x)
      (universalNormalizedFlow_isAncientKappaSolution F hF ht x) roundThreeSpace_finrank
  have hcurv : ∀ s : ℝ, s ≤ 0 → ∀ z : (universalNormalizedFlow F hF ht x).M,
      (universalNormalizedFlow F hF ht x).rmNormSq (I := I3) s z ≤ (2 : ℝ) ^ 2 := by
    intro s hs z
    have hterm : (universalNormalizedFlow F hF ht x).S.scalar 0 z ≤ 1 :=
      le_of_eq (sphericalSpaceFormFlow_normalized_scalar_terminal_eq_one F hF hround ht x z)
    exact (KLim.rmNormSq_le_of_terminal_scalar_le (universalNormalizedFlow F hF ht x) hG
      roundThreeSpace_finrank hs z hterm).trans (by norm_num)
  have hnorm := (hbound kappa ancientTimeInterval (universalNormalizedFlow F hF ht x)
    hG hcurv 0 le_rfl x).2
  have hnorm' : mixedCurvatureNorm (curvatureNormalizedSolution F.S t Q hQ ht) a b 0 x ≤ C :=
    hnorm
  have hscale := mixedCurvatureNorm_curvatureNormalizedSolution (I := I3) F.S F.isSolution
    hF.carrier_eq hF.regular_eq t Q hQ ht a b (le_refl (0 : ℝ)) x
  have hpt : parabolicTime t Q 0 = t := by simp [parabolicTime]
  rw [hpt] at hscale
  have hexp : (-(1 : ℝ) - (a : ℝ) / 2 - (b : ℝ)) = -(mixedCurvatureWeight a b) := by
    simp only [mixedCurvatureWeight]; ring
  rw [hexp, Real.rpow_neg hQ.le] at hscale
  rw [hscale] at hnorm'
  have hw : 0 < Q ^ mixedCurvatureWeight a b := Real.rpow_pos_of_pos hQ _
  have hfinal := (inv_mul_le_iff₀ hw).1 hnorm'
  linarith [hfinal]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_round_mixed_jet_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_round_mixed_jet_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_round_mixed_jet_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_round_mixed_jet_bound


theorem exists_universal_mixed_jet_bound_unconditional (a b : ℕ) :
    ∃ C : ℝ, 0 < C ∧ UniversalMixedJetBound.{u} a b C := by
  obtain ⟨C₁, _, hround⟩ := exists_round_mixed_jet_bound.{u} a b
  exact exists_universal_mixed_jet_bound a b hround

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_universal_mixed_jet_bound_unconditional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_universal_mixed_jet_bound_unconditional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_universal_mixed_jet_bound_unconditional ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_universal_mixed_jet_bound_unconditional


end RoundBranch

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
