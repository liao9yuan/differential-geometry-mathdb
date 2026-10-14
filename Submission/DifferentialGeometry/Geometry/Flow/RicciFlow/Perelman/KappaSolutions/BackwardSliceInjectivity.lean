import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientRescaledVolume
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackSelectedInjectivity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceSequence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Bundle _root_.Submission.Bundle

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance injTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.injTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.injTopology target :: scope.openDecls } }
private local instance injCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.injCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.injCharted target :: scope.openDecls } }
private local instance injSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.injSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.injSmooth target :: scope.openDecls } }
private local instance injT2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.injT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.injT2 target :: scope.openDecls } }
private local instance injSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.injSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.injSigma target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_backwardSliceSequence_injRadius_bound
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {A D : ℝ} (hbase : ∀ i, redLength F.S 0 p (q i) (tau i) ≤ A) (hD : 0 ≤ D) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ i : ℕ, ∀ x : F.M,
      riemannianEDistOf ((backwardSliceSequence F tau htau q).obj i).metric (q i) x ≤
        ENNReal.ofReal D →
      HasInjRadiusAt (I := I) ((backwardSliceSequence F tau htau q).obj i) x eta := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let K := 1 + (Module.finrank ℝ E : ℝ) ^ 2 *
    (3 * (Real.sqrt A + Real.sqrt 3 / 2 * (D + 1)) ^ 2)
  have hK : 0 < K := by dsimp only [K]; positivity
  let rho := _root_.Min.min 1 (1 / Real.sqrt K)
  have hrho : 0 < rho := lt_min zero_lt_one (one_div_pos.mpr (Real.sqrt_pos.mpr hK))
  have hrho1 : rho ≤ 1 := min_le_left _ _
  have hrhoK : rho ≤ 1 / Real.sqrt K := min_le_right _ _
  obtain ⟨rJ, hrJ, hrJrho, herror⟩ :=
    exists_uniform_local_jacobi_scale (Module.finrank ℝ E) hrho hK.le
  let R := _root_.Min.min rJ (Real.pi / Real.sqrt K)
  have hR : 0 < R := lt_min hrJ (div_pos Real.pi_pos (Real.sqrt_pos.mpr hK))
  have hRj : R ≤ rJ := min_le_left _ _
  have hRrho : R ≤ rho := hRj.trans hrJrho
  have hRpi : R ≤ Real.pi / Real.sqrt K := min_le_right _ _
  have hsmall : 0 < R / 8 := by positivity
  have hsmallR : R / 8 ≤ R := by linarith
  have hsmall1 : R / 8 ≤ 1 := hsmallR.trans (hRrho.trans hrho1)
  have hsmallK : (R / 8) ^ 2 *
      ((Module.finrank ℝ E : ℝ) ^ 2 *
        (3 * (Real.sqrt A + Real.sqrt 3 / 2 * (D + 1)) ^ 2)) ≤ 1 := by
    have hmul : (R / 8) * Real.sqrt K ≤ 1 :=
      (le_div_iff₀ (Real.sqrt_pos.mpr hK)).mp (hsmallR.trans (hRrho.trans hrhoK))
    have hsquare := (sq_le_sq₀ (mul_nonneg hsmall.le (Real.sqrt_nonneg K)) zero_le_one).2 hmul
    rw [mul_pow, Real.sq_sqrt hK.le, one_pow] at hsquare
    have hle : (Module.finrank ℝ E : ℝ) ^ 2 *
        (3 * (Real.sqrt A + Real.sqrt 3 / 2 * (D + 1)) ^ 2) ≤ K := by
      dsimp only [K]
      linarith
    exact (mul_le_mul_of_nonneg_left hle (sq_nonneg (R / 8))).trans hsquare
  have heta := selectedCGTInjRadius_pos (E := E) hF.kappa_pos hR
  refine ⟨selectedCGTInjRadius E kappa R, heta, ?_⟩
  intro i x hx
  refine ⟨heta, ?_⟩
  intro hcomplete
  let Y := (backwardSliceSequence F tau htau q).obj i
  let _ : TopologicalSpace Y.M := Y.topology
  let _ : ChartedSpace H Y.M := Y.charted
  let _ : IsManifold I ∞ Y.M := Y.smooth
  let _ : IsManifold I 1 Y.M := IsManifold.of_le (n := ∞) (by decide)
  let _ : T2Space Y.M := Y.t2
  let _ : SigmaCompactSpace Y.M := Y.sigmaCompact
  let _ : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let _ : Bundle.RiemannianBundle (fun y : Y.M => TangentSpace I y) := Y.riemBundle (I := I)
  let _ : (y : Y.M) → InnerProductSpace ℝ (TangentSpace I y) := Y.riemInner (I := I)
  let _ : IsContinuousRiemannianBundle E (fun y : Y.M => TangentSpace I y) :=
    Y.riemBundle_cont (I := I)
  let _ : EMetricSpace Y.M := Y.emetricSpace (I := I)
  have : IsRiemannianManifold I Y.M := ⟨fun _ _ => rfl⟩
  let _ : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  let _ : ConnectedSpace Y.M := hF.connected
  let hEnorm : IsMetricNorm (I := I) Y.metric := by
    intro y v
    with_unfolding_all
      exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) Y.metric y v
  have hRm : ∀ y : Y.M, _root_.Manifold.riemannianEDist I x y < ENNReal.ofReal rho →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) Y.metric y 4
        (metricRm04At (I := I) Y.metric y)) ≤ K := by
    intro y hy
    have hyOf : riemannianEDistOf Y.metric x y < ENNReal.ofReal rho := by
      rw [riemannianEDistOf_eq_riemannianEDist Y.metric hEnorm]
      exact hy
    have hqy : riemannianEDistOf Y.metric (q i) y ≤ ENNReal.ofReal (D + 1) := by
      calc
        _ ≤ riemannianEDistOf Y.metric (q i) x + riemannianEDistOf Y.metric x y :=
          riemannianEDistOf_triangle Y.metric (q i) x y
        _ ≤ ENNReal.ofReal D + ENNReal.ofReal 1 :=
          add_le_add hx (hyOf.le.trans (ENNReal.ofReal_le_ofReal hrho1))
        _ = ENNReal.ofReal (D + 1) := (ENNReal.ofReal_add hD zero_le_one).symm
    have hbound := rmNorm_le_of_rescaled_distance_le F hF p (q i) y (htau i)
      (by linarith : 0 ≤ D + 1) (hbase i) hqy
    exact hbound.trans (by dsimp only [K]; linarith)
  have hRic : RicciBoundedBelow (I := I) Y.metric
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (0 : ℝ) ^ 2)) := by
    intro y v
    have hcone : metricAlgebraicCurvatureTensorAt (I := I) Y.metric y ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := Y.M) := by
      change metricAlgebraicCurvatureTensorAt
        (scaleMetric (tau i)⁻¹ (inv_pos.mpr (htau i)) (F.S.base.metric (-tau i))) y ∈ _
      rw [metricAlgebraicCurvatureTensorAt_scaleMetric]
      apply algebraicCurvatureOperatorNonnegativeCone.smul_mem ?_ (inv_pos.mpr (htau i)).le
      apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
        (I := I) (F.S.base.metric (-tau i)) y).mpr
      intro n c a b
      simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
        hF.nonnegativeCurvatureOperator (-tau i) (neg_nonpos.mpr (htau i).le) y n c a b
    have h := metricRicciAt_nonnegative_of_curvatureOperator_nonnegative Y.metric y hcone v
    change (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (0 : ℝ) ^ 2)) *
      Y.metric.inner y v v ≤ ricciTensor (I := I) Y.metric y v v
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), _root_.MulZeroClass.mul_zero, neg_zero, _root_.MulZeroClass.zero_mul,
      metricRicciAt_apply_eq_ricciTensor] using h
  have hvolOf := volume_lower_bound_of_rescaled_distance_le F hF p (q i) x
    (htau i) hD (hbase i) hx hsmall hsmall1 hsmallK
  have hvol : ENNReal.ofReal kappa * ENNReal.ofReal (R / 8) ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric
        {y : Y.M | _root_.Manifold.riemannianEDist I x y < ENNReal.ofReal (R / 8)} := by
    change ENNReal.ofReal kappa * ENNReal.ofReal (R / 8) ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure (I := I) (M := Y.M) Y.metric
        {y : Y.M | riemannianEDistOf Y.metric x y < ENNReal.ofReal (R / 8)} at hvolOf
    simpa only [riemannianEDistOf_eq_riemannianEDist Y.metric hEnorm] using hvolOf
  have hcgt := intrInj_ge_vol_of_ball Y.metric hEnorm x hK hR hRrho hRpi hRm
    (fun a ha haR => herror a ha (haR.trans hRj))
    (r₀ := R / 8) (s := R / 8) hsmall hsmall (by linarith) (by linarith)
    (q := 0) (by norm_num) hRic hvol
  have hhalf : R / 8 / 2 = R / 16 := by ring
  have hadd : R / 8 + R / 8 = R / 4 := by ring
  rw [hhalf, hadd] at hcgt
  have hinj := (selectedCGTInjRadius_le_quotient (E := E) hF.kappa_pos.le hR).trans hcgt
  exact hinj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_backwardSliceSequence_injRadius_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_backwardSliceSequence_injRadius_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_backwardSliceSequence_injRadius_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_backwardSliceSequence_injRadius_bound

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
