import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedLengthTimeComparison
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.LipschitzBound
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Potential.GradientIdentities

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData (I := I) ancientTimeInterval)
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

omit [I.Boundaryless] in
private theorem ancient_length_nonneg
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p x : F.M)
    {tau : ℝ} (htau : 0 < tau) : 0 ≤ redLength F.S 0 p x tau := by
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  apply div_nonneg _ (by positivity)
  apply lCost_nonneg_of_scalar_nonneg F.S 0 htau.le
  intro r hr w
  simpa only [zero_sub] using (hC (-r) (neg_nonpos.mpr hr.1) w).1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_length_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_length_nonneg target :: scope.openDecls } }

theorem normGradSqFun_ancient_redLength_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p x : F.M)
    {tau : ℝ} (htau : 0 < tau) :
    normGradSqFun (F.S.base.metric (-tau)) (fun y => redLength F.S 0 p y tau) x ≤
      3 * redLength F.S 0 p x tau / tau := by
  let _ : ConnectedSpace F.M := hF.connected
  let K : ℝ≥0 := ⟨Real.sqrt 3 / (2 * Real.sqrt tau), by positivity⟩
  have hLip (y z : F.M) :
      _root_.EDist.edist (Real.sqrt (redLength F.S 0 p y tau)) (Real.sqrt (redLength F.S 0 p z tau)) ≤
        (K : ENNReal) * riemannianEDistOf (F.S.base.metric (-tau)) y z := by
    have h := abs_sqrt_redLength_sub_le_rescaled_distance F hF p y z htau
    rw [edistOf_scale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
      Real.sqrt_inv] at h
    have h' : |Real.sqrt (redLength F.S 0 p y tau) - Real.sqrt (redLength F.S 0 p z tau)| ≤
        (K : ℝ) * (riemannianEDistOf (F.S.base.metric (-tau)) y z).toReal := by
      calc
        _ ≤ Real.sqrt 3 / 2 * ((Real.sqrt tau)⁻¹ *
            (riemannianEDistOf (F.S.base.metric (-tau)) y z).toReal) := h
        _ = _ := by
          change _ = (Real.sqrt 3 / (2 * Real.sqrt tau)) * _
          ring
    have he := ENNReal.ofReal_le_ofReal h'
    rw [ENNReal.ofReal_mul K.coe_nonneg,
      ENNReal.ofReal_toReal (riemannianEDistOf_ne_top (F.S.base.metric (-tau)) y z)] at he
    simpa only [edist_dist, Real.dist_eq, ENNReal.coe_nnreal_eq] using he
  have h := Geometry.Riemannian.grad_norm_sq_le_of_sqrt_lipschitz
    (F.S.base.metric (-tau)) (ancient_length_nonneg F hF p · htau) hLip x
  calc
    _ ≤ 4 * (K : ℝ) ^ 2 * redLength F.S 0 p x tau := h
    _ = _ := by
      change 4 * (Real.sqrt 3 / (2 * Real.sqrt tau)) ^ 2 * redLength F.S 0 p x tau = _
      rw [div_pow, mul_pow, Real.sq_sqrt htau.le, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      field_simp
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normGradSqFun_ancient_redLength_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normGradSqFun_ancient_redLength_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normGradSqFun_ancient_redLength_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normGradSqFun_ancient_redLength_le

theorem normGradSqFun_ancient_perelmanDensity_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p x : F.M)
    {tau : ℝ} (htau : 0 < tau) :
    normGradSqFun (F.S.base.metric (-tau))
      (Entropy.perelmanDensity (Module.finrank ℝ E) tau (fun y => redLength F.S 0 p y tau)) x ≤
      3 * redLength F.S 0 p x tau / tau *
        Entropy.perelmanDensity (Module.finrank ℝ E) tau (fun y => redLength F.S 0 p y tau) x ^ 2 := by
  have heq : normGradSqFun (F.S.base.metric (-tau))
      (Entropy.perelmanDensity (Module.finrank ℝ E) tau (fun y => redLength F.S 0 p y tau)) x =
      Entropy.perelmanDensity (Module.finrank ℝ E) tau (fun y => redLength F.S 0 p y tau) x ^ 2 *
        normGradSqFun (F.S.base.metric (-tau)) (fun y => redLength F.S 0 p y tau) x :=
    Entropy.density_grad_sq _ _ _ _ _
  rw [heq]
  calc
    _ ≤ Entropy.perelmanDensity (Module.finrank ℝ E) tau (fun y => redLength F.S 0 p y tau) x ^ 2 *
        (3 * redLength F.S 0 p x tau / tau) :=
      mul_le_mul_of_nonneg_left (normGradSqFun_ancient_redLength_le F hF p x htau) (sq_nonneg _)
    _ = _ := mul_comm _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normGradSqFun_ancient_perelmanDensity_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normGradSqFun_ancient_perelmanDensity_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normGradSqFun_ancient_perelmanDensity_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.normGradSqFun_ancient_perelmanDensity_le

theorem exists_ancient_perelmanDensity_gradient_le_linear_distance
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p o : F.M)
    {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ≥0, ∀ tau ∈ _root_.Set.Icc a b, ∀ x : F.M,
      Real.sqrt (normGradSqFun (F.S.base.metric (-tau))
        (Entropy.perelmanDensity (Module.finrank ℝ E) tau (fun y => redLength F.S 0 p y tau)) x) ≤
        C * (1 + (riemannianEDistOf (F.S.base.metric (-a)) o x).toReal) *
          Entropy.perelmanDensity (Module.finrank ℝ E) tau (fun y => redLength F.S 0 p y tau) x := by
  let A := Real.sqrt (redLength F.S 0 p o a)
  let B := Real.sqrt 3 / (2 * Real.sqrt a)
  let K := 1 + 3 * (b / a) ^ 2
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := by positivity
  have hK : 0 ≤ K := by positivity
  let C : ℝ≥0 := ⟨Real.sqrt (3 * K / a) * (A + B), by positivity⟩
  refine ⟨C, ?_⟩
  intro tau htau x
  have ht : 0 < tau := ha.trans_le htau.1
  let r := (riemannianEDistOf (F.S.base.metric (-a)) o x).toReal
  have hr : 0 ≤ r := ENNReal.toReal_nonneg
  have hroot : Real.sqrt (redLength F.S 0 p x a) ≤ A + B * r := by
    have hh := abs_sqrt_redLength_sub_le_rescaled_distance F hF p o x ha
    rw [edistOf_scale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Real.sqrt_inv] at hh
    have hcoef : Real.sqrt 3 / 2 * ((Real.sqrt a)⁻¹ * r) = B * r := by dsimp only [B]; ring
    change |A - Real.sqrt (redLength F.S 0 p x a)| ≤ Real.sqrt 3 / 2 * ((Real.sqrt a)⁻¹ * r) at hh
    rw [hcoef] at hh
    linarith only [(abs_le.mp hh).1]
  have hqa : redLength F.S 0 p x a ≤ (A + B * r) ^ 2 := by
    have hh := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr hroot
    rwa [Real.sq_sqrt (ancient_length_nonneg F hF p x ha)] at hh
  have hqt : redLength F.S 0 p x tau ≤ K * redLength F.S 0 p x a := by
    have hh := redLength_le_mul_on_rescaled_time_interval F hF p x ha
      (T := b / a) (t := tau / a)
      ⟨(le_div_iff₀ ha).mpr (by simpa only [one_mul] using htau.1),
        (div_le_div_iff_of_pos_right ha).mpr htau.2⟩
    simpa only [mul_div_cancel₀ _ ha.ne'] using hh
  have hlin : A + B * r ≤ (A + B) * (1 + r) := by
    nlinarith only [mul_nonneg hA hr, hB]
  have hq : redLength F.S 0 p x tau ≤ K * ((A + B) * (1 + r)) ^ 2 :=
    hqt.trans (mul_le_mul_of_nonneg_left
      (hqa.trans ((sq_le_sq₀ (by positivity) (by positivity)).mpr hlin)) hK)
  let u := Entropy.perelmanDensity (Module.finrank ℝ E) tau (fun y => redLength F.S 0 p y tau) x
  have hu : 0 ≤ u := (mul_pos (Entropy.prefactor_pos _ ht) (Real.exp_pos _)).le
  have hdiv : 3 * redLength F.S 0 p x tau / tau ≤ 3 * redLength F.S 0 p x tau / a :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (ancient_length_nonneg F hF p x ht)) ha htau.1
  have hg := normGradSqFun_ancient_perelmanDensity_le F hF p x ht
  have hsqC : ((C : ℝ) * (1 + r) * u) ^ 2 =
      (3 * K / a) * ((A + B) * (1 + r)) ^ 2 * u ^ 2 := by
    change (Real.sqrt (3 * K / a) * (A + B) * (1 + r) * u) ^ 2 = _
    simp only [mul_pow, Real.sq_sqrt (show 0 ≤ 3 * K / a by positivity)]
    ring
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  change normGradSqFun _ _ x ≤ ((C : ℝ) * (1 + r) * u) ^ 2
  rw [hsqC]
  have hq' : 3 * redLength F.S 0 p x tau / a ≤ (3 * K / a) * ((A + B) * (1 + r)) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hq (show 0 ≤ 3 / a by positivity)
    calc
      _ = (3 / a) * redLength F.S 0 p x tau := by ring
      _ ≤ (3 / a) * (K * ((A + B) * (1 + r)) ^ 2) := hh
      _ = _ := by ring
  exact hg.trans (mul_le_mul_of_nonneg_right (hdiv.trans hq') (sq_nonneg u))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_ancient_perelmanDensity_gradient_le_linear_distance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_ancient_perelmanDensity_gradient_le_linear_distance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_ancient_perelmanDensity_gradient_le_linear_distance ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_ancient_perelmanDensity_gradient_le_linear_distance

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
