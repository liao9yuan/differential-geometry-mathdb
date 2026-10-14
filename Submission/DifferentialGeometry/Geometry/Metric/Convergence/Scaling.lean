import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Scaling
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance metricJetComplete : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricJetComplete
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.metricJetComplete target :: scope.openDecls } }
private local instance metricJetC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricJetC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.metricJetC1 target :: scope.openDecls } }
private local instance metricJetC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricJetC2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.metricJetC2 target :: scope.openDecls } }
private local instance metricJetCInfSucc : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  change IsManifold I ∞ M
  infer_instance

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricJetCInfSucc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.metricJetCInfSucc target :: scope.openDecls } }

private theorem metricJet_tensorField_scale (c : ℝ) (hc : 0 < c)
    (g : SmoothRiemannianMetric I M) :
    metricTensorField (I := I) (scaleMetric c hc g) = c • metricTensorField (I := I) g := by
  apply DFunLike.ext
  intro x
  apply Tensor0SBundle.tensor0SSpace_ext
  intro v
  simp only [metricTensorField_apply, scaleMetric_inner,
    ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.smul_apply, smul_eq_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricJet_tensorField_scale
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.metricJet_tensorField_scale target :: scope.openDecls } }

variable [T2Space M]

private theorem metricJet_covDeriv_scale_reference (c : ℝ) (hc : 0 < c)
    (g gRef : SmoothRiemannianMetric I M) (a : ℕ) :
    metricCovDeriv (I := I) g (scaleMetric c hc gRef) a =
      metricCovDeriv (I := I) g gRef a := by
  induction a with
  | zero => rfl
  | succ a ih =>
      rw [metricCovDeriv_succ, metricCovDeriv_succ, ih, metricCovDerivStep_scaleMetric]

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricJet_covDeriv_scale_reference
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.metricJet_covDeriv_scale_reference target :: scope.openDecls } }

private theorem metricJet_covDeriv_scale_metric (c : ℝ) (hc : 0 < c)
    (g gRef : SmoothRiemannianMetric I M) (a : ℕ) :
    metricCovDeriv (I := I) (scaleMetric c hc g) gRef a =
      c • metricCovDeriv (I := I) g gRef a := by
  induction a with
  | zero => exact metricJet_tensorField_scale c hc g
  | succ a ih =>
      rw [metricCovDeriv_succ, metricCovDeriv_succ, ih, metricCovDerivStep_smul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricJet_covDeriv_scale_metric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.metricJet_covDeriv_scale_metric target :: scope.openDecls } }

theorem metricCovDeriv_scale_all (c : ℝ) (hc : 0 < c)
    (g gRef : SmoothRiemannianMetric I M) (a : ℕ) :
    metricCovDeriv (I := I) (scaleMetric c hc g) (scaleMetric c hc gRef) a =
      c • metricCovDeriv (I := I) g gRef a := by
  rw [metricJet_covDeriv_scale_reference, metricJet_covDeriv_scale_metric]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricCovDeriv_scale_all then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricCovDeriv_scale_all"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricCovDeriv_scale_all ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricCovDeriv_scale_all

theorem metricDiffCovDerivAt_scale_all (c : ℝ) (hc : 0 < c)
    (gk gInf gRef : SmoothRiemannianMetric I M) (a : ℕ) (x : M) :
    metricDiffCovDerivAt (I := I) a
        (scaleMetric c hc gk) (scaleMetric c hc gInf) (scaleMetric c hc gRef) x =
      c • metricDiffCovDerivAt (I := I) a gk gInf gRef x := by
  unfold metricDiffCovDerivAt
  rw [metricCovDeriv_scale_all, metricCovDeriv_scale_all]
  simp only [ContMDiffSection.coe_smul, Pi.smul_apply, smul_sub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricDiffCovDerivAt_scale_all then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricDiffCovDerivAt_scale_all"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricDiffCovDerivAt_scale_all ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricDiffCovDerivAt_scale_all

theorem metricDerivNorm_scale_all (c : ℝ) (hc : 0 < c)
    (gk gInf gRef : SmoothRiemannianMetric I M) (a : ℕ) (x : M) :
    metricDerivNorm (I := I) a
        (scaleMetric c hc gk) (scaleMetric c hc gInf) (scaleMetric c hc gRef) x =
      Real.sqrt ((c⁻¹) ^ a) * metricDerivNorm (I := I) a gk gInf gRef x := by
  have hweight : (c⁻¹) ^ (a + 2) * c ^ 2 = (c⁻¹) ^ a := by
    calc
      (c⁻¹) ^ (a + 2) * c ^ 2 = (c⁻¹) ^ a * ((c⁻¹ * c) ^ 2) := by
        rw [pow_add, mul_pow]
        ring
      _ = (c⁻¹) ^ a := by rw [inv_mul_cancel₀ hc.ne']; simp only [one_pow, mul_one]
  unfold metricDerivNorm
  rw [metricDiffCovDerivAt_scale_all, normSq0S_scale, normSq0S_smul,
    ← mul_assoc, hweight, Real.sqrt_mul (pow_nonneg (inv_nonneg.mpr hc.le) a)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm_scale_all then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm_scale_all"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm_scale_all ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm_scale_all

def metricJetScaleLoss (c : ℝ) (p : ℕ) : ℝ :=
  1 + ∑ a ∈ Finset.range (p + 1), Real.sqrt ((c⁻¹) ^ a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricJetScaleLoss then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricJetScaleLoss"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricJetScaleLoss ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricJetScaleLoss

theorem metricJetScaleLoss_pos (c : ℝ) (p : ℕ) : 0 < metricJetScaleLoss c p := by
  dsimp only [metricJetScaleLoss]
  exact add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricJetScaleLoss_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricJetScaleLoss_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricJetScaleLoss_pos ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricJetScaleLoss_pos

private theorem metricJet_weight_le_loss (c : ℝ) {a p : ℕ} (ha : a ≤ p) :
    Real.sqrt ((c⁻¹) ^ a) ≤ metricJetScaleLoss c p := by
  have hsum := Finset.single_le_sum
    (fun j (_hj : j ∈ Finset.range (p + 1)) => Real.sqrt_nonneg ((c⁻¹) ^ j))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le ha))
  dsimp only [metricJetScaleLoss]
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricJet_weight_le_loss
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.metricJet_weight_le_loss target :: scope.openDecls } }

theorem metricDerivNormSupOn_scale_all_le (c : ℝ) (hc : 0 < c)
    {K : Set M} (hK : IsCompact K) (p : ℕ)
    (gk gInf gRef : SmoothRiemannianMetric I M) :
    metricDerivNormSupOn (I := I) K p
        (scaleMetric c hc gk) (scaleMetric c hc gInf) (scaleMetric c hc gRef) ≤
      metricJetScaleLoss c p * metricDerivNormSupOn (I := I) K p gk gInf gRef := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp [metricDerivNormSupOn]
  · obtain ⟨x₀, hx₀⟩ := hne
    unfold metricDerivNormSupOn
    apply csSup_le
    · exact ⟨_, 0, Nat.zero_le p, x₀, hx₀, rfl⟩
    · rintro r ⟨a, hap, x, hx, rfl⟩
      change metricDerivNorm (I := I) a
          (scaleMetric c hc gk) (scaleMetric c hc gInf) (scaleMetric c hc gRef) x ≤
        metricJetScaleLoss c p * metricDerivNormSupOn (I := I) K p gk gInf gRef
      rw [metricDerivNorm_scale_all]
      exact (mul_le_mul_of_nonneg_right (metricJet_weight_le_loss c hap)
        (Real.sqrt_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (derivNorm_le_sup hK hap gk gInf gRef hx)
          (metricJetScaleLoss_pos c p).le)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricDerivNormSupOn_scale_all_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricDerivNormSupOn_scale_all_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricDerivNormSupOn_scale_all_le ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricDerivNormSupOn_scale_all_le

theorem metricCPConvOn_scale_all (c : ℝ) (hc : 0 < c)
    {K : Set M} (hK : IsCompact K) (p : ℕ)
    (gSeq : ℕ → SmoothRiemannianMetric I M) (gInf gRef : SmoothRiemannianMetric I M)
    (hconv : MetricCPConvergenceOn (I := I) K p gSeq gInf gRef) :
    MetricCPConvergenceOn (I := I) K p (fun k => scaleMetric c hc (gSeq k))
      (scaleMetric c hc gInf) (scaleMetric c hc gRef) := by
  intro epsilon hepsilon
  let A := metricJetScaleLoss c p
  have hA : 0 < A := metricJetScaleLoss_pos c p
  obtain ⟨k₀, hk₀⟩ := hconv (epsilon / A) (div_pos hepsilon hA)
  refine ⟨k₀, fun k hk => ?_⟩
  calc
    metricDerivNormSupOn (I := I) K p
        (scaleMetric c hc (gSeq k)) (scaleMetric c hc gInf) (scaleMetric c hc gRef) ≤
      A * metricDerivNormSupOn (I := I) K p (gSeq k) gInf gRef :=
        metricDerivNormSupOn_scale_all_le c hc hK p (gSeq k) gInf gRef
    _ < A * (epsilon / A) := mul_lt_mul_of_pos_left (hk₀ k hk) hA
    _ = epsilon := by field_simp [hA.ne']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricCPConvOn_scale_all then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricCPConvOn_scale_all"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricCPConvOn_scale_all ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricCPConvOn_scale_all

theorem metricCInfConvOnCompacts_scale_all (c : ℝ) (hc : 0 < c)
    (gSeq : ℕ → SmoothRiemannianMetric I M) (gInf gRef : SmoothRiemannianMetric I M)
    (hconv : MetricCInfConvergenceOnCompacts (I := I) gSeq gInf gRef) :
    MetricCInfConvergenceOnCompacts (I := I) (fun k => scaleMetric c hc (gSeq k))
      (scaleMetric c hc gInf) (scaleMetric c hc gRef) := by
  intro K hK p
  exact metricCPConvOn_scale_all c hc hK p gSeq gInf gRef (hconv K hK p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricCInfConvOnCompacts_scale_all then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricCInfConvOnCompacts_scale_all"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricCInfConvOnCompacts_scale_all ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricCInfConvOnCompacts_scale_all

end DifferentialGeometry.CheegerGromovCompactness

end
