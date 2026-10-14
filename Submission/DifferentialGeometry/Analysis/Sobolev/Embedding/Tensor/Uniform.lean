import Submission.DifferentialGeometry.Analysis.Sobolev.Embedding.Tensor.SharpC0JetSum
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Inner
import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Lowering
import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Commutation.ParallelNaturality
import Submission.DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Metric
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Integral
namespace L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def SmoothCcTensor.recast {g g' : SmoothRiemannianMetric I M} {r s : ℕ}
    (T : SmoothCcTensor g r s) : SmoothCcTensor g' r s where
  toSection := T.toSection
  hasCompactSupport := T.hasCompactSupport

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.recast then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.recast"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.recast ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.recast

@[simp] lemma SmoothCcTensor.recast_toSection
    {g g' : SmoothRiemannianMetric I M} {r s : ℕ} (T : SmoothCcTensor g r s) :
    (T.recast (g' := g')).toSection = T.toSection := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.recast_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.recast_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.recast_toSection ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.recast_toSection

end L2
end Integral
end DifferentialGeometry

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lowerAllUpper_zero_unit
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : SmoothCcTensor g 0 s) (w : Fin (0 + s) → E) :
    lowerAllUpperIndices (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)) w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
        (unitZeroSec (I := I) (M := M) x)
          (fun j : Fin s =>
            (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
              (w (Fin.natAdd 0 j))) := by
  let W0 : TensorRSSpace 0 s I x := W.toSection x
  change lowerAllUpperIndices (I := I) (M := M) g 0 s x
      (TensorRSSpace.toModel W0) w =
    (TensorRSSpace.toCLM W0) (unitZeroSec (I := I) (M := M) x)
      (fun j : Fin s =>
        (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
          (w (Fin.natAdd 0 j)))
  rw [lowerAllUpperIndices_apply, separableFormAt_zero]
  rw [show (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
      Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) from rfl]
  rw [← toModel_tensorRS_apply (I := I) (M := M) 0 s x W0
    (unitZeroSec (I := I) (M := M) x)]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.lowerAllUpper_zero_unit
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.lowerAllUpper_zero_unit target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma riemannianFiberNormSq0_eq_normSq0S
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (W : SmoothCcTensor g 0 s) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x (W.toSection x) =
      normSq0S (I := I) g x s
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
          (unitZeroSec (I := I) (M := M) x)) := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 s x
    (W.toSection x)]
  rw [show tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (W.toSection x)) (TensorRSSpace.toModel (W.toSection x)) =
      covariantTensorInnerPointwise (I := I) (M := M) (0 + s) g x
        (lowerAllUpperIndices (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel (W.toSection x)))
        (lowerAllUpperIndices (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel (W.toSection x))) from rfl]
  rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x (0 + s)
    basis hON _ _]
  rw [normSq0S_identity_eq_sum_sq (I := I) g x s basis
    (DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g basis hON) _]
  symm
  refine Fintype.sum_equiv
    (Equiv.arrowCongr (finCongr (Nat.zero_add s).symm) (Equiv.refl _)) _ _ ?_
  intro slots
  rw [component0S_apply]
  rw [lowerAllUpper_zero_unit (I := I) g s x W]
  rw [sq]
  congr 1 <;>
    (congr 1; funext a;
     simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq];
     rw [ContinuousLinearEquiv.symm_apply_apply];
     congr 1;
     apply Fin.ext;
     simp)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.riemannianFiberNormSq0_eq_normSq0S
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.riemannianFiberNormSq0_eq_normSq0S target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem fibreNormSq_cross_le
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hequiv : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (s : ℕ) (x : M) (T : SmoothCcTensor g₀ 0 s) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (T.toSection x) ≤
      Λ ^ s * riemannianFiberNormSq (I := I) (M := M) gBase 0 s x
        ((T.recast (g' := gBase)).toSection x) := by
  rw [riemannianFiberNormSq0_eq_normSq0S (I := I) g₀ s x T,
    riemannianFiberNormSq0_eq_normSq0S (I := I) gBase s x (T.recast (g' := gBase))]
  have h := (normSq0S_le_of_metric_equiv (I := I) gBase g₀ x s hΛ (hequiv x)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T.toSection x)
      (unitZeroSec (I := I) (M := M) x))).2
  rwa [zpow_natCast] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.fibreNormSq_cross_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.fibreNormSq_cross_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.fibreNormSq_cross_le ``Submission.DifferentialGeometry.PDE.RicciFlow.fibreNormSq_cross_le

def morreyUniformConst (Λ Cb Kjet : ℝ) (n s : ℕ) : ℝ :=
  Real.sqrt (Λ ^ s) * (Cb * ((n / 2 + 2 : ℕ) : ℝ) * Kjet)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.morreyUniformConst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.morreyUniformConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.morreyUniformConst ``Submission.DifferentialGeometry.PDE.RicciFlow.morreyUniformConst

lemma morreyUniformConst_nonneg {Λ Cb Kjet : ℝ} (hΛ : 0 ≤ Λ) (hCb : 0 ≤ Cb)
    (hKjet : 0 ≤ Kjet) (n s : ℕ) : 0 ≤ morreyUniformConst Λ Cb Kjet n s := by
  unfold morreyUniformConst
  have hp : (0 : ℝ) ≤ Λ ^ s := pow_nonneg hΛ s
  positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.morreyUniformConst_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.morreyUniformConst_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.morreyUniformConst_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.morreyUniformConst_nonneg

lemma morreyUniformConst_sq {Λ Cb Kjet : ℝ} (hΛ : 0 ≤ Λ) (n s : ℕ) :
    morreyUniformConst Λ Cb Kjet n s ^ 2 =
      Λ ^ s * (Cb ^ 2 * (((n / 2 + 2 : ℕ) : ℝ) ^ 2 * Kjet ^ 2)) := by
  unfold morreyUniformConst
  rw [mul_pow, Real.sq_sqrt (pow_nonneg hΛ s)]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.morreyUniformConst_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.morreyUniformConst_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.morreyUniformConst_sq ``Submission.DifferentialGeometry.PDE.RicciFlow.morreyUniformConst_sq

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] in
theorem fibreMorrey_uniform
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hequiv : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (s : ℕ) {Cb Kjet : ℝ}
    (hbase : ∀ (W : SmoothCcTensor gBase 0 s) (y : M),
      riemannianFiberNormSq (I := I) (M := M) gBase 0 s y (W.toSection y) ≤
        Cb ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) gBase 0 s j W‖ ^ 2)
    (hjet : ∀ (S : SmoothCcTensor g₀ 0 s),
      ∀ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
        ‖iteratedCovGrad (I := I) gBase 0 s j (S.recast (g' := gBase))‖ ≤
          Kjet * ∑ i ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 s i S‖)
    (T : SmoothCcTensor g₀ 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (T.toSection x) ≤
      morreyUniformConst Λ Cb Kjet (Module.finrank ℝ E) s ^ 2 *
        ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 s j T‖ ^ 2 := by
  classical
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ
  set w : ℕ := Module.finrank ℝ E / 2 + 2 with hw_def
  set Q : ℝ := ∑ i ∈ Finset.range w, ‖iteratedCovGrad (I := I) g₀ 0 s i T‖ ^ 2
    with hQ_def
  set S : ℝ := ∑ i ∈ Finset.range w, ‖iteratedCovGrad (I := I) g₀ 0 s i T‖
    with hS_def
  have hQ_nn : 0 ≤ Q := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hS_nn : 0 ≤ S := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hCS : S ^ 2 ≤ (w : ℝ) * Q := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range w)
      (f := fun i => ‖iteratedCovGrad (I := I) g₀ 0 s i T‖)
    simpa [hS_def, hQ_def] using h
  have hjet_sq : ∀ j ∈ Finset.range w,
      ‖iteratedCovGrad (I := I) gBase 0 s j (T.recast (g' := gBase))‖ ^ 2 ≤
        Kjet ^ 2 * S ^ 2 := by
    intro j hj
    have h := hjet T j hj
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    calc ‖iteratedCovGrad (I := I) gBase 0 s j (T.recast (g' := gBase))‖ ^ 2
        ≤ (Kjet * S) ^ 2 := h2
      _ = Kjet ^ 2 * S ^ 2 := by ring
  have hjet_sum : (∑ j ∈ Finset.range w,
      ‖iteratedCovGrad (I := I) gBase 0 s j (T.recast (g' := gBase))‖ ^ 2) ≤
      (w : ℝ) ^ 2 * Kjet ^ 2 * Q := by
    have hstep := Finset.sum_le_sum hjet_sq
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hstep
    have hmul : (w : ℝ) * (Kjet ^ 2 * S ^ 2) ≤
        (w : ℝ) * (Kjet ^ 2 * ((w : ℝ) * Q)) := by
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg w)
      exact mul_le_mul_of_nonneg_left hCS (sq_nonneg Kjet)
    calc (∑ j ∈ Finset.range w,
        ‖iteratedCovGrad (I := I) gBase 0 s j (T.recast (g' := gBase))‖ ^ 2)
        ≤ (w : ℝ) * (Kjet ^ 2 * S ^ 2) := hstep
      _ ≤ (w : ℝ) * (Kjet ^ 2 * ((w : ℝ) * Q)) := hmul
      _ = (w : ℝ) ^ 2 * Kjet ^ 2 * Q := by ring
  have hCb_sq_nn : (0 : ℝ) ≤ Cb ^ 2 := sq_nonneg Cb
  have hbase' :
      riemannianFiberNormSq (I := I) (M := M) gBase 0 s x
          ((T.recast (g' := gBase)).toSection x) ≤
        Cb ^ 2 * ((w : ℝ) ^ 2 * Kjet ^ 2 * Q) :=
    le_trans (hbase (T.recast (g' := gBase)) x)
      (mul_le_mul_of_nonneg_left hjet_sum hCb_sq_nn)
  have hfib := fibreNormSq_cross_le (I := I) gBase g₀ hΛ hequiv s x T
  have hpow_nn : (0 : ℝ) ≤ Λ ^ s := pow_nonneg hΛ0 s
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (T.toSection x)
      ≤ Λ ^ s * riemannianFiberNormSq (I := I) (M := M) gBase 0 s x
          ((T.recast (g' := gBase)).toSection x) := hfib
    _ ≤ Λ ^ s * (Cb ^ 2 * ((w : ℝ) ^ 2 * Kjet ^ 2 * Q)) :=
        mul_le_mul_of_nonneg_left hbase' hpow_nn
    _ = morreyUniformConst Λ Cb Kjet (Module.finrank ℝ E) s ^ 2 * Q := by
        rw [morreyUniformConst_sq hΛ0, ← hw_def]
        ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.fibreMorrey_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.fibreMorrey_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.fibreMorrey_uniform ``Submission.DifferentialGeometry.PDE.RicciFlow.fibreMorrey_uniform

def baseMorreyConst (gBase : SmoothRiemannianMetric I M) (r s : ℕ) : ℝ :=
  (exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
    (I := I) (M := M) gBase r s).choose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.baseMorreyConst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.baseMorreyConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.baseMorreyConst ``Submission.DifferentialGeometry.PDE.RicciFlow.baseMorreyConst

omit [BoundarylessManifold I M] in
lemma baseMorreyConst_nonneg (gBase : SmoothRiemannianMetric I M) (r s : ℕ) :
    0 ≤ baseMorreyConst (I := I) (M := M) gBase r s :=
  (exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
    (I := I) (M := M) gBase r s).choose_spec.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.baseMorreyConst_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.baseMorreyConst_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.baseMorreyConst_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.baseMorreyConst_nonneg

omit [BoundarylessManifold I M] in
lemma fibreNormSq_le_baseMorreyConst
    (gBase : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : SmoothCcTensor gBase r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) gBase r s x (W.toSection x) ≤
      baseMorreyConst (I := I) (M := M) gBase r s ^ 2 *
        ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) gBase r s j W‖ ^ 2 :=
  (exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
    (I := I) (M := M) gBase r s).choose_spec.2 W x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.fibreNormSq_le_baseMorreyConst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.fibreNormSq_le_baseMorreyConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.fibreNormSq_le_baseMorreyConst ``Submission.DifferentialGeometry.PDE.RicciFlow.fibreNormSq_le_baseMorreyConst

omit [BoundarylessManifold I M] in
theorem fibreMorrey_uniform_base
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hequiv : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (s : ℕ) {Kjet : ℝ}
    (hjet : ∀ (S : SmoothCcTensor g₀ 0 s),
      ∀ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
        ‖iteratedCovGrad (I := I) gBase 0 s j (S.recast (g' := gBase))‖ ≤
          Kjet * ∑ i ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 s i S‖)
    (T : SmoothCcTensor g₀ 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (T.toSection x) ≤
      morreyUniformConst Λ (baseMorreyConst (I := I) (M := M) gBase 0 s) Kjet
          (Module.finrank ℝ E) s ^ 2 *
        ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 s j T‖ ^ 2 :=
  fibreMorrey_uniform (I := I) gBase g₀ hΛ hequiv s
    (fibreNormSq_le_baseMorreyConst (I := I) gBase 0 s) hjet T x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.fibreMorrey_uniform_base then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.fibreMorrey_uniform_base"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.fibreMorrey_uniform_base ``Submission.DifferentialGeometry.PDE.RicciFlow.fibreMorrey_uniform_base

end DifferentialGeometry.PDE.RicciFlow

end
