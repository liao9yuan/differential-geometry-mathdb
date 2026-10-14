import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.SlotCurry.Defs
import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Commutation.ParallelNaturality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def tensor0SToTensorRS {s : ℕ} (x : M) (C : Tensor0SSpace s I x) :
    TensorRSSpace 0 s I x :=
  (tensor00Scalar (I := I) (M := M) x).smulRight C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensor0SToTensorRS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensor0SToTensorRS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensor0SToTensorRS ``Submission.DifferentialGeometry.Analysis.Elliptic.tensor0SToTensorRS


lemma tensor0SAsRS_apply {s : ℕ} (x : M) (C : Tensor0SSpace s I x)
    (τ : Tensor0SSpace 0 I x) :
    (tensor0SToTensorRS (I := I) (M := M) x C :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) τ =
      tensor00Scalar (I := I) (M := M) x τ • C := by
  change ((tensor00Scalar (I := I) (M := M) x).smulRight C) τ = _
  rw [ContinuousLinearMap.smulRight_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensor0SAsRS_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensor0SAsRS_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensor0SAsRS_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.tensor0SAsRS_apply


lemma coframeS_zero_eq_unitZeroSec
    (g : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n) :
    coframeS (I := I) (M := M) g x 0 e K₀ = unitZeroSec (I := I) (M := M) x := by
  classical
  apply tensor0SSpace_ext (𝕜 := ℝ) 0 x
  intro u
  rw [coframeS_apply (I := I) (M := M) g x 0 e K₀ u]
  rw [Fin.prod_univ_zero]
  change 1 = Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x)
    (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (u i))
  rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.constOfIsEmpty_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.coframeS_zero_eq_unitZeroSec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.coframeS_zero_eq_unitZeroSec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.coframeS_zero_eq_unitZeroSec ``Submission.DifferentialGeometry.Analysis.Elliptic.coframeS_zero_eq_unitZeroSec

private lemma tensor01_comp
    (g : SmoothRiemannianMetric I M) (x : M)
    (W : TensorRSSpace 0 1 I x) {n : ℕ}
    (e : Fin n → TangentSpace I x) (J : Fin 1 → Fin n)
    (K₀ : Fin 0 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x 0 1 W n e K₀ J =
      Tensor0SSpace.eval
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from W)
          (unitZeroSec (I := I) (M := M) x))
        (fun i : Fin 1 ↦ e (J i)) := by
  classical
  unfold fiberNormSqComponent
  rw [show ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun l : Fin 0 ↦ g.inner x (e (K₀ l))) : Tensor0SSpace 0 I x) =
      coframeS (I := I) (M := M) g x 0 e K₀ from rfl]
  rw [coframeS_zero_eq_unitZeroSec (I := I) (M := M) g x e K₀]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.tensor01_comp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.tensor01_comp target :: scope.openDecls } }

theorem sq_unit_eval_le
    (g : SmoothRiemannianMetric I M) (x : M)
    (W : TensorRSSpace 0 1 I x) (X : TangentSpace I x) :
    (Tensor0SSpace.eval
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from W)
          (unitZeroSec (I := I) (M := M) x))
        (fun _ : Fin 1 ↦ X)) ^ 2 ≤
      g.inner x X X *
        riemannianFiberNormSq (I := I) (M := M) g 0 1 x W := by
  classical
  obtain ⟨n, e, _bse, _hn, _hbse, _horth, hpars, hexpand, hriemannianFiberNormSq⟩ :=
    exists_tangent_orthonormalBasisS_with_norm_sum (I := I) (M := M) g 1 x
  let vec : Fin 1 → TangentSpace I x := fun _ ↦ X
  let vecE : Fin 1 → E := fun i ↦
    tangentSpaceModelContinuousLinearEquiv (I := I) x (vec i)
  let eE : Fin n → E := fun j ↦
    tangentSpaceModelContinuousLinearEquiv (I := I) x (e j)
  let B : ContinuousMultilinearMap ℝ (fun _ : Fin 1 ↦ E) ℝ :=
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from W)
        (unitZeroSec (I := I) (M := M) x))
  let coef : (Fin 1 → Fin n) → ℝ := fun J ↦
    ∏ i : Fin 1, g.inner x (e (J i)) (vec i)
  let comp : (Fin 1 → Fin n) → ℝ := fun J ↦
    B (fun i : Fin 1 ↦ eE (J i))
  have hvalue : B vecE = ∑ J : Fin 1 → Fin n, coef J * comp J := by
    have hrw : B vecE = B (fun i : Fin 1 ↦
        ∑ j : Fin n, g.inner x (e j) (vec i) • eE j) := by
      congr 1
      funext i
      simpa only [vecE, eE, map_sum, map_smul] using
        congrArg (tangentSpaceModelContinuousLinearEquiv (I := I) x) (hexpand (vec i))
    rw [hrw, ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl (fun J _ ↦ ?_)
    dsimp only [coef, comp]
    simpa only [smul_eq_mul] using
      B.map_smul_univ
        (fun i : Fin 1 ↦ g.inner x (e (J i)) (vec i))
        (fun i : Fin 1 ↦ eE (J i))
  have hcs : (∑ J : Fin 1 → Fin n, coef J * comp J) ^ 2 ≤
      (∑ J : Fin 1 → Fin n, coef J ^ 2) *
        ∑ J : Fin 1 → Fin n, comp J ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ coef comp
  have hcoef : (∑ J : Fin 1 → Fin n, coef J ^ 2) = g.inner x X X := by
    have hpow (J : Fin 1 → Fin n) : coef J ^ 2 =
        ∏ i : Fin 1, g.inner x (e (J i)) (vec i) ^ 2 := by
      dsimp only [coef]
      rw [← Finset.prod_pow]
    rw [Finset.sum_congr rfl (fun J _ ↦ hpow J)]
    rw [show (∑ J : Fin 1 → Fin n,
          ∏ i : Fin 1, g.inner x (e (J i)) (vec i) ^ 2) =
        ∑ J ∈ Fintype.piFinset (fun _ : Fin 1 ↦ (Finset.univ : Finset (Fin n))),
          ∏ i : Fin 1, g.inner x (e (J i)) (vec i) ^ 2 by
      rw [Fintype.piFinset_univ]]
    rw [← Finset.prod_univ_sum
      (fun _ : Fin 1 ↦ (Finset.univ : Finset (Fin n)))
      (fun i j ↦ g.inner x (e j) (vec i) ^ 2)]
    rw [Fin.prod_univ_one, hpars (vec 0)]
  have hcomp : (∑ J : Fin 1 → Fin n, comp J ^ 2) =
      riemannianFiberNormSq (I := I) (M := M) g 0 1 x W := by
    rw [hriemannianFiberNormSq W]
    rw [Fintype.sum_unique (fun K : Fin 0 → Fin n ↦
      ∑ J : Fin 1 → Fin n,
        fiberNormSqSummand (I := I) (M := M) g x 0 1 W n e K J)]
    refine Finset.sum_congr rfl (fun J _ ↦ ?_)
    dsimp only [comp]
    rw [fiberNormSqSummand_eq_component_sq,
      tensor01_comp (I := I) (M := M) g x W e J (_root_.Inhabited.default : Fin 0 → Fin n)]
    rw [Tensor0SSpace.toModel_apply_model_vector]
    simp only [eE, ContinuousLinearEquiv.symm_apply_apply, Tensor0SSpace.eval_eq]
  change (B vecE) ^ 2 ≤ _
  rw [hvalue]
  calc
    (∑ J : Fin 1 → Fin n, coef J * comp J) ^ 2
        ≤ (∑ J : Fin 1 → Fin n, coef J ^ 2) *
            ∑ J : Fin 1 → Fin n, comp J ^ 2 := hcs
    _ = g.inner x X X *
        riemannianFiberNormSq (I := I) (M := M) g 0 1 x W := by
      rw [hcoef, hcomp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.sq_unit_eval_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.sq_unit_eval_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.sq_unit_eval_le ``Submission.DifferentialGeometry.Analysis.Elliptic.sq_unit_eval_le


lemma slot0Curry_eq_tensor0SToTensorRS_curry_unitZeroSec
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (T : TensorRSSpace 0 (s + 1) I x) (a : Fin n) :
    slot0Curry (I := I) (M := M) g x s e K₀ T a =
      tensor0SToTensorRS (I := I) (M := M) x
        (tensor0SCurry (I := I) (M := M) s x
          ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
            (unitZeroSec (I := I) (M := M) x)) (e a)) := by
  unfold slot0Curry tensor0SToTensorRS
  rw [coframeS_zero_eq_unitZeroSec (I := I) (M := M) g x e K₀]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.slot0Curry_eq_tensor0SToTensorRS_curry_unitZeroSec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.slot0Curry_eq_tensor0SToTensorRS_curry_unitZeroSec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.slot0Curry_eq_tensor0SToTensorRS_curry_unitZeroSec ``Submission.DifferentialGeometry.Analysis.Elliptic.slot0Curry_eq_tensor0SToTensorRS_curry_unitZeroSec

theorem riemannianFiberNormSq_succ_eq_sum_tensor0SCurry
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (T : TensorRSSpace 0 (s + 1) I x) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x T =
        ∑ a : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (tensor0SToTensorRS (I := I) (M := M) x
              (tensor0SCurry (I := I) (M := M) s x
                ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
                  (unitZeroSec (I := I) (M := M) x)) (e a))) := by
  classical
  obtain ⟨n, e, K₀, hn, hsplit⟩ :=
    riemannianFiberNormSq_succ_eq_sum_slot0Curry (I := I) (M := M) g s x T
  refine ⟨n, e, hn, ?_⟩
  rw [hsplit]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [slot0Curry_eq_tensor0SToTensorRS_curry_unitZeroSec (I := I) (M := M) g x s e K₀ T a]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_succ_eq_sum_tensor0SCurry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_succ_eq_sum_tensor0SCurry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_succ_eq_sum_tensor0SCurry ``Submission.DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_succ_eq_sum_tensor0SCurry

theorem riemannianFiberNormSq_three_eq_sum_tensor0SCurry
    (g : SmoothRiemannianMetric I M) (x : M)
    (T : TensorRSSpace 0 3 I x) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x T =
        ∑ a : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (tensor0SToTensorRS (I := I) (M := M) x
              (tensor0SCurry (I := I) (M := M) 2 x
                ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x)
                  (unitZeroSec (I := I) (M := M) x)) (e a))) :=
  riemannianFiberNormSq_succ_eq_sum_tensor0SCurry (I := I) (M := M) g 2 x T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_three_eq_sum_tensor0SCurry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_three_eq_sum_tensor0SCurry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_three_eq_sum_tensor0SCurry ``Submission.DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_three_eq_sum_tensor0SCurry

end Elliptic
end Analysis
end DifferentialGeometry

namespace DifferentialGeometry.Integral.Connection

open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

abbrev tensor0SAsRS {s : ℕ} (x : M) (C : Tensor0SSpace s I x) :
    TensorRSSpace 0 s I x :=
  tensor0SToTensorRS (I := I) (M := M) x C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.tensor0SAsRS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.tensor0SAsRS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.tensor0SAsRS ``Submission.DifferentialGeometry.Integral.Connection.tensor0SAsRS

lemma slot0Curry_eq_tensor0SAsRS_curry_unitZeroSec
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (T : TensorRSSpace 0 (s + 1) I x) (a : Fin n) :
    slot0Curry (I := I) (M := M) g x s e K₀ T a =
      tensor0SAsRS (I := I) (M := M) x
        (tensor0SCurry (I := I) (M := M) s x
          ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
            (unitZeroSec (I := I) (M := M) x)) (e a)) :=
  slot0Curry_eq_tensor0SToTensorRS_curry_unitZeroSec
    (I := I) (M := M) g x s e K₀ T a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.slot0Curry_eq_tensor0SAsRS_curry_unitZeroSec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.slot0Curry_eq_tensor0SAsRS_curry_unitZeroSec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.slot0Curry_eq_tensor0SAsRS_curry_unitZeroSec ``Submission.DifferentialGeometry.Integral.Connection.slot0Curry_eq_tensor0SAsRS_curry_unitZeroSec

end DifferentialGeometry.Integral.Connection

end
