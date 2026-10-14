import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.SlotCurry.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Submission.DifferentialGeometry.Analysis.Elliptic

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
theorem tensor0S_uncurry_cons_eval_of_expansion
    {s : ℕ} {x : M} (T : Tensor0SSpace (s + 1) I x)
    {n : ℕ} (c : Fin n → ℝ) (e : Fin n → TangentSpace I x)
    (w : TangentSpace I x) (hw : w = ∑ a : Fin n, c a • e a)
    (m : Fin s → E) :
    Tensor0SSpace.toModel T
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x w) m) =
      ∑ a : Fin n, c a • Tensor0SSpace.toModel
        (tensor0SCurry (I := I) (M := M) s x T (e a)) m := by
  classical
  simp only [Tensor0SSpace.toModel_apply_model_vector]
  let wm : Fin (s + 1) → E :=
    Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x w) m
  have hcons :
      (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
        (wm i)) =
        Fin.cons w
          (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m i)) := by
    unfold wm
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  rw [hcons]
  change Tensor0SSpace.eval T
      (Fin.cons w
        (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m i))) =
    ∑ a : Fin n, c a • Tensor0SSpace.eval
      (tensor0SCurry (I := I) (M := M) s x T (e a))
        (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m i))
  rw [← TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := s) (b := x)
    T w (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m i))]
  rw [hw]
  rw [map_sum (tensor0SCurry (I := I) (M := M) s x T) (fun a => c a • e a) Finset.univ]
  simp only [Tensor0SSpace.eval_eq]
  rw [sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [(tensor0SCurry (I := I) (M := M) s x T).map_smul (c a) (e a)]
  rw [smul_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor0S_uncurry_cons_eval_of_expansion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor0S_uncurry_cons_eval_of_expansion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor0S_uncurry_cons_eval_of_expansion ``Submission.DifferentialGeometry.Geometry.Curvature.tensor0S_uncurry_cons_eval_of_expansion

omit [FiniteDimensional ℝ E] in
theorem tensor0S_uncurry_cons_eval_orthonormal
    (g : SmoothRiemannianMetric I M) {s : ℕ} {x : M} (T : Tensor0SSpace (s + 1) I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hv_expand : ∀ u : TangentSpace I x, u = ∑ a : Fin n, g.inner x (e a) u • e a)
    (w : TangentSpace I x) (m : Fin s → E) :
    Tensor0SSpace.toModel T
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x w) m) =
      ∑ a : Fin n, g.inner x (e a) w • Tensor0SSpace.toModel
        (tensor0SCurry (I := I) (M := M) s x T (e a)) m :=
  tensor0S_uncurry_cons_eval_of_expansion (I := I) (M := M) T
    (fun a => g.inner x (e a) w) e w (hv_expand w) m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor0S_uncurry_cons_eval_orthonormal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor0S_uncurry_cons_eval_orthonormal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor0S_uncurry_cons_eval_orthonormal ``Submission.DifferentialGeometry.Geometry.Curvature.tensor0S_uncurry_cons_eval_orthonormal

omit [FiniteDimensional ℝ E] in
theorem tensor0S_uncurry_cons_eval_of_expansion_natural
    {s : ℕ} {x : M} (T : Tensor0SSpace (s + 1) I x)
    {n : ℕ} (c : Fin n → ℝ) (e : Fin n → TangentSpace I x)
    (w : TangentSpace I x) (hw : w = ∑ a : Fin n, c a • e a)
    (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.eval T (Fin.cons w m) =
      ∑ a : Fin n, c a • Tensor0SSpace.eval
        (tensor0SCurry (I := I) (M := M) s x T (e a)) m := by
  classical
  rw [← TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := s) (b := x)
    T w m]
  rw [hw]
  rw [map_sum (tensor0SCurry (I := I) (M := M) s x T)
    (fun a => c a • e a) Finset.univ]
  simp only [Tensor0SSpace.eval_eq]
  rw [sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [(tensor0SCurry (I := I) (M := M) s x T).map_smul (c a) (e a)]
  rw [smul_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor0S_uncurry_cons_eval_of_expansion_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor0S_uncurry_cons_eval_of_expansion_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor0S_uncurry_cons_eval_of_expansion_natural ``Submission.DifferentialGeometry.Geometry.Curvature.tensor0S_uncurry_cons_eval_of_expansion_natural

omit [FiniteDimensional ℝ E] in
theorem tensor0S_uncurry_cons_eval_orthonormal_natural
    (g : SmoothRiemannianMetric I M) {s : ℕ} {x : M} (T : Tensor0SSpace (s + 1) I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (hv_expand : ∀ u : TangentSpace I x, u = ∑ a : Fin n, g.inner x (e a) u • e a)
    (w : TangentSpace I x) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.eval T (Fin.cons w m) =
      ∑ a : Fin n, g.inner x (e a) w • Tensor0SSpace.eval
        (tensor0SCurry (I := I) (M := M) s x T (e a)) m :=
  tensor0S_uncurry_cons_eval_of_expansion_natural (I := I) (M := M) T
    (fun a => g.inner x (e a) w) e w (hv_expand w) m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor0S_uncurry_cons_eval_orthonormal_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor0S_uncurry_cons_eval_orthonormal_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor0S_uncurry_cons_eval_orthonormal_natural ``Submission.DifferentialGeometry.Geometry.Curvature.tensor0S_uncurry_cons_eval_orthonormal_natural

lemma slot0Curry_coframeS_eq_tensor0S_curry
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (T : TensorRSSpace 0 (s + 1) I x) (a : Fin n) :
    (slot0Curry (I := I) (M := M) g x s e K₀ T a :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x)
        (coframeS (I := I) (M := M) g x 0 e K₀) =
      tensor0SCurry (I := I) (M := M) s x
        ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
          (coframeS (I := I) (M := M) g x 0 e K₀)) (e a) := by
  classical
  rw [slot0Curry_apply (I := I) (M := M) g x s e K₀ T a
    (coframeS (I := I) (M := M) g x 0 e K₀)]
  have hscalar : tensor00Scalar (I := I) (M := M) x
      (coframeS (I := I) (M := M) g x 0 e K₀) = 1 := by
    rw [tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0),
      coframeS_apply (I := I) (M := M) g x 0 e K₀]
    simp
  rw [hscalar, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.slot0Curry_coframeS_eq_tensor0S_curry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.slot0Curry_coframeS_eq_tensor0S_curry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.slot0Curry_coframeS_eq_tensor0S_curry ``Submission.DifferentialGeometry.Geometry.Curvature.slot0Curry_coframeS_eq_tensor0S_curry

theorem tensorRS_section_uncurry_cons_eval_slot0Curry
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (hv_expand : ∀ u : TangentSpace I x, u = ∑ a : Fin n, g.inner x (e a) u • e a)
    (T : TensorRSSpace 0 (s + 1) I x)
    (w : TangentSpace I x) (m : Fin s → E) :
    Tensor0SSpace.toModel
        ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
          (coframeS (I := I) (M := M) g x 0 e K₀))
          (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x w) m) =
      ∑ a : Fin n, g.inner x (e a) w • Tensor0SSpace.toModel
        ((slot0Curry (I := I) (M := M) g x s e K₀ T a :
            Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x)
          (coframeS (I := I) (M := M) g x 0 e K₀)) m := by
  classical
  rw [tensor0S_uncurry_cons_eval_orthonormal (I := I) (M := M) g
    ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
      (coframeS (I := I) (M := M) g x 0 e K₀)) e hv_expand w m]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [slot0Curry_coframeS_eq_tensor0S_curry (I := I) (M := M) g x s e K₀ T a]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensorRS_section_uncurry_cons_eval_slot0Curry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensorRS_section_uncurry_cons_eval_slot0Curry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensorRS_section_uncurry_cons_eval_slot0Curry ``Submission.DifferentialGeometry.Geometry.Curvature.tensorRS_section_uncurry_cons_eval_slot0Curry

theorem tensor0S_eq_sum_slot0_uncurry
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ (T : Tensor0SSpace (s + 1) I x) (w : TangentSpace I x)
        (m : Fin s → E),
        Tensor0SSpace.toModel T
            (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x w) m) =
          ∑ a : Fin n, g.inner x (e a) w • Tensor0SSpace.toModel
            (tensor0SCurry (I := I) (M := M) s x T (e a)) m := by
  classical
  obtain ⟨n, e, _bse, hn, _hbse, horth, _hpars, hv_expand, _hrepr⟩ :=
    exists_tangent_orthonormalBasisS_with_norm_sum (I := I) (M := M) g s x
  refine ⟨n, e, hn, horth, fun T w m => ?_⟩
  exact tensor0S_uncurry_cons_eval_orthonormal (I := I) (M := M) g T e hv_expand w m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor0S_eq_sum_slot0_uncurry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor0S_eq_sum_slot0_uncurry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor0S_eq_sum_slot0_uncurry ``Submission.DifferentialGeometry.Geometry.Curvature.tensor0S_eq_sum_slot0_uncurry

theorem tensorRS_section_eq_sum_slot0Curry_uncurry
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ (T : TensorRSSpace 0 (s + 1) I x) (w : TangentSpace I x)
        (m : Fin s → E),
        Tensor0SSpace.toModel
            ((T : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x)
              (coframeS (I := I) (M := M) g x 0 e K₀))
              (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x w) m) =
          ∑ a : Fin n, g.inner x (e a) w • Tensor0SSpace.toModel
            ((slot0Curry (I := I) (M := M) g x s e K₀ T a :
                Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x)
              (coframeS (I := I) (M := M) g x 0 e K₀)) m := by
  classical
  obtain ⟨n, e, _bse, hn, _hbse, horth, _hpars, hv_expand, _hrepr⟩ :=
    exists_tangent_orthonormalBasisS_with_norm_sum (I := I) (M := M) g s x
  refine ⟨n, e, fun k => k.elim0, hn, horth, fun T w m => ?_⟩
  exact tensorRS_section_uncurry_cons_eval_slot0Curry (I := I) (M := M) g s x e
    (fun k => k.elim0) hv_expand T w m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensorRS_section_eq_sum_slot0Curry_uncurry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensorRS_section_eq_sum_slot0Curry_uncurry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensorRS_section_eq_sum_slot0Curry_uncurry ``Submission.DifferentialGeometry.Geometry.Curvature.tensorRS_section_eq_sum_slot0Curry_uncurry

end Curvature
end Geometry
end DifferentialGeometry
