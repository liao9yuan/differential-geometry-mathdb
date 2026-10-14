import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Algebra.ContractionLeibniz
import Submission.DifferentialGeometry.Tensor.RSTensor.Algebra.Product

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace Tensor0SBundle

open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]
variable [T2Space M]

omit [IsManifold I 2 M] [T2Space M] in
theorem normSq0S_product {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M) {s q : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q) :
    normSq0S (I := I) g x (s + q)
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B x)
      = normSq0S (I := I) g x s (A x) * normSq0S (I := I) g x q (B x) := by
  classical
  rw [normSq0S_identity_eq_sum_sq (I := I) g x (s + q) basis hinv,
    normSq0S_identity_eq_sum_sq (I := I) g x s basis hinv,
    normSq0S_identity_eq_sum_sq (I := I) g x q basis hinv,
    Finset.sum_mul_sum,
    ← Fintype.sum_prod_type
      (f := fun p : (Fin s -> Idx) × (Fin q -> Idx) =>
        component0S (I := I) basis (A x) p.1 ^ 2
          * component0S (I := I) basis (B x) p.2 ^ 2)]
  refine Fintype.sum_equiv
    { toFun := fun slots : Fin (s + q) -> Idx =>
        (slots ∘ Fin.castAdd q, slots ∘ Fin.natAdd s)
      invFun := fun p => Fin.addCases p.1 p.2
      left_inv := fun slots => by
        funext i
        refine Fin.addCases (fun a => ?_) (fun b => ?_) i
        · simp only [Fin.addCases_left, Function.comp_apply]
        · simp only [Fin.addCases_right, Function.comp_apply]
      right_inv := fun p => by
        obtain ⟨f, h⟩ := p
        refine Prod.ext ?_ ?_
        · funext a; simp only [Function.comp_apply, Fin.addCases_left]
        · funext b; simp only [Function.comp_apply, Fin.addCases_right] }
    _ _ ?_
  intro slots
  have hprod :
      component0S (I := I) basis
          (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B x)
          slots
        = component0S (I := I) basis (A x) (slots ∘ Fin.castAdd q)
          * component0S (I := I) basis (B x) (slots ∘ Fin.natAdd s) := by
    rw [component0S_apply, component0S_apply, component0S_apply,
      tensor0SField_product_apply]
    rfl
  rw [hprod, mul_pow]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.normSq0S_product then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.normSq0S_product"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.normSq0S_product ``Submission.DifferentialGeometry.Tensor0SBundle.normSq0S_product

omit [IsManifold I 2 M] [T2Space M] in
theorem normSq0S_prod {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M) {s q : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : Tensor0SSpace s I x) (B : Tensor0SSpace q I x) :
    normSq0S (I := I) g x (s + q)
        (Tensor0SSpace.product A B)
      = normSq0S (I := I) g x s A * normSq0S (I := I) g x q B := by
  classical
  rw [normSq0S_identity_eq_sum_sq (I := I) g x (s + q) basis hinv,
    normSq0S_identity_eq_sum_sq (I := I) g x s basis hinv,
    normSq0S_identity_eq_sum_sq (I := I) g x q basis hinv,
    Finset.sum_mul_sum,
    ← Fintype.sum_prod_type
      (f := fun p : (Fin s -> Idx) × (Fin q -> Idx) =>
        component0S (I := I) basis A p.1 ^ 2 *
          component0S (I := I) basis B p.2 ^ 2)]
  refine Fintype.sum_equiv
    { toFun := fun slots : Fin (s + q) -> Idx =>
        (slots ∘ Fin.castAdd q, slots ∘ Fin.natAdd s)
      invFun := fun p => Fin.addCases p.1 p.2
      left_inv := fun slots => by
        funext i
        refine Fin.addCases (fun a => ?_) (fun b => ?_) i
        · simp only [Fin.addCases_left, Function.comp_apply]
        · simp only [Fin.addCases_right, Function.comp_apply]
      right_inv := fun p => by
        obtain ⟨f, h⟩ := p
        refine Prod.ext ?_ ?_
        · funext a
          simp only [Function.comp_apply, Fin.addCases_left]
        · funext b
          simp only [Function.comp_apply, Fin.addCases_right] }
    _ _ ?_
  intro slots
  have hprod :
      component0S (I := I) basis
          (Tensor0SSpace.product A B) slots
        = component0S (I := I) basis A (slots ∘ Fin.castAdd q) *
          component0S (I := I) basis B (slots ∘ Fin.natAdd s) := by
    rw [component0S_apply, component0S_apply, component0S_apply,
      Tensor0SSpace.product_apply]
    rfl
  rw [hprod, mul_pow]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.normSq0S_prod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.normSq0S_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.normSq0S_prod ``Submission.DifferentialGeometry.Tensor0SBundle.normSq0S_prod

omit [IsManifold I 2 M] [T2Space M] in
theorem normSq0S_domDomCongr {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M) {s s' : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (e : Fin s ≃ Fin s') (T : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s' (T.domDomCongr e) = normSq0S (I := I) g x s T := by
  classical
  rw [normSq0S_identity_eq_sum_sq (I := I) g x s' basis hinv,
    normSq0S_identity_eq_sum_sq (I := I) g x s basis hinv]
  refine Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl Idx)) _ _ ?_
  intro w
  simp only [component0S_apply, Equiv.arrowCongr_apply, Equiv.symm_symm,
    Equiv.coe_refl, Function.comp, id_eq]
  rw [Tensor0SSpace.domDomCongr_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.normSq0S_domDomCongr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.normSq0S_domDomCongr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.normSq0S_domDomCongr ``Submission.DifferentialGeometry.Tensor0SBundle.normSq0S_domDomCongr

end Tensor0SBundle
end DifferentialGeometry
