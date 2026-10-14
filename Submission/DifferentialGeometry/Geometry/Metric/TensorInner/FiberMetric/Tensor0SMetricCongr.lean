import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace Tensor0SBundle

open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem inner0S_identity_eq_sum {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A B : Tensor0SSpace s I x) :
    inner0S (I := I) g x s A B =
      ∑ slots : Fin s -> Idx,
        component0S (I := I) basis A slots * component0S (I := I) basis B slots := by
  rw [inner0S_eq_coord (I := I) g x s basis (identityInvMetric (Idx := Idx)) hinv,
    coordInner0S_identity_eq_sum (I := I) (x := x) s A B basis]
  apply Finset.sum_congr rfl
  intro slots _
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Tensor0SBundle.inner0S_identity_eq_sum then
    throwError "Refusing to shadow existing declaration Tensor0SBundle.inner0S_identity_eq_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `Tensor0SBundle.inner0S_identity_eq_sum ``Submission.Tensor0SBundle.inner0S_identity_eq_sum

theorem inner0S_domDomCongr {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M) {s s' : Nat}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (e : Fin s ≃ Fin s') (A B : Tensor0SSpace s I x) :
    inner0S (I := I) g x s' (A.domDomCongr e) (B.domDomCongr e) =
      inner0S (I := I) g x s A B := by
  classical
  rw [inner0S_identity_eq_sum (I := I) g x s' basis hinv,
    inner0S_identity_eq_sum (I := I) g x s basis hinv]
  refine Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl Idx)) _ _ ?_
  intro w
  simp only [component0S_apply, Equiv.arrowCongr_apply, Equiv.symm_symm,
    Equiv.coe_refl, Function.comp, id_eq]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Tensor0SBundle.inner0S_domDomCongr then
    throwError "Refusing to shadow existing declaration Tensor0SBundle.inner0S_domDomCongr"
  Lean.modifyEnv fun env => Lean.addAlias env `Tensor0SBundle.inner0S_domDomCongr ``Submission.Tensor0SBundle.inner0S_domDomCongr

end Tensor0SBundle
