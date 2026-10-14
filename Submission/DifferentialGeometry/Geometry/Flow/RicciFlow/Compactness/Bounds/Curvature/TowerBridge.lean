import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Covariant
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.BoundedGeometry

import Submission.DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Product
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.HeatEquation
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import Submission.DifferentialGeometry.Geometry.Curvature.Components.RicciTrace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M]

private def curvEquiv : (m : Nat) → Fin (4 + m) ≃ Fin (m + 4)
  | 0 => Equiv.refl _
  | (m + 1) => frontExtendEquiv (curvEquiv m)

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.curvEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.curvEquiv target :: scope.openDecls } }

omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem curv_apply_iterCov
    (g : SmoothRiemannianMetric I M) :
    ∀ (m : Nat) (x : M) (v : Fin (m + 4) → TangentSpace I x),
      curvCovDeriv (I := I) (M := M) g m x v =
        (ContinuousMultilinearMap.domDomCongr (curvEquiv m)
          ((iterCov (I := I) g 4
            (DifferentialGeometry.Geometry.Curvature.metricRm04
              (I := I) (M := M) g) m) x)) v := by
  intro m
  induction m with
  | zero =>
      intro x v
      rfl
  | succ m ih =>
      intro x v
      have hfield :
          curvCovDeriv (I := I) (M := M) g m =
            MultilinearSection.domDomCongr
              (𝕜 := Real) (F := E) (IB := I) (E := TangentSpace I)
              (∞ : WithTop ℕ∞) (curvEquiv m)
              (iterCov (I := I) g 4
                (DifferentialGeometry.Geometry.Curvature.metricRm04
                  (I := I) (M := M) g) m) := by
        refine DFunLike.ext _ _ (fun y => ?_)
        refine ContinuousMultilinearMap.ext (fun w => ?_)
        exact ih y w
      calc
        curvCovDeriv (I := I) (M := M) g (m + 1) x v =
            curvCovDerivStep (I := I) g m
              (curvCovDeriv (I := I) (M := M) g m) x v :=
          congrArg (fun A => A x v)
            (curvCovDeriv_succ (I := I) (M := M) g m)
        _ = covStep (I := I) g (m + 4)
              (curvCovDeriv (I := I) (M := M) g m) x v :=
          congrArg (fun A => A x v)
            (curvStep_eq_covStep (I := I) (M := M) g m _)
        _ = covStep (I := I) g (m + 4)
              (MultilinearSection.domDomCongr
                (𝕜 := Real) (F := E) (IB := I) (E := TangentSpace I)
                (∞ : WithTop ℕ∞) (curvEquiv m)
                (iterCov (I := I) g 4
                  (DifferentialGeometry.Geometry.Curvature.metricRm04
                    (I := I) (M := M) g) m)) x v :=
          congrArg (fun A => covStep (I := I) g (m + 4) A x v) hfield
        _ = (MultilinearSection.domDomCongr
              (𝕜 := Real) (F := E) (IB := I) (E := TangentSpace I)
              (∞ : WithTop ℕ∞) (frontExtendEquiv (curvEquiv m))
              (covStep (I := I) g (4 + m)
                (iterCov (I := I) g 4
                  (DifferentialGeometry.Geometry.Curvature.metricRm04
                    (I := I) (M := M) g) m))) x v :=
          congrArg (fun A => A x v)
            (covStep_domDomCongr (I := I) g (curvEquiv m) _)
        _ = (ContinuousMultilinearMap.domDomCongr (curvEquiv (m + 1))
              ((iterCov (I := I) g 4
                (DifferentialGeometry.Geometry.Curvature.metricRm04
                  (I := I) (M := M) g) (m + 1)) x)) v := by
          rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.curv_apply_iterCov
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.curv_apply_iterCov target :: scope.openDecls } }

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem curvCovDeriv_normSq_eq
    (g : SmoothRiemannianMetric I M) (m : Nat) (x : M) :
    normSq0S (I := I) g x (m + 4) (curvCovDeriv (I := I) (M := M) g m x) =
      normSq0S (I := I) g x (4 + m)
        ((iterCov (I := I) g 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04
            (I := I) (M := M) g) m) x) := by
  classical
  have hfiber :
      curvCovDeriv (I := I) (M := M) g m x =
        ContinuousMultilinearMap.domDomCongr (curvEquiv m)
          ((iterCov (I := I) g 4
            (DifferentialGeometry.Geometry.Curvature.metricRm04
              (I := I) (M := M) g) m) x) := by
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    exact curv_apply_iterCov (I := I) (M := M) g m x v
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  have hinv :
      MetricInverseInBasis (I := I) g x basis
        (identityInvMetric
          (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h' := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h' i j
  rw [hfiber]
  exact normSq0S_domDomCongr (I := I) g x basis hinv (curvEquiv m)
    ((iterCov (I := I) g 4
      (DifferentialGeometry.Geometry.Curvature.metricRm04
        (I := I) (M := M) g) m) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.curvCovDeriv_normSq_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.curvCovDeriv_normSq_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.curvCovDeriv_normSq_eq ``Submission.DifferentialGeometry.CheegerGromovCompactness.curvCovDeriv_normSq_eq

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem curvNormSq_eq
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (k : Nat) (t : Real) (x : M) :
    curvDerivNormSq (I := I) (M := M) k (S.base.metric t) x =
      nablaKRm04NormSqIntrinsic (I := I) S k t x := by
  classical
  unfold curvDerivNormSq nablaKRm04NormSqIntrinsic
  rw [curvCovDeriv_normSq_eq (I := I) (M := M) (S.base.metric t) k x]
  exact congrArg
    (fun A => normSq0S (I := I) (S.base.metric t) x (4 + k) (A x))
    (nablaKRm_eq_iterCov (I := I) S t k).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.curvNormSq_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.curvNormSq_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.curvNormSq_eq ``Submission.DifferentialGeometry.CheegerGromovCompactness.curvNormSq_eq

end CheegerGromovCompactness
end DifferentialGeometry
