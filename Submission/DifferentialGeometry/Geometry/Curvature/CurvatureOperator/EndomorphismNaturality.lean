import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Endomorphism
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.KernelNaturality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

noncomputable local instance twoFormFiniteDimensionalNaturality (x : M) :
    FiniteDimensional Real
      (TangentSpace I x [⋀^Fin 2]→L[Real] Real) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
    (Module.finBasis Real (TangentSpace I x))).finiteDimensional_of_finite

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.twoFormFiniteDimensionalNaturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.twoFormFiniteDimensionalNaturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.twoFormFiniteDimensionalNaturality ``Submission.DifferentialGeometry.Geometry.Curvature.twoFormFiniteDimensionalNaturality

omit [CompleteSpace E] [T2Space M] in
theorem twoFormMetricData_inner_congrLeft
    (gSource gTarget : SmoothRiemannianMetric I M) (x y : M)
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (hiso : ∀ u v, gTarget.inner y (e u) (e v) =
      gSource.inner x u v)
    (a b : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    (twoFormMetricData (I := I) gTarget y).inner
        (e.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
          (ι := Fin 2) a)
        (e.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
          (ι := Fin 2) b) =
      (twoFormMetricData (I := I) gSource x).inner a b := by
  rw [twoFormMetricData_inner, twoFormMetricData_inner]
  rw [← Tensor0SBundle.inner0S_tensor0SPullbackCLE
    (I := I) gSource gTarget x y 2 e hiso]
  rw [tensor0SPullbackCLE_twoFormTensorAt_congrLeft,
    tensor0SPullbackCLE_twoFormTensorAt_congrLeft]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.twoFormMetricData_inner_congrLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.twoFormMetricData_inner_congrLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.twoFormMetricData_inner_congrLeft ``Submission.DifferentialGeometry.Geometry.Curvature.twoFormMetricData_inner_congrLeft

omit [CompleteSpace E] [T2Space M] in
theorem curvatureOperatorEndomorphismAt_congrLeft
    (gSource gTarget : SmoothRiemannianMetric I M) (x y : M)
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (hiso : ∀ u v, gTarget.inner y (e u) (e v) =
      gSource.inner x u v)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) y)
    (a : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    e.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
        (ι := Fin 2)
        (curvatureOperatorEndomorphismAt (I := I) gSource x
          (algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e A) a) =
      curvatureOperatorEndomorphismAt (I := I) gTarget y A
        (e.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
          (ι := Fin 2) a) := by
  let F :
      (TangentSpace I x [⋀^Fin 2]→L[Real] Real) ≃L[Real]
        (TangentSpace I y [⋀^Fin 2]→L[Real] Real) :=
    e.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft (ι := Fin 2)
  apply (twoFormMetricData (I := I) gTarget y).flat.injective
  ext c
  let b := F.symm c
  have hc : F b = c := F.apply_symm_apply c
  calc
    (twoFormMetricData (I := I) gTarget y).inner
        (F (curvatureOperatorEndomorphismAt (I := I) gSource x
          (algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e A) a)) c =
      (twoFormMetricData (I := I) gSource x).inner
        (curvatureOperatorEndomorphismAt (I := I) gSource x
          (algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e A) a) b := by
            rw [← hc]
            exact twoFormMetricData_inner_congrLeft
              (I := I) gSource gTarget x y e hiso _ _
    _ = curvatureOperatorPairingAt (I := I) gSource x
        (algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e A) a b :=
      twoFormMetricData_inner_curvatureOperatorEndomorphismAt
        (I := I) gSource x _ a b
    _ = curvatureOperatorPairingAt (I := I) gTarget y A (F a) (F b) :=
      (curvatureOperatorPairingAt_congrLeft
        (I := I) gSource gTarget x y e hiso A a b).symm
    _ = (twoFormMetricData (I := I) gTarget y).inner
        (curvatureOperatorEndomorphismAt (I := I) gTarget y A (F a)) (F b) :=
      (twoFormMetricData_inner_curvatureOperatorEndomorphismAt
        (I := I) gTarget y A (F a) (F b)).symm
    _ = (twoFormMetricData (I := I) gTarget y).inner
        (curvatureOperatorEndomorphismAt (I := I) gTarget y A (F a)) c := by
      rw [hc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt_congrLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt_congrLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt_congrLeft ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt_congrLeft

omit [CompleteSpace E] [T2Space M] in
theorem curvatureOperatorImageAt_map_congrLeft
    (gSource gTarget : SmoothRiemannianMetric I M) (x y : M)
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (hiso : ∀ u v, gTarget.inner y (e u) (e v) =
      gSource.inner x u v)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) y) :
    Submodule.map
        (e.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft
          (ι := Fin 2)).toLinearMap
        (curvatureOperatorImageAt (I := I) gSource x
          (algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e A)) =
      curvatureOperatorImageAt (I := I) gTarget y A := by
  let F :
      (TangentSpace I x [⋀^Fin 2]→L[Real] Real) ≃L[Real]
        (TangentSpace I y [⋀^Fin 2]→L[Real] Real) :=
    e.toContinuousLinearEquiv.continuousAlternatingMapCongrLeft (ι := Fin 2)
  apply le_antisymm
  · rintro beta ⟨alpha, ⟨gamma, hgamma⟩, rfl⟩
    refine ⟨F gamma, ?_⟩
    change curvatureOperatorEndomorphismAt (I := I) gTarget y A (F gamma) = F alpha
    calc
      curvatureOperatorEndomorphismAt (I := I) gTarget y A (F gamma) =
          F (curvatureOperatorEndomorphismAt (I := I) gSource x
            (algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e A) gamma) :=
        (curvatureOperatorEndomorphismAt_congrLeft
          (I := I) gSource gTarget x y e hiso A gamma).symm
      _ = F alpha := congrArg F hgamma
  · intro beta hbeta
    obtain ⟨gamma, hgamma⟩ := hbeta
    refine ⟨F.symm beta, ?_, F.apply_symm_apply beta⟩
    refine ⟨F.symm gamma, ?_⟩
    apply F.injective
    calc
      F (curvatureOperatorEndomorphismAt (I := I) gSource x
          (algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e A) (F.symm gamma)) =
        curvatureOperatorEndomorphismAt (I := I) gTarget y A (F (F.symm gamma)) :=
          curvatureOperatorEndomorphismAt_congrLeft
            (I := I) gSource gTarget x y e hiso A (F.symm gamma)
      _ = curvatureOperatorEndomorphismAt (I := I) gTarget y A gamma := by
        rw [F.apply_symm_apply]
      _ = beta := hgamma
      _ = F (F.symm beta) := (F.apply_symm_apply beta).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt_map_congrLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt_map_congrLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt_map_congrLeft ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt_map_congrLeft

end DifferentialGeometry.Geometry.Curvature
