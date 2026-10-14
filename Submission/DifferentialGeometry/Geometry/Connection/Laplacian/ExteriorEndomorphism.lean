import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.ExteriorEndomorphism
import Submission.DifferentialGeometry.Geometry.Connection.Hessian.Map
import Submission.DifferentialGeometry.Geometry.Connection.Laplacian.Map

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.HomConnectionGen _root_.Submission.DifferentialGeometry.Geometry.Connection
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff _root_.RealInnerProductSpace _root_.BigOperators

namespace CovariantDerivative
open _root_.CovariantDerivative


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I 2 F V]

open _root_.CovariantDerivative _root_.CovariantDerivative.IsMetricCompatible in
theorem IsMetricCompatible.multilinear_hessian_endomorphismTensor
    {cov : CovariantDerivative I F V} [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hcov : cov.IsMetricCompatible) (k : ℕ)
    (base : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V k
    letI := Bundle.ExteriorPower.fiberBundle F V k
    letI := Bundle.ExteriorPower.vector_bundle F V k
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V k
    let c := cov.exteriorPower k
    let D := homBundleCovariantDerivativeGen I M (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x))
      (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) c c
    ∀ (R : ∀ x, (⋀[ℝ]^k (V x)) →L[ℝ] ⋀[ℝ]^k (V x)),
    ContMDiff I (I.prod 𝓘(ℝ, (⋀[ℝ]^k F) →L[ℝ] ⋀[ℝ]^k F)) 2
      (fun x => TotalSpace.mk' ((⋀[ℝ]^k F) →L[ℝ] ⋀[ℝ]^k F) x (R x)) →
    ∀ (x : M) (X Y : TangentSpace I x),
      (cov.multilinear (k + k)).hessian base
          (fun y => _root_.Submission.exteriorPower.endomorphismTensor k (R y)) x X Y =
        _root_.Submission.exteriorPower.endomorphismTensor k (D.hessian base R x X Y) := by
  dsimp only
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := Bundle.ExteriorPower.totalSpaceTopology F V k
  let := Bundle.ExteriorPower.fiberBundle F V k
  let := Bundle.ExteriorPower.vector_bundle F V k
  let := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V k
  let c := cov.exteriorPower k
  let hc : _root_.CovariantDerivative.ContMDiffCovariantDerivative c ∞ := cov.exteriorPower_contMDiff k
  let D := homBundleCovariantDerivativeGen I M (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x))
    (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) c c
  let hD : _root_.CovariantDerivative.ContMDiffCovariantDerivative D ∞ := inferInstance
  intro R hR x X Y
  exact hessian_map
    (F := (⋀[ℝ]^k F) →L[ℝ] ⋀[ℝ]^k F)
    (V := fun y => (⋀[ℝ]^k (V y)) →L[ℝ] ⋀[ℝ]^k (V y))
    (G := ContinuousMultilinearMap ℝ (fun _ : Fin (k + k) => F) ℝ)
    (W := Bundle.continuousMultilinearMap ℝ (k + k) F V)
    D hD (cov.multilinear (k + k)) (multilinear_contMDiff cov (k + k))
    (fun _ => _root_.Submission.exteriorPower.endomorphismTensorLinear k)
    (fun S hS y Z => hcov.multilinear_endomorphismTensor k S hS y Z) base R hR
    (Bundle.ExteriorPower.contMDiff_endomorphismTensor (IB := I) (n := 2) F V k R hR) x X Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.IsMetricCompatible.multilinear_hessian_endomorphismTensor then
    throwError "Refusing to shadow existing declaration CovariantDerivative.IsMetricCompatible.multilinear_hessian_endomorphismTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.IsMetricCompatible.multilinear_hessian_endomorphismTensor ``Submission.CovariantDerivative.IsMetricCompatible.multilinear_hessian_endomorphismTensor

end CovariantDerivative

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.HomConnectionGen _root_.Submission.DifferentialGeometry.Geometry.Connection
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff _root_.RealInnerProductSpace _root_.BigOperators

namespace CovariantDerivative
open _root_.CovariantDerivative


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I 1 F V]

open _root_.CovariantDerivative _root_.CovariantDerivative.IsMetricCompatible in
theorem IsMetricCompatible.rawBundleConnLap_multilinear_endomorphismTensor
    {cov : CovariantDerivative I F V} [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hcov : cov.IsMetricCompatible) (k : ℕ) (g : SmoothRiemannianMetric I M) :
    letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
    letI := Bundle.ExteriorPower.totalSpaceTopology F V k
    letI := Bundle.ExteriorPower.fiberBundle F V k
    letI := Bundle.ExteriorPower.vector_bundle F V k
    letI := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V k
    let c := cov.exteriorPower k
    let D := homBundleCovariantDerivativeGen I M (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x))
      (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) c c
    ∀ (R : ∀ x, (⋀[ℝ]^k (V x)) →L[ℝ] ⋀[ℝ]^k (V x)),
    ContMDiff I (I.prod 𝓘(ℝ, (⋀[ℝ]^k F) →L[ℝ] ⋀[ℝ]^k F)) 2
      (fun x => TotalSpace.mk' ((⋀[ℝ]^k F) →L[ℝ] ⋀[ℝ]^k F) x (R x)) →
    ∀ (x : M),
      rawBundleConnLap g (cov.multilinear (k + k))
          (fun y => _root_.Submission.exteriorPower.endomorphismTensor k (R y)) x =
        _root_.Submission.exteriorPower.endomorphismTensor k (rawBundleConnLap g D R x) := by
  dsimp only
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let := Bundle.ExteriorPower.totalSpaceTopology F V k
  let := Bundle.ExteriorPower.fiberBundle F V k
  let := Bundle.ExteriorPower.vector_bundle F V k
  let := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V k
  let c := cov.exteriorPower k
  let hc : _root_.CovariantDerivative.ContMDiffCovariantDerivative c ∞ := cov.exteriorPower_contMDiff k
  let D := homBundleCovariantDerivativeGen I M (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x))
    (⋀[ℝ]^k F) (fun x => ⋀[ℝ]^k (V x)) c c
  let hD : _root_.CovariantDerivative.ContMDiffCovariantDerivative D ∞ := inferInstance
  intro R hR x
  exact rawBundleConnLap_map
    (F := (⋀[ℝ]^k F) →L[ℝ] ⋀[ℝ]^k F)
    (V := fun y => (⋀[ℝ]^k (V y)) →L[ℝ] ⋀[ℝ]^k (V y))
    (G := ContinuousMultilinearMap ℝ (fun _ : Fin (k + k) => F) ℝ)
    (W := Bundle.continuousMultilinearMap ℝ (k + k) F V)
    D hD (cov.multilinear (k + k))
    (fun _ => _root_.Submission.exteriorPower.endomorphismTensorLinear k)
    (fun S hS y Z => hcov.multilinear_endomorphismTensor k S hS y Z) g R hR x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.IsMetricCompatible.rawBundleConnLap_multilinear_endomorphismTensor then
    throwError "Refusing to shadow existing declaration CovariantDerivative.IsMetricCompatible.rawBundleConnLap_multilinear_endomorphismTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.IsMetricCompatible.rawBundleConnLap_multilinear_endomorphismTensor ``Submission.CovariantDerivative.IsMetricCompatible.rawBundleConnLap_multilinear_endomorphismTensor

end CovariantDerivative
