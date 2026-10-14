import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Metric.TensorError
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedDomain

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

section MapLevel

variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
variable [T2Space N] [IsManifold I ∞ N] [SigmaCompactSpace N]

structure SmoothPullbackMetricTensor
    (Phi : M -> N) (h : SmoothRiemannianMetric I N) where
  tensor :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2
  tensor_apply :
    forall x : M, forall v : Fin 2 -> TangentSpace I x,
      tensor x v =
        h.inner (Phi x)
          (mfderiv I I Phi x (v 0))
          (mfderiv I I Phi x (v 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SmoothPullbackMetricTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SmoothPullbackMetricTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SmoothPullbackMetricTensor ``Submission.DifferentialGeometry.CheegerGromovCompactness.SmoothPullbackMetricTensor

structure MapMetricApproximation
    (K : Set M) (eps : Real) (p : Nat)
    (Phi : M -> N)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) where
  eps_pos : 0 < eps
  eps_lt_one : eps < 1
  smooth : ContMDiff I I (∞ : WithTop ℕ∞) Phi
  pullbackTensor : SmoothPullbackMetricTensor (I := I) Phi h
  c0_small :
    forall x : M, x ∈ K ->
      metricTensorErrorNorm (I := I) pullbackTensor.tensor g x <= eps
  cov_deriv_small :
    forall a : Nat, 1 <= a -> a <= p ->
      forall x : M, x ∈ K ->
        tensor02CovDerivNormWith (I := I) a pullbackTensor.tensor g g x <= eps

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximation ``Submission.DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximation

structure DiffeomorphMetricApproximation
    (K : Set M) (L : Set N) (eps : Real) (p : Nat)
    (Phi : M ≃ₘ⟮I, I⟯ N)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) where
  forward : MapMetricApproximation (I := I) K eps p (Phi : M -> N) g h
  reverse : MapMetricApproximation (I := I) L eps p (Phi.symm : N -> M) h g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.DiffeomorphMetricApproximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.DiffeomorphMetricApproximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.DiffeomorphMetricApproximation ``Submission.DifferentialGeometry.CheegerGromovCompactness.DiffeomorphMetricApproximation

structure MapMetricApproximationOn
    (K : Set M) (eps : Real) (p : Nat)
    (Phi : M -> N)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) where
  eps_pos : 0 < eps
  eps_lt_one : eps < 1
  smoothOn : ContMDiffOn I I (∞ : WithTop ℕ∞) Phi K
  pullback :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2
  pullback_apply :
    forall x : M, x ∈ K -> forall v : Fin 2 -> TangentSpace I x,
      pullback x v =
        h.inner (Phi x)
          (mfderiv I I Phi x (v 0))
          (mfderiv I I Phi x (v 1))
  c0_small :
    forall x : M, x ∈ K ->
      metricTensorErrorNorm (I := I) pullback g x <= eps
  cov_deriv_small :
    forall a : Nat, 1 <= a -> a <= p ->
      forall x : M, x ∈ K ->
        tensor02CovDerivNormWith (I := I) a pullback g g x <= eps

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationOn

structure PartialDiffeomorphMetricApproximation
    (K : Set M) (eps : Real) (p : Nat)
    (Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) where
  source_sub : K ⊆ Phi.source
  forward : MapMetricApproximationOn (I := I) K eps p (Phi : M -> N) g h
  reverse : MapMetricApproximationOn (I := I) ((Phi : M -> N) '' K) eps p (Phi.symm : N -> M) h g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximation ``Submission.DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximation

structure MapMetricApproximationBoundsOn
    (K : Set M) (c0 cov : Real) (p : Nat)
    (Phi : M -> N)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) where
  c0_nonneg : 0 <= c0
  cov_nonneg : 0 <= cov
  smoothOn : ContMDiffOn I I (∞ : WithTop ℕ∞) Phi K
  pullback :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2
  pullback_apply :
    forall x : M, x ∈ K -> forall v : Fin 2 -> TangentSpace I x,
      pullback x v =
        h.inner (Phi x)
          (mfderiv I I Phi x (v 0))
          (mfderiv I I Phi x (v 1))
  c0_small :
    forall x : M, x ∈ K ->
      metricTensorErrorNorm (I := I) pullback g x <= c0
  cov_small :
    forall a : Nat, 1 <= a -> a <= p ->
      forall x : M, x ∈ K ->
        tensor02CovDerivNormWith (I := I) a pullback g g x <= cov

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn

def MapMetricApproximationBoundsOn.toMetricApproximation
    {K : Set M} {c0 cov eps : Real} {p : Nat} {Phi : M -> N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : MapMetricApproximationBoundsOn (I := I) K c0 cov p Phi g h)
    (heps0 : 0 < eps) (heps1 : eps < 1)
    (hc0 : c0 <= eps) (hcov : cov <= eps) :
    MapMetricApproximationOn (I := I) K eps p Phi g h where
  eps_pos := heps0
  eps_lt_one := heps1
  smoothOn := D.smoothOn
  pullback := D.pullback
  pullback_apply := D.pullback_apply
  c0_small := fun x hx => le_trans (D.c0_small x hx) hc0
  cov_deriv_small := fun a h1 h2 x hx =>
    le_trans (D.cov_small a h1 h2 x hx) hcov

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.toMetricApproximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.toMetricApproximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.toMetricApproximation ``Submission.DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.toMetricApproximation

def MapMetricApproximationBoundsOn.toZeroOrderMetricApproximation
    {K : Set M} {c0 cov eps : ℝ} {p : ℕ} {Phi : M → N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : MapMetricApproximationBoundsOn (I := I) K c0 cov p Phi g h)
    (heps0 : 0 < eps) (heps1 : eps < 1) (hc0 : c0 ≤ eps) :
    MapMetricApproximationOn (I := I) K eps 0 Phi g h where
  eps_pos := heps0
  eps_lt_one := heps1
  smoothOn := D.smoothOn
  pullback := D.pullback
  pullback_apply := D.pullback_apply
  c0_small := fun x hx => (D.c0_small x hx).trans hc0
  cov_deriv_small := fun a ha hzero => False.elim (by omega)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.toZeroOrderMetricApproximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.toZeroOrderMetricApproximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.toZeroOrderMetricApproximation ``Submission.DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.toZeroOrderMetricApproximation

structure PartialDiffeomorphMetricApproximationBounds
    (K : Set M) (c0 cov : Real) (p : Nat)
    (Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) where
  source_sub : K ⊆ Phi.source
  forward : MapMetricApproximationBoundsOn (I := I) K c0 cov p (Phi : M -> N) g h
  reverse : MapMetricApproximationBoundsOn (I := I) ((Phi : M -> N) '' K) c0 cov p (Phi.symm : N -> M) h g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds ``Submission.DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds

def PartialDiffeomorphMetricApproximationBounds.toMetricApproximation
    {K : Set M} {c0 cov eps : Real} {p : Nat}
    {Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : PartialDiffeomorphMetricApproximationBounds (I := I) K c0 cov p Phi g h)
    (heps0 : 0 < eps) (heps1 : eps < 1)
    (hc0 : c0 <= eps) (hcov : cov <= eps) :
    PartialDiffeomorphMetricApproximation (I := I) K eps p Phi g h where
  source_sub := D.source_sub
  forward := D.forward.toMetricApproximation heps0 heps1 hc0 hcov
  reverse := D.reverse.toMetricApproximation heps0 heps1 hc0 hcov

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds.toMetricApproximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds.toMetricApproximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds.toMetricApproximation ``Submission.DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds.toMetricApproximation

def PartialDiffeomorphMetricApproximationBounds.toZeroOrderMetricApproximation
    {K : Set M} {c0 cov eps : ℝ} {p : ℕ}
    {Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : PartialDiffeomorphMetricApproximationBounds (I := I) K c0 cov p Phi g h)
    (heps0 : 0 < eps) (heps1 : eps < 1) (hc0 : c0 ≤ eps) :
    PartialDiffeomorphMetricApproximation (I := I) K eps 0 Phi g h where
  source_sub := D.source_sub
  forward := D.forward.toZeroOrderMetricApproximation heps0 heps1 hc0
  reverse := D.reverse.toZeroOrderMetricApproximation heps0 heps1 hc0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds.toZeroOrderMetricApproximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds.toZeroOrderMetricApproximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds.toZeroOrderMetricApproximation ``Submission.DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds.toZeroOrderMetricApproximation

def MapMetricApproximationOn.toSeparateBounds
    {K : Set M} {eps : Real} {p : Nat} {Phi : M -> N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : MapMetricApproximationOn (I := I) K eps p Phi g h) :
    MapMetricApproximationBoundsOn (I := I) K eps eps p Phi g h where
  c0_nonneg := le_of_lt D.eps_pos
  cov_nonneg := le_of_lt D.eps_pos
  smoothOn := D.smoothOn
  pullback := D.pullback
  pullback_apply := D.pullback_apply
  c0_small := D.c0_small
  cov_small := D.cov_deriv_small

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationOn
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationOn.toSeparateBounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationOn.toSeparateBounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationOn.toSeparateBounds ``Submission.DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationOn.toSeparateBounds

def PartialDiffeomorphMetricApproximation.toSeparateBounds
    {K : Set M} {eps : Real} {p : Nat}
    {Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : PartialDiffeomorphMetricApproximation (I := I) K eps p Phi g h) :
    PartialDiffeomorphMetricApproximationBounds (I := I) K eps eps p Phi g h where
  source_sub := D.source_sub
  forward := D.forward.toSeparateBounds
  reverse := D.reverse.toSeparateBounds

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximation
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximation.toSeparateBounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximation.toSeparateBounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximation.toSeparateBounds ``Submission.DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximation.toSeparateBounds

end MapLevel

end FixedDomain

end CheegerGromovCompactness
end DifferentialGeometry
