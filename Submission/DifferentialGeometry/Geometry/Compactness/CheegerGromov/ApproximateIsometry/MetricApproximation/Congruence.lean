import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Monotonicity

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

open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.BigOperators _root_.ENNReal
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

section DataTransport

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [MetricSpace M] [Nonempty M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [T2Space N] [IsManifold I ∞ N]
  [SigmaCompactSpace N]

noncomputable def MapMetricApproximationOn.congr {K : Set M} {ε : Real} {p : Nat} {F F' : M → N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hdata : MapMetricApproximationOn (I := I) K ε p F g h)
    (hev : ∀ x ∈ K, F' =ᶠ[nhds x] F) :
    MapMetricApproximationOn (I := I) K ε p F' g h where
  eps_pos := hdata.eps_pos
  eps_lt_one := hdata.eps_lt_one
  smoothOn := hdata.smoothOn.congr (fun x hx => (hev x hx).self_of_nhds)
  pullback := hdata.pullback
  pullback_apply := by
    intro x hx v
    rw [(hev x hx).self_of_nhds, (hev x hx).mfderiv_eq]
    exact hdata.pullback_apply x hx v
  c0_small := hdata.c0_small
  cov_deriv_small := hdata.cov_deriv_small

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationOn.congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationOn.congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationOn.congr ``Submission.DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationOn.congr

noncomputable def MapMetricApproximationOn.congrEq {K : Set M} {ε : ℝ} {p : ℕ} {F F' : M → N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : MapMetricApproximationOn (I := I) K ε p F g h) (hEq : F' = F) :
    MapMetricApproximationOn (I := I) K ε p F' g h :=
  D.congr (fun _ _ => Filter.EventuallyEq.of_eq hEq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationOn.congrEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationOn.congrEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationOn.congrEq ``Submission.DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationOn.congrEq

noncomputable def MapMetricApproximationBoundsOn.congr {K : Set M} {c0 cov : ℝ} {p : ℕ} {F F' : M → N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : MapMetricApproximationBoundsOn (I := I) K c0 cov p F g h)
    (hev : ∀ x ∈ K, F' =ᶠ[nhds x] F) :
    MapMetricApproximationBoundsOn (I := I) K c0 cov p F' g h where
  c0_nonneg := D.c0_nonneg
  cov_nonneg := D.cov_nonneg
  smoothOn := D.smoothOn.congr (fun x hx => (hev x hx).self_of_nhds)
  pullback := D.pullback
  pullback_apply := by
    intro x hx v
    rw [(hev x hx).self_of_nhds, (hev x hx).mfderiv_eq]
    exact D.pullback_apply x hx v
  c0_small := D.c0_small
  cov_small := D.cov_small

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.congr ``Submission.DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.congr

noncomputable def MapMetricApproximationBoundsOn.congrEq {K : Set M} {c0 cov : ℝ} {p : ℕ} {F F' : M → N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : MapMetricApproximationBoundsOn (I := I) K c0 cov p F g h) (hEq : F' = F) :
    MapMetricApproximationBoundsOn (I := I) K c0 cov p F' g h :=
  D.congr (fun _ _ => Filter.EventuallyEq.of_eq hEq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.congrEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.congrEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.congrEq ``Submission.DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.congrEq

noncomputable def MapMetricApproximationBoundsOn.congrSet {K K' : Set M} {c0 cov : ℝ} {p : ℕ}
    {F : M → N} {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : MapMetricApproximationBoundsOn (I := I) K c0 cov p F g h) (hK : K' = K) :
    MapMetricApproximationBoundsOn (I := I) K' c0 cov p F g h := by
  subst hK
  exact D

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.congrSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.congrSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.congrSet ``Submission.DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationBoundsOn.congrSet

noncomputable def PartialDiffeomorphMetricApproximation.ofParts {K : Set M} {ε : ℝ} {p : ℕ}
    {Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hsrc : K ⊆ Φ.source)
    (forward : MapMetricApproximationOn (I := I) K ε p (Φ : M → N) g h)
    (reverse : MapMetricApproximationOn (I := I) ((Φ : M → N) '' K) ε p (Φ.symm : N → M) h g) :
    PartialDiffeomorphMetricApproximation (I := I) K ε p Φ g h where
  source_sub := hsrc
  forward := forward
  reverse := reverse

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximation.ofParts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximation.ofParts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximation.ofParts ``Submission.DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximation.ofParts

noncomputable def PartialDiffeomorphMetricApproximationBounds.ofParts {K : Set M} {c0 cov : ℝ} {p : ℕ}
    {Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hsrc : K ⊆ Φ.source)
    (forward : MapMetricApproximationBoundsOn (I := I) K c0 cov p (Φ : M → N) g h)
    (reverse : MapMetricApproximationBoundsOn (I := I) ((Φ : M → N) '' K) c0 cov p (Φ.symm : N → M) h g) :
    PartialDiffeomorphMetricApproximationBounds (I := I) K c0 cov p Φ g h where
  source_sub := hsrc
  forward := forward
  reverse := reverse

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds.ofParts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds.ofParts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds.ofParts ``Submission.DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds.ofParts

noncomputable def PartialDiffeomorphMetricApproximationBounds.congrSet {K K' : Set M} {c0 cov : ℝ} {p : ℕ}
    {Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : PartialDiffeomorphMetricApproximationBounds (I := I) K c0 cov p Φ g h) (hK : K' = K) :
    PartialDiffeomorphMetricApproximationBounds (I := I) K' c0 cov p Φ g h := by
  subst hK
  exact D

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds.congrSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds.congrSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds.congrSet ``Submission.DifferentialGeometry.CheegerGromovCompactness.PartialDiffeomorphMetricApproximationBounds.congrSet

end DataTransport

end CheegerGromovCompactness
end DifferentialGeometry
