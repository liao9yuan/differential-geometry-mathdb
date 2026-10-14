import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.InverseMetric
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

section Raise

variable {Idx : Type*} [Fintype Idx] {x : M}

def raiseAt (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x)) (a : Idx -> Real) :
    TangentSpace I x :=
  ∑ p : Idx, (∑ l : Idx, basisInvMetric (I := I) g x basis p l * a l) • basis p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.raiseAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.raiseAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.raiseAt ``Submission.DifferentialGeometry.PDE.RicciFlow.raiseAt

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem raiseAt_eq (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x)) (a : Idx -> Real) :
    raiseAt (I := I) g x basis a =
      ∑ p : Idx, (∑ l : Idx, basisInvMetric (I := I) g x basis p l * a l) • basis p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.raiseAt_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.raiseAt_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.raiseAt_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.raiseAt_eq

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem raiseAt_lower (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x)) (V : TangentSpace I x) :
    raiseAt (I := I) g x basis (fun l : Idx => g.inner x V (basis l)) = V := by
  classical
  have hcoord : ∀ p : Idx,
      (∑ l : Idx, basisInvMetric (I := I) g x basis p l * g.inner x V (basis l)) =
        basis.repr V p := by
    intro p
    set S : TangentSpace I x :=
      (tangentFlatEquiv (I := I) g x).symm (basis.coord p) with hS
    have hb : ∀ l : Idx, basisInvMetric (I := I) g x basis p l = basis.repr S l := by
      intro l
      rw [hS]
      exact basis.coord_apply l _
    have hsum : (∑ l : Idx, basis.repr S l * g.inner x V (basis l)) = g.inner x V S := by
      conv_rhs => rw [← basis.sum_repr S]
      rw [map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [map_smul, smul_eq_mul]
    have hflat : g.inner x V S = basis.repr V p := by
      have h1 : g.inner x V S = g.inner x S V := g.symm x V S
      have h2 : g.inner x S V = tangentFlatEquiv (I := I) g x S V :=
        (tangentFlatEquiv_apply (I := I) g x S V).symm
      have h3 : tangentFlatEquiv (I := I) g x S = basis.coord p := by
        rw [hS]
        exact (tangentFlatEquiv (I := I) g x).apply_symm_apply _
      rw [h1, h2, h3]
      exact basis.coord_apply p V
    calc (∑ l : Idx, basisInvMetric (I := I) g x basis p l * g.inner x V (basis l))
        = ∑ l : Idx, basis.repr S l * g.inner x V (basis l) :=
          Finset.sum_congr rfl fun l _ => by rw [hb l]
      _ = g.inner x V S := hsum
      _ = basis.repr V p := hflat
  rw [raiseAt_eq]
  calc (∑ p : Idx,
        (∑ l : Idx, basisInvMetric (I := I) g x basis p l * g.inner x V (basis l)) • basis p)
      = ∑ p : Idx, basis.repr V p • basis p :=
        Finset.sum_congr rfl fun p _ => by rw [hcoord p]
    _ = V := basis.sum_repr V

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.raiseAt_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.raiseAt_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.raiseAt_lower ``Submission.DifferentialGeometry.PDE.RicciFlow.raiseAt_lower

end Raise

def sharpFlat (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →ₗ[Real] TangentSpace I x :=
  (tangentFlatEquiv (I := I) g₂ x).symm.toLinearMap ∘ₗ
    (tangentFlatEquiv (I := I) g₁ x).toLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.sharpFlat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.sharpFlat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.sharpFlat ``Submission.DifferentialGeometry.PDE.RicciFlow.sharpFlat

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp]
theorem sharpFlat_self (g : SmoothRiemannianMetric I M) (x : M) (W : TangentSpace I x) :
    sharpFlat (I := I) g g x W = W := by
  change (tangentFlatEquiv (I := I) g x).symm
    ((tangentFlatEquiv (I := I) g x) W) = W
  exact (tangentFlatEquiv (I := I) g x).symm_apply_apply W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.sharpFlat_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.sharpFlat_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.sharpFlat_self ``Submission.DifferentialGeometry.PDE.RicciFlow.sharpFlat_self

section Pairing

variable [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [I.Boundaryless]

omit [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem inner_sharpFlat (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (V W : TangentSpace I x) :
    g₁.inner x V (sharpFlat (I := I) g₂ g₁ x W) = g₂.inner x V W := by
  have hflat : tangentFlatEquiv (I := I) g₁ x (sharpFlat (I := I) g₂ g₁ x W) =
      tangentFlatEquiv (I := I) g₂ x W := by
    change tangentFlatEquiv (I := I) g₁ x
      ((tangentFlatEquiv (I := I) g₁ x).symm
        ((tangentFlatEquiv (I := I) g₂ x) W)) = _
    exact (tangentFlatEquiv (I := I) g₁ x).apply_symm_apply _
  calc g₁.inner x V (sharpFlat (I := I) g₂ g₁ x W)
      = g₁.inner x (sharpFlat (I := I) g₂ g₁ x W) V :=
        g₁.symm x V (sharpFlat (I := I) g₂ g₁ x W)
    _ = tangentFlatEquiv (I := I) g₁ x (sharpFlat (I := I) g₂ g₁ x W) V :=
        (tangentFlatEquiv_apply (I := I) g₁ x _ V).symm
    _ = tangentFlatEquiv (I := I) g₂ x W V := by rw [hflat]
    _ = g₂.inner x W V := tangentFlatEquiv_apply (I := I) g₂ x W V
    _ = g₂.inner x V W := g₂.symm x W V

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.inner_sharpFlat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.inner_sharpFlat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.inner_sharpFlat ``Submission.DifferentialGeometry.PDE.RicciFlow.inner_sharpFlat

end Pairing

end DifferentialGeometry.PDE.RicciFlow

end
