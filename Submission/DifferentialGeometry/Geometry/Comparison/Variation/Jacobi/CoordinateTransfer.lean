import Submission.DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Coordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

open _root_.Set _root_.Function _root_.Manifold _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Topology _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.AlongCurve
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E']
  [NeZero (Module.finrank ℝ E')]
variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [I'.Boundaryless]
variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' ∞ M'] [T2Space M'] [SigmaCompactSpace M']

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M]
  [NeZero (Module.finrank ℝ E')]
  [SigmaCompactSpace M'] in
theorem jacobi_coord_xfer
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (g' : SmoothRiemannianMetric I' M') (γ' : ℝ → M') {b : ℝ}
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (F : ι → ∀ s : ℝ, TangentSpace I (γ s))
    (F' : ι → ∀ s : ℝ, TangentSpace I' (γ' s))
    (Y : ∀ s : ℝ, TangentSpace I (γ s))
    (Y' : ∀ s : ℝ, TangentSpace I' (γ' s))
    {C : ℝ} (hC : 0 ≤ C)
    (hγ : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b, ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hγ' : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b, ContMDiffAt 𝓘(ℝ, ℝ) I' n γ' t)
    (hFdiff : ∀ i, ∀ t ∈ _root_.Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (F i) t) t)
    (hFdiff' : ∀ i, ∀ t ∈ _root_.Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I') γ' (F' i) t) t)
    (hFpar : ∀ i, ∀ t ∈ _root_.Set.Icc (0 : ℝ) b,
      covDerivAlong (I := I) g γ (F i) t = 0)
    (hFpar' : ∀ i, ∀ t ∈ _root_.Set.Icc (0 : ℝ) b,
      covDerivAlong (I := I') g' γ' (F' i) t = 0)
    (hON : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b, ∀ i j,
      g.inner (γ t) (F i t) (F j t) = if i = j then (1 : ℝ) else 0)
    (hON' : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b, ∀ i j,
      g'.inner (γ' t) (F' i t) (F' j t) = if i = j then (1 : ℝ) else 0)
    (hcard : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I (γ t)))
    (hcard' : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b,
      Fintype.card ι = Module.finrank ℝ (TangentSpace I' (γ' t)))
    (hYdiff : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ Y t) t)
    (hYdiff' : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I') γ' Y' t) t)
    (hDYdiff : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ
        (fun s : ℝ => covDerivAlong (I := I) g γ Y s) t) t)
    (hDYdiff' : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I') γ'
        (fun s : ℝ => covDerivAlong (I := I') g' γ' Y' s) t) t)
    (hJ : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b, IsJacobiAt (I := I) g γ Y t)
    (hJ' : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b, IsJacobiAt (I := I') g' γ' Y' t)
    (hmatch : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b, ∀ i j,
      g.inner (γ t) (F i t)
          ((DifferentialGeometry.Geometry.Curvature.riemannOp
              (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
              (γ t))
            (F j t) (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t))
        =
      g'.inner (γ' t) (F' i t)
          ((DifferentialGeometry.Geometry.Curvature.riemannOp
              (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I') g')
              (γ' t))
            (F' j t) (curveVelocity (I := I') γ' t)
            (curveVelocity (I := I') γ' t)))
    (hCbound : ∀ t ∈ _root_.Set.Icc (0 : ℝ) b, ∀ i j,
      |g.inner (γ t) (F i t)
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
            (γ t))
          (F j t) (curveVelocity (I := I) γ t)
          (curveVelocity (I := I) γ t))| ≤ C)
    (h0 : ∀ i,
      g.inner (γ 0) (F i 0) (Y 0) = g'.inner (γ' 0) (F' i 0) (Y' 0))
    (h0' : ∀ i,
      g.inner (γ 0) (F i 0) (covDerivAlong (I := I) g γ Y 0) =
        g'.inner (γ' 0) (F' i 0) (covDerivAlong (I := I') g' γ' Y' 0)) :
    ∀ t ∈ _root_.Set.Icc (0 : ℝ) b, ∀ i,
      g.inner (γ t) (F i t) (Y t) = g'.inner (γ' t) (F' i t) (Y' t) := by
  classical
  have hzero := DifferentialGeometry.Analysis.ODE.ode2_pi_zero
    (y := fun t i =>
      g.inner (γ t) (F i t) (Y t) - g'.inner (γ' t) (F' i t) (Y' t))
    (v := fun t i =>
      g.inner (γ t) (F i t) (covDerivAlong (I := I) g γ Y t) -
        g'.inner (γ' t) (F' i t) (covDerivAlong (I := I') g' γ' Y' t))
    (w := fun t i =>
      (- g.inner (γ t) (F i t)
          ((DifferentialGeometry.Geometry.Curvature.riemannOp
              (DifferentialGeometry.Geometry.Connection.LeviCivita
                (I := I) g) (γ t))
            (Y t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)))
        - (- g'.inner (γ' t) (F' i t)
            ((DifferentialGeometry.Geometry.Curvature.riemannOp
                (DifferentialGeometry.Geometry.Connection.LeviCivita
                  (I := I') g') (γ' t))
              (Y' t) (curveVelocity (I := I') γ' t)
              (curveVelocity (I := I') γ' t))))
    (b := b) (C := C) hC
    (fun i => fun t ht =>
      (((parInner_deriv (I := I) hn g γ (F i) Y t (hγ t ht) (hFdiff i t ht)
          (hYdiff t ht) (hFpar i t ht)).sub
        (parInner_deriv (I := I') hn g' γ' (F' i) Y' t (hγ' t ht)
          (hFdiff' i t ht) (hYdiff' t ht) (hFpar' i t ht))).continuousAt).continuousWithinAt)
    (fun i => fun t ht =>
      (((parInner_d2 (I := I) hn g γ (F i) Y t (hγ t ht) (hFdiff i t ht)
          (hDYdiff t ht) (hFpar i t ht) (hJ t ht)).sub
        (parInner_d2 (I := I') hn g' γ' (F' i) Y' t (hγ' t ht)
          (hFdiff' i t ht) (hDYdiff' t ht) (hFpar' i t ht)
          (hJ' t ht))).continuousAt).continuousWithinAt)
    (fun t ht i => by
      have hIcc : t ∈ _root_.Set.Icc (0 : ℝ) b := ⟨ht.1, le_of_lt ht.2⟩
      exact ((parInner_deriv (I := I) hn g γ (F i) Y t (hγ t hIcc)
          (hFdiff i t hIcc) (hYdiff t hIcc) (hFpar i t hIcc)).sub
        (parInner_deriv (I := I') hn g' γ' (F' i) Y' t (hγ' t hIcc)
          (hFdiff' i t hIcc) (hYdiff' t hIcc)
          (hFpar' i t hIcc))).hasDerivWithinAt)
    (fun t ht i => by
      have hIcc : t ∈ _root_.Set.Icc (0 : ℝ) b := ⟨ht.1, le_of_lt ht.2⟩
      exact ((parInner_d2 (I := I) hn g γ (F i) Y t (hγ t hIcc)
          (hFdiff i t hIcc) (hDYdiff t hIcc) (hFpar i t hIcc)
          (hJ t hIcc)).sub
        (parInner_d2 (I := I') hn g' γ' (F' i) Y' t (hγ' t hIcc)
          (hFdiff' i t hIcc) (hDYdiff' t hIcc) (hFpar' i t hIcc)
          (hJ' t hIcc))).hasDerivWithinAt)
    (fun t ht i => by
      have hIcc : t ∈ _root_.Set.Icc (0 : ℝ) b := ⟨ht.1, le_of_lt ht.2⟩
      have hexp := parInner_curv_expand (I := I) g γ t F Y
        (hON t hIcc) (hcard t hIcc) i
      have hexp' := parInner_curv_expand (I := I') g' γ' t F' Y'
        (hON' t hIcc) (hcard' t hIcc) i
      have hw :
          (- g.inner (γ t) (F i t)
              ((DifferentialGeometry.Geometry.Curvature.riemannOp
                  (DifferentialGeometry.Geometry.Connection.LeviCivita
                    (I := I) g) (γ t))
                (Y t) (curveVelocity (I := I) γ t)
                (curveVelocity (I := I) γ t)))
            - (- g'.inner (γ' t) (F' i t)
                ((DifferentialGeometry.Geometry.Curvature.riemannOp
                    (DifferentialGeometry.Geometry.Connection.LeviCivita
                      (I := I') g') (γ' t))
                  (Y' t) (curveVelocity (I := I') γ' t)
                  (curveVelocity (I := I') γ' t)))
          = ∑ j, (g'.inner (γ' t) (F' j t) (Y' t) -
                  g.inner (γ t) (F j t) (Y t)) *
              g.inner (γ t) (F i t)
                ((DifferentialGeometry.Geometry.Curvature.riemannOp
                    (DifferentialGeometry.Geometry.Connection.LeviCivita
                      (I := I) g) (γ t))
                  (F j t) (curveVelocity (I := I) γ t)
                  (curveVelocity (I := I) γ t)) := by
        rw [neg_sub_neg, hexp, hexp', ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← hmatch t hIcc i j]
        ring
      rw [hw]
      calc
        |∑ j, (g'.inner (γ' t) (F' j t) (Y' t) -
                  g.inner (γ t) (F j t) (Y t)) *
              g.inner (γ t) (F i t)
                ((DifferentialGeometry.Geometry.Curvature.riemannOp
                    (DifferentialGeometry.Geometry.Connection.LeviCivita
                      (I := I) g) (γ t))
                  (F j t) (curveVelocity (I := I) γ t)
                  (curveVelocity (I := I) γ t))|
            ≤ ∑ j, |(g'.inner (γ' t) (F' j t) (Y' t) -
                    g.inner (γ t) (F j t) (Y t)) *
                g.inner (γ t) (F i t)
                  ((DifferentialGeometry.Geometry.Curvature.riemannOp
                      (DifferentialGeometry.Geometry.Connection.LeviCivita
                        (I := I) g) (γ t))
                    (F j t) (curveVelocity (I := I) γ t)
                    (curveVelocity (I := I) γ t))| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, |g'.inner (γ' t) (F' j t) (Y' t) -
                g.inner (γ t) (F j t) (Y t)| * C := by
              refine Finset.sum_le_sum fun j _ => ?_
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (hCbound t hIcc i j) (abs_nonneg _)
        _ = C * ∑ j, |g.inner (γ t) (F j t) (Y t) -
                g'.inner (γ' t) (F' j t) (Y' t)| := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [abs_sub_comm]
              ring)
    (fun i => by rw [h0 i, sub_self])
    (fun i => by rw [h0' i, sub_self])
  intro t ht i
  exact sub_eq_zero.mp (hzero t ht i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.jacobi_coord_xfer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.jacobi_coord_xfer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.jacobi_coord_xfer ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.jacobi_coord_xfer

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
