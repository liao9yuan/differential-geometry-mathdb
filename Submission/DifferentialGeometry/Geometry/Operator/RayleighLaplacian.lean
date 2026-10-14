import Submission.DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Tensor.FirstNull.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Components

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Operator

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem laplacian_shifted_tensor_at_eigenvector
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) ∞ 2)
    (x : M) (v : TangentSpace I x) (ell : ℝ)
    (V : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (hV : V x = v)
    (hcovV :
      ∀ W : ContMDiffSection I E ∞ (TangentSpace I : M → Type _),
        ((leviCivitaConnectionOfMetric g) (fun y => V y) x) (W x) = 0)
    (hleft : ∀ z : TangentSpace I x,
      A x (vec2 v z) = ell * g.inner x v z)
    (hright : ∀ z : TangentSpace I x,
      A x (vec2 z v) = ell * g.inner x z v) :
    laplacian (leviCivitaConnectionOfMetric g) g
        (fun y =>
          (A + (-ell) • metricTensorField g) y (vec2 (V y) (V y))) x =
      tensorHeat0SMetricAt g (iterCov g 2 A 2 x) (vec2 v v) := by
  let cov := leviCivitaConnectionOfMetric g
  let B : Tensor0SField (I := I) (M := M) ∞ 2 :=
    A + (-ell) • metricTensorField g
  let f : M → ℝ := fun y => B y (vec2 (V y) (V y))
  have hcovInf :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
        (∞ : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally g
  have hcovOne :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
        (1 : WithTop ℕ∞) :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one g
  have hmc : IsMetricCompatible cov g :=
    leviCivitaConnectionOfMetric_isMetricCompatible g
  have hrealA :
      TotalNabla0SRealizes (I := I) 2 cov A (iterCov g 2 A 1) := by
    exact iterCov_realizes g A 0
  have hrealMetric :
      TotalNabla0SRealizes (I := I) 2 cov (metricTensorField g)
        (0 : Tensor0SField (I := I) (M := M) ∞ 3) :=
    zero_realizes_metric cov g hmc
  have hrealB :
      TotalNabla0SRealizes (I := I) 2 cov B (iterCov g 2 A 1) := by
    simpa only [B, smul_zero, add_zero] using
      (TotalNabla0SRealizes.add hrealA
        (TotalNabla0SRealizes.smul (-ell) hrealMetric))
  have hrealSecond :
      TotalNabla0SRealizes (I := I) 3 cov
        (iterCov g 2 A 1) (iterCov g 2 A 2) := by
    exact iterCov_realizes g A 1
  have hkerL : ∀ z : TangentSpace I x, B x (vec2 v z) = 0 := by
    intro z
    change A x (vec2 v z) +
      (-ell) * metricTensorField g x (vec2 v z) = 0
    rw [hleft z]
    simp only [metricTensorField_apply]
    change ell * g.inner x v z + (-ell) * g.inner x v z = 0
    ring
  have hkerR : ∀ z : TangentSpace I x, B x (vec2 z v) = 0 := by
    intro z
    change A x (vec2 z v) +
      (-ell) * metricTensorField g x (vec2 z v) = 0
    rw [hright z]
    simp only [metricTensorField_apply]
    change ell * g.inner x z v + (-ell) * g.inner x z v = 0
    ring
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := by
    let slots :
        Fin 2 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
      fun _ => V
    simpa only [f, slots, vec2_self_eq_const] using
      TensorMultilinear.contMDiff_tensor0SField_apply B slots
  have hAreg :
      ∀ Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _),
        ContMDiffAt I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
          (fun y =>
            (⟨y, (cov (fun z => V z) y) (Y y)⟩ :
              TotalSpace E (TangentSpace I : M → Type _))) x := by
    intro Y
    exact CovariantDerivative.smoothSections_cov_contMDiffAt_one
      cov hcovOne Y V x
  have hslots :=
    nabla2Eval_hess_slots (I := I)
      hrealB hrealSecond V hV hcovV hkerL hkerR
      (duSec_realizes f hf)
      (hessianSec_realizesAt cov hcovInf f hf x)
      hAreg
  have hlap :=
    scalarLap_smooth cov hcovInf g hmc (x := x) f hf
  have htrace :=
    lapTrace_of_slots cov g f (iterCov g 2 A 2 x)
      (vec2 v v) (hessianSec cov hcovInf f hf x) hlap hslots
  simpa only [f, B, tensorHeat0SMetricAt_apply] using htrace.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.laplacian_shifted_tensor_at_eigenvector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.laplacian_shifted_tensor_at_eigenvector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.laplacian_shifted_tensor_at_eigenvector ``Submission.DifferentialGeometry.Geometry.Operator.laplacian_shifted_tensor_at_eigenvector

end DifferentialGeometry.Geometry.Operator
