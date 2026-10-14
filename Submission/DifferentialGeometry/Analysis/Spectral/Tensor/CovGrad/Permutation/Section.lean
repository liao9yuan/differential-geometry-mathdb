import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.FiberNorm
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.CovariantOrderCoefficient.PassZero
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Algebra
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Norm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (sigma : Equiv.Perm (Fin s))
    (R : SmoothCcTensor g r s) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i
          (rsDomDomCongrSection (I := I) (M := M) g r s sigma R)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i R).toSection x) :=
  riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr
    (I := I) (M := M) g r s sigma R
    (rsDomDomCongrSection (I := I) (M := M) g r s sigma R)
    (fun y d => by
      rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) i x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq ``Submission.DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_iteratedCovGrad_ccTensor02Symm_le
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2) (k : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (2 + k) x
        ((iteratedCovGrad (I := I) g 0 2 k
          (ccTensor02Symm (I := I) (M := M) g P)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g 0 (2 + k) x
        ((iteratedCovGrad (I := I) g 0 2 k P).toSection x) := by
  rw [iteratedCovGrad_ccTensor02Symm_eq (I := I) (M := M) g P k]
  rw [show (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 k P +
      (1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 k
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) P)).toSection x) =
      ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 k P).toSection x +
        ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 k
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) P)).toSection x from by
    rw [SmoothCcTensor.toSection_add]
    rfl]
  refine (riemannianFiberNormSq_add_le_sq_sqrt
    (I := I) (M := M) g 0 (2 + k) x _ _).trans ?_
  rw [show (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 k P).toSection x) =
      (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g 0 2 k P).toSection x from by
    rw [SmoothCcTensor.toSection_smul]
    rfl]
  rw [show (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g 0 2 k
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) P)).toSection x) =
      (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g 0 2 k
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) P)).toSection x from by
    rw [SmoothCcTensor.toSection_smul]
    rfl]
  rw [DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul,
    DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul]
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
    (I := I) (M := M) g (Equiv.swap (0 : Fin 2) 1) P k x]
  set A := riemannianFiberNormSq (I := I) (M := M) g 0 (2 + k) x
    ((iteratedCovGrad (I := I) g 0 2 k P).toSection x) with hA_def
  have hA0 : 0 ≤ A := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (2 + k) x _
  have hs : Real.sqrt ((1 / 2 : ℝ) ^ 2 * A) =
      (1 / 2 : ℝ) * Real.sqrt A := by
    rw [Real.sqrt_mul (by positivity) A, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [hs]
  nlinarith [Real.sq_sqrt hA0, Real.sqrt_nonneg A]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_ccTensor02Symm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_ccTensor02Symm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_ccTensor02Symm_le ``Submission.DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_ccTensor02Symm_le

end Spectral
end Analysis
end DifferentialGeometry

namespace DifferentialGeometry.Integral.Connection

alias riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq :=
  DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq

end DifferentialGeometry.Integral.Connection

end
