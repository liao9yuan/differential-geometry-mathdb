import Submission.DifferentialGeometry.Geometry.Curvature.Bochner.Tensor.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import Submission.DifferentialGeometry.Geometry.Operator.Hessian.Trace.Realization
import Submission.DifferentialGeometry.Geometry.Operator.Scalar.Calculus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

open _root_.Submission.DifferentialGeometry.Geometry.Operator
namespace DifferentialGeometry.Geometry.Curvature

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]
variable [SigmaCompactSpace M] [T2Space M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete Real E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
theorem ricHess_eq_inner
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M)
    (hmc : IsMetricCompatible (I := I) cov g)
    (f : M -> Real) (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f)
    (x : M) :
    LinearMap.trace Real (TangentSpace I x)
        ((cotangentSharpLinear (I := I) g x).comp
          ((tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x
              (metricRicciAt (I := I) g x)).toLinearMap.comp
            (cov (fun y : M => gradientFun (I := I) g f y) x).toLinearMap)) =
      inner02 (I := I) g x (metricRicciAt (I := I) g x)
        (hessianSec (I := I) cov hcov f hf x) := by
  classical
  let G : (y : M) -> TangentSpace I y :=
    fun y => gradientFun (I := I) g f y
  let D : TangentSpace I x →L[Real] TangentSpace I x := cov G x
  let Ric := metricRicciAt (I := I) g x
  let R : TangentSpace I x →ₗ[Real] TangentSpace I x :=
    (cotangentSharpLinear (I := I) g x).comp
      (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x Ric).toLinearMap
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  let delta : Fin (Module.finrank Real (TangentSpace I x)) ->
      Fin (Module.finrank Real (TangentSpace I x)) -> Real :=
    fun i j => if i = j then 1 else 0
  have hinv : MetricInverseInBasis (I := I) g x basis delta :=
    DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g basis hON
  have hrepr (i j : Fin (Module.finrank Real (TangentSpace I x))) :
      basis.repr (D (basis i)) j = g.inner x (D (basis i)) (basis j) := by
    rw [basis_repr_eq_sum_inv_inner (I := I) g x basis delta hinv]
    simp [delta]
  have hD (i : Fin (Module.finrank Real (TangentSpace I x))) :
      D (basis i) =
        ∑ j, g.inner x (D (basis i)) (basis j) • basis j := by
    calc
      D (basis i) = ∑ j, basis.repr (D (basis i)) j • basis j :=
        (basis.sum_repr (D (basis i))).symm
      _ = ∑ j, g.inner x (D (basis i)) (basis j) • basis j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hrepr i j]
  have hraise (v w : TangentSpace I x) :
      g.inner x (R v) w = Ric (vec2 (I := I) v w) := by
    change g.inner x
        (cotangentSharp (I := I) g x
          (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x Ric v)) w = _
    rw [cotangentSharp_inner_eval, tensor0S_curry_one_apply]
    rfl
  have htrace :
      LinearMap.trace Real (TangentSpace I x)
          (R.comp D.toLinearMap) =
        ∑ i, Ric (vec2 (I := I) (D (basis i)) (basis i)) := by
    rw [linearMap_trace_eq_sum_inv_inner_apply
      (I := I) g x basis delta hinv]
    simp only [LinearMap.comp_apply]
    simp_rw [hraise]
    simp [delta]
  have hinner :
      inner02 (I := I) g x (metricRicciAt (I := I) g x)
          (hessianSec (I := I) cov hcov f hf x) =
        ∑ i, ∑ j,
          Ric (vec2 (I := I) (basis i) (basis j)) *
            g.inner x (D (basis i)) (basis j) := by
    rw [inner02_eq_coord_direct (I := I) g x basis delta hinv]
    simp_rw [hessSec_inner_cov (I := I) cov hcov g hmc f hf x]
    simp [delta, D, G, Ric]
  have hRic_sum (i : Fin (Module.finrank Real (TangentSpace I x))) :
      Ric (vec2 (I := I) (D (basis i)) (basis i)) =
        ∑ j, g.inner x (D (basis i)) (basis j) *
          Ric (vec2 (I := I) (basis j) (basis i)) := by
    unfold vec2
    rw [← tensor0S_curry_one_apply (I := I) Ric (D (basis i)) (basis i)]
    conv_lhs => rw [hD i]
    rw [map_sum, Tensor0SSpace.sum_apply]
    simp only [map_smul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Tensor0SSpace.smul_apply, smul_eq_mul]
    rw [tensor0S_curry_one_apply]
  calc
    LinearMap.trace Real (TangentSpace I x)
        ((cotangentSharpLinear (I := I) g x).comp
          ((tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x
              (metricRicciAt (I := I) g x)).toLinearMap.comp
            (cov (fun y : M => gradientFun (I := I) g f y) x).toLinearMap)) =
        ∑ i, Ric (vec2 (I := I) (D (basis i)) (basis i)) := by
      simpa [R, Ric, D, G, LinearMap.comp_assoc] using htrace
    _ = ∑ i, ∑ j,
          g.inner x (D (basis i)) (basis j) *
            Ric (vec2 (I := I) (basis j) (basis i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hRic_sum i
    _ = ∑ i, ∑ j,
          Ric (vec2 (I := I) (basis i) (basis j)) *
            g.inner x (D (basis i)) (basis j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [show Ric (vec2 (I := I) (basis j) (basis i)) =
          Ric (vec2 (I := I) (basis i) (basis j)) by
        exact metricRicciSymm (I := I) g basis delta hinv j i]
      ring
    _ = inner02 (I := I) g x (metricRicciAt (I := I) g x)
          (hessianSec (I := I) cov hcov f hf x) := hinner.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricHess_eq_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricHess_eq_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricHess_eq_inner ``Submission.DifferentialGeometry.Geometry.Curvature.ricHess_eq_inner

end DifferentialGeometry.Geometry.Curvature
