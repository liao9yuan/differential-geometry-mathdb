import Submission.DifferentialGeometry.Geometry.Coordinates.Connection.Christoffel
import Submission.DifferentialGeometry.Geometry.Coordinates.Fields.Tensor
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.ConnectionDifference
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.TensorRS.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.Tensor.Coordinates

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Module _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.BigOperators _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {u : Set M}

omit [DecidableEq Idx] in
theorem tensor12Comp_connectionDifferenceTensorAt
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u) (i j k : Idx) :
    tensor12CompInFrame (I := I)
        (fun y : M => connectionDifferenceTensorAt (I := I) cov cov' y)
        frame hframe x hx k i j =
      christoffelSymbolDifferenceInFrame cov cov' frame hframe x i j k := by
  classical
  unfold tensor12CompInFrame tensorRSComponentInFrame
    christoffelSymbolDifferenceInFrame
  change
    componentRSField (I := I) (hframe.toBasisAt hx)
        (connectionDifferenceTensorAt (I := I) cov cov' x)
        (fun _ : Fin 1 => k)
        (fun q : Fin 2 => if q = 0 then i else j) =
      (hframe.coeff k x)
        (((CovariantDerivative.difference cov cov' x) (frame j x)) (frame i x))
  rw [componentRS_connectionDifferenceTensorAt]
  simp [IsLocalFrameOn.coeff, hx, IsLocalFrameOn.toBasisAt_coe]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.tensor12Comp_connectionDifferenceTensorAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.tensor12Comp_connectionDifferenceTensorAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.tensor12Comp_connectionDifferenceTensorAt ``Submission.DifferentialGeometry.Tensor.Coordinates.tensor12Comp_connectionDifferenceTensorAt

theorem normSqRS_connectionDifferenceTensorAt_eq_christoffel_sum
    [IsManifold I ∞ M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g : SmoothRiemannianMetric I M)
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u)
    (hinv :
      MetricInverseInBasis (I := I) g x (hframe.toBasisAt hx)
        (identityInvMetric (Idx := Idx))) :
    normSqRS (I := I) (g := g) (x := x) 1 2
        (connectionDifferenceTensorAt (I := I) cov cov' x) =
      ∑ k : Idx, ∑ i : Idx, ∑ j : Idx,
        (christoffelSymbolDifferenceInFrame cov cov' frame hframe x i j k) ^ 2 := by
  rw [normSqRS_one_two_identity_eq_sum (I := I) g x
    (hframe.toBasisAt hx) hinv
    (connectionDifferenceTensorAt (I := I) cov cov' x)]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  unfold christoffelSymbolDifferenceInFrame
  rw [componentRS_connectionDifferenceTensorAt]
  simp [IsLocalFrameOn.coeff, hx, IsLocalFrameOn.toBasisAt_coe]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.normSqRS_connectionDifferenceTensorAt_eq_christoffel_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.normSqRS_connectionDifferenceTensorAt_eq_christoffel_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.normSqRS_connectionDifferenceTensorAt_eq_christoffel_sum ``Submission.DifferentialGeometry.Tensor.Coordinates.normSqRS_connectionDifferenceTensorAt_eq_christoffel_sum

end

end DifferentialGeometry.Tensor.Coordinates
