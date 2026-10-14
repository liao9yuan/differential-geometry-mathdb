import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.TensorInner
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.CovariantDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow

noncomputable section

open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem laplacianAt_inner0S_eq_inner_roughLap_flowG_of_flat
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {s : ℕ} {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {t : Real} {x : M}
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (nabla2A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (nabla2B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s (S.base.connection t) A nablaA)
    (h2A : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) (S.base.connection t) nablaA nabla2A)
    (hB : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s (S.base.connection t) B nablaB)
    (h2B : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) (S.base.connection t) nablaB nabla2B)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (S.base.metric t) x basis gInv)
    (hBflat1 : nablaB x = 0)
    (hBflat2 : metricTrace0S2TensorInBasis (I := I) basis gInv (nabla2B x) = 0) :
    laplacianAt (I := I) (flowG (I := I) S) t
        (fun y : M => inner0S (I := I) (S.base.metric t) y s (A y) (B y)) x =
      inner0S (I := I) (S.base.metric t) x s
        (metricTrace0S2TensorInBasis (I := I) basis gInv (nabla2A x)) (B x) := by
  classical
  have hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      ((flowG (I := I) S).connection t) (∞ : WithTop ℕ∞) := by
    simpa [flowG, SolutionFamily.connection] using
      (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (S.base.metric t))
  simpa [flowG] using
    laplacianAt_inner0S_eq_inner_roughLap_of_flat (I := I)
      (G := flowG (I := I) S) (t := t) (x := x)
      A nablaA nabla2A B nablaB nabla2B
      (by simpa [flowG] using hA) (by simpa [flowG] using h2A)
      (by simpa [flowG] using hB) (by simpa [flowG] using h2B)
      hcov basis gInv (by simpa [flowG] using hinv)
      hBflat1 (by simpa [flowG] using hBflat2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.laplacianAt_inner0S_eq_inner_roughLap_flowG_of_flat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.laplacianAt_inner0S_eq_inner_roughLap_flowG_of_flat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.laplacianAt_inner0S_eq_inner_roughLap_flowG_of_flat ``Submission.DifferentialGeometry.PDE.RicciFlow.laplacianAt_inner0S_eq_inner_roughLap_flowG_of_flat

end

end DifferentialGeometry.PDE.RicciFlow
