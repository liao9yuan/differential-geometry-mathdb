import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.LocalTrace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem laplacian_eq_sum_hessFun_of_contMDiffOn_orthonormal
    (g : SmoothRiemannianMetric I M) {f : M → Real} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn I 𝓘(Real, Real) ∞ f U)
    {x : M} (hx : x ∈ U)
    (P : Fin (Module.finrank Real E) → TangentSpace I x)
    (hP : ∀ i j, g.inner x (P i) (P j) = if i = j then (1 : Real) else 0) :
    laplacian (I := I) (LeviCivita (I := I) g) g f x =
      ∑ i : Fin (Module.finrank Real E), hessFun (I := I) g f x (P i) (P i) := by
  classical
  have hlin : LinearIndependent Real P := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    have hinner := congrArg ((g.inner x) (P i)) hc
    simpa [map_sum, hP] using hinner
  have hcard : Fintype.card (Fin (Module.finrank Real E)) =
      Module.finrank Real (TangentSpace I x) := by
    change Fintype.card (Fin (Module.finrank Real E)) = Module.finrank Real E
    exact Fintype.card_fin _
  let B := basisOfLinearIndependentOfCardEqFinrank' P hlin hcard
  have hBP : ∀ i, B i = P i :=
    fun i ↦ congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' P hlin hcard) i
  have hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : Real) else 0 := by
    intro i j
    rw [hBP i, hBP j]
    exact hP i j
  rw [laplacian_eq_sum_hessFun_of_contMDiffOn g hU hf hx B hB]
  apply Finset.sum_congr rfl
  intro i _
  rw [hBP i]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.laplacian_eq_sum_hessFun_of_contMDiffOn_orthonormal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.laplacian_eq_sum_hessFun_of_contMDiffOn_orthonormal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.laplacian_eq_sum_hessFun_of_contMDiffOn_orthonormal ``Submission.DifferentialGeometry.Geometry.Operator.laplacian_eq_sum_hessFun_of_contMDiffOn_orthonormal

end DifferentialGeometry.Geometry.Operator
