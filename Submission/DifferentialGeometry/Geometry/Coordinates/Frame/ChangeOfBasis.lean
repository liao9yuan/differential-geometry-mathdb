import Submission.DifferentialGeometry.Geometry.Coordinates.Frame.Chart
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section ChangeOfBasis

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
theorem localFrame_eq_sum_repr
    (e : _root_.Bundle.Trivialization E (π E (TangentSpace I : M → Type _)))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E) (c : Module.Basis κ ℝ E)
    (j : κ) :
    e.localFrame c j = ∑ a, b.repr (c j) a • e.localFrame b a := by
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply]
  by_cases hx : x ∈ e.baseSet
  · simp only [e.localFrame_apply_of_mem_baseSet _ hx,
      Trivialization.basisAt, Module.Basis.map_apply]
    simpa only [map_sum, map_smul] using
      congrArg (e.linearEquivAt ℝ x hx).symm (b.sum_repr (c j)).symm
  · simp only [e.localFrame_apply_of_notMem _ hx, smul_zero, Finset.sum_const_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.localFrame_eq_sum_repr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.localFrame_eq_sum_repr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.localFrame_eq_sum_repr ``Submission.DifferentialGeometry.Tensor.Coordinates.localFrame_eq_sum_repr

omit [Fintype ι] [Fintype κ] in
theorem localFrame_coeff_localFrame
    (e : _root_.Bundle.Trivialization E (π E (TangentSpace I : M → Type _)))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E) (c : Module.Basis κ ℝ E)
    {x : M} (hx : x ∈ e.baseSet) (i : ι) (k : κ) :
    e.localFrameCoeff I c k x (e.localFrame b i x) = c.repr (b i) k := by
  rw [e.localFrameCoeff_apply_of_mem_baseSet c hx,
    e.localFrame_apply_of_mem_baseSet b hx]
  simp only [Trivialization.basisAt, Module.Basis.map_apply, Module.Basis.map_repr,
    LinearEquiv.trans_apply, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.localFrame_coeff_localFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.localFrame_coeff_localFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.localFrame_coeff_localFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.localFrame_coeff_localFrame

end ChangeOfBasis

variable [Module.Finite ℝ E]

theorem chartBasisVecFiber_eq_localFrame (α : M) :
    chartBasisVecFiber (I := I) α =
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).localFrame (chartModelBasis E) := by
  funext i x
  by_cases hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
  · rw [Trivialization.localFrame_apply_of_mem_baseSet _ _ hx]
    rw [chartBasisVecFiber, Trivialization.symmL_apply _ hx]
    rfl
  · rw [Trivialization.localFrame_apply_of_notMem _ _ hx]
    exact Trivialization.symmL_apply_of_notMem _ hx _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber_eq_localFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber_eq_localFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber_eq_localFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber_eq_localFrame

theorem chartBasisVecFiber_isLocalFrame (α : M) :
    IsLocalFrameOn I E 1 (chartBasisVecFiber (I := I) α)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  rw [chartBasisVecFiber_eq_localFrame]
  exact (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).isLocalFrameOn_localFrame_baseSet
    I 1 (chartModelBasis E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber_isLocalFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber_isLocalFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber_isLocalFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber_isLocalFrame

end DifferentialGeometry.Tensor.Coordinates
