import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section


open _root_.Bundle _root_.Manifold _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


def chartConstVecFiber (x₀ : M) (c : E) (x : M) : TangentSpace I x :=
  (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symm x c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.chartConstVecFiber then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.chartConstVecFiber"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.chartConstVecFiber ``Submission.DifferentialGeometry.Geometry.Riemannian.chartConstVecFiber


omit [FiniteDimensional ℝ E] in
lemma chartConstVecFiber_self (q : M) (v : TangentSpace I q) :
    chartConstVecFiber (I := I) q
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) q ⟨q, v⟩).2) q = v := by
  have hq : q ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) q).baseSet :=
    _root_.FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) q
  simp only [chartConstVecFiber]
  exact (_root_.FiberBundle.trivializationAt E (TangentSpace I) q).symm_apply_apply_mk hq v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.chartConstVecFiber_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.chartConstVecFiber_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.chartConstVecFiber_self ``Submission.DifferentialGeometry.Geometry.Riemannian.chartConstVecFiber_self


omit [FiniteDimensional ℝ E] in
lemma chartConstVec_contMDiffOn (x₀ : M) (c : E) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x
        (chartConstVecFiber (I := I) x₀ c x))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet := by
  have hiff :=
    ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀)).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞) (s := fun x => chartConstVecFiber (I := I) x₀ c x)
  refine hiff.mpr ?_
  refine (contMDiffOn_const (c := c)).congr ?_
  intro x hx
  have h := (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).apply_mk_symm hx c
  simpa [chartConstVecFiber] using congrArg Prod.snd h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.chartConstVec_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.chartConstVec_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.chartConstVec_contMDiffOn ``Submission.DifferentialGeometry.Geometry.Riemannian.chartConstVec_contMDiffOn

end Riemannian
end Geometry
end DifferentialGeometry

end
