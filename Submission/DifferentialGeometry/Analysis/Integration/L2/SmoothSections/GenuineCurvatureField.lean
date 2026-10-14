import Submission.DifferentialGeometry.Geometry.Curvature.Bochner.Tensor.Pointwise.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Bounds.Uniform.SmoothTensor

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Integral
namespace L2

open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace SmoothCcTensor


def toFunAddHom {g : SmoothRiemannianMetric I M} {r s : ℕ} :
    SmoothCcTensor g r s →+ (M → TensorRSModel r s ℝ E) where
  toFun := fun S => S.toFun
  map_zero' := SmoothCcTensor.toFun_zero
  map_add' := SmoothCcTensor.toFun_add

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toFunAddHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toFunAddHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toFunAddHom ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toFunAddHom


lemma toSection_sum {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {ι : Type*} (t : Finset ι) (F : ι → SmoothCcTensor g r s) :
    (∑ i ∈ t, F i).toSection = ∑ i ∈ t, (F i).toSection :=
  map_sum (SmoothCcTensor.toSectionAddHom (I := I) (M := M) (g := g) (r := r) (s := s)) F t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_sum ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_sum


lemma toFun_sum {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {ι : Type*} (t : Finset ι) (F : ι → SmoothCcTensor g r s) :
    (∑ i ∈ t, F i).toFun = ∑ i ∈ t, (F i).toFun :=
  map_sum (SmoothCcTensor.toFunAddHom (I := I) (M := M) (g := g) (r := r) (s := s)) F t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_sum ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toFun_sum


lemma toSection_sum_apply {g : SmoothRiemannianMetric I M} {r s : ℕ}
    {ι : Type*} (t : Finset ι) (F : ι → SmoothCcTensor g r s) (x : M) :
    (∑ i ∈ t, F i).toSection x = ∑ i ∈ t, (F i).toSection x := by
  rw [toSection_sum]
  have hcoe : (⇑(∑ i ∈ t, (F i).toSection) :
        Π x : M, TensorRSSpace r s I x) =
      ∑ i ∈ t, (⇑((F i).toSection) : Π x : M, TensorRSSpace r s I x) :=
    map_sum (ContMDiffSection.coeAddHom I (TensorRSModel r s ℝ E) ∞
      (fun x : M => TensorRSSpace r s I x)) (fun i => (F i).toSection) t
  calc (∑ i ∈ t, (F i).toSection) x
      = (⇑(∑ i ∈ t, (F i).toSection) : Π x : M, TensorRSSpace r s I x) x := rfl
    _ = (∑ i ∈ t, (⇑((F i).toSection) : Π x : M, TensorRSSpace r s I x)) x := by rw [hcoe]
    _ = ∑ i ∈ t, (F i).toSection x := Finset.sum_apply x t _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_sum_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_sum_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_sum_apply ``Submission.DifferentialGeometry.Integral.L2.SmoothCcTensor.toSection_sum_apply

end SmoothCcTensor

end L2
end Integral
end DifferentialGeometry

end
