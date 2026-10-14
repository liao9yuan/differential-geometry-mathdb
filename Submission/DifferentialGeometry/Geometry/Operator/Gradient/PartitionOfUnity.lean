import Submission.DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import Submission.DifferentialGeometry.Topology.PartitionOfUnity.CompactSupport
import Mathlib.Geometry.Manifold.PartitionOfUnity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Set
open scoped _root_.Manifold _root_.ContDiff
namespace DifferentialGeometry.Geometry.Operator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
theorem gradientFun_eq_sum_fintsupportOn
    {ι : Type*} {s K : Set M} (ρ : SmoothPartitionOfUnity ι I M s)
    (hK : IsCompact K) (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hfK : Function.support f ⊆ K) (hfs : Function.support f ⊆ s)
    {x : M} (hf : MDifferentiableAt I 𝓘(ℝ) f x) :
    gradientFun g f x =
      ∑ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
        gradientFun g (fun y => ρ i y * f y) x := by
  classical
  have heq : f = ∑ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
      (fun y => ρ i y * f y) := by
    funext y
    simp only [Finset.sum_apply]
    change f y = ∑ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
      ρ.toPartitionOfUnity i y • f y
    exact (ρ.toPartitionOfUnity.sum_fintsupportOn_smul hK hfK hfs y).symm
  calc
    gradientFun g f x = gradientFun g
        (∑ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK, (fun y => ρ i y * f y)) x := by
      rw [← heq]
    _ = _ := gradientFun_sum g _ fun i _ =>
      ((ρ i).contMDiff.mdifferentiableAt (by simp)).mul hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.gradientFun_eq_sum_fintsupportOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.gradientFun_eq_sum_fintsupportOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.gradientFun_eq_sum_fintsupportOn ``Submission.DifferentialGeometry.Geometry.Operator.gradientFun_eq_sum_fintsupportOn
end DifferentialGeometry.Geometry.Operator
