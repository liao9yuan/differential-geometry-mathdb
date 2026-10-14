import Submission.DifferentialGeometry.Topology.PartitionOfUnity.CompactSupport
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace SmoothPartitionOfUnity
open _root_.SmoothPartitionOfUnity

variable {ι E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

open _root_.SmoothPartitionOfUnity in
theorem sum_mvfderiv_mul_fintsupportOn
    {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s) {K : Set M} (hK : IsCompact K)
    {f : M → ℝ} (hfK : Function.support f ⊆ K) (hfs : Function.support f ⊆ s) {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) :
    (∑ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
      mvfderiv I (fun y => ρ i y * f y) x) = mvfderiv I f x := by
  classical
  have hsum :
      (∑ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
        (fun y => ρ i y * f y)) = f := by
    funext y
    have hcoe (i : ι) : ρ.toPartitionOfUnity i y = ρ i y := rfl
    simpa only [Finset.sum_apply, smul_eq_mul, hcoe] using
      ρ.toPartitionOfUnity.sum_fintsupportOn_smul hK hfK hfs y
  have hd (i : ι) : MDifferentiableAt I 𝓘(ℝ) (fun y => ρ i y * f y) x :=
    ((ρ i).contMDiff.mdifferentiableAt (by simp)).mul hf
  have hfinite (J : Finset ι) :
      MDifferentiableAt I 𝓘(ℝ) (∑ i ∈ J, (fun y => ρ i y * f y)) x ∧
        mvfderiv I (∑ i ∈ J, (fun y => ρ i y * f y)) x =
          ∑ i ∈ J, mvfderiv I (fun y => ρ i y * f y) x := by
    induction J using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact ⟨mdifferentiableAt_const, mvfderiv_zero⟩
    | insert i J hi ih =>
      simp only [Finset.sum_insert hi]
      exact ⟨(hd i).add ih.1, by rw [mvfderiv_add (hd i) ih.1, ih.2]⟩
  simpa only [hsum] using
    (hfinite (ρ.toPartitionOfUnity.fintsupportOn K hK)).2.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SmoothPartitionOfUnity.sum_mvfderiv_mul_fintsupportOn then
    throwError "Refusing to shadow existing declaration SmoothPartitionOfUnity.sum_mvfderiv_mul_fintsupportOn"
  Lean.modifyEnv fun env => Lean.addAlias env `SmoothPartitionOfUnity.sum_mvfderiv_mul_fintsupportOn ``Submission.SmoothPartitionOfUnity.sum_mvfderiv_mul_fintsupportOn

end SmoothPartitionOfUnity
