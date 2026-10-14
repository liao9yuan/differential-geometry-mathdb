import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace SmoothPartitionOfUnity
open _root_.SmoothPartitionOfUnity

variable {ι E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ F H} {K : Set M}
  (mu : SmoothPartitionOfUnity ι I M K)
  (U : TopologicalSpace.Opens E) (e : U → M)

open _root_.SmoothPartitionOfUnity in
def coordinateWeights : E → ι → ℝ :=
  Function.extend Subtype.val (fun z : U => fun i => mu i (e z)) (fun _ => 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SmoothPartitionOfUnity.coordinateWeights then
    throwError "Refusing to shadow existing declaration SmoothPartitionOfUnity.coordinateWeights"
  Lean.modifyEnv fun env => Lean.addAlias env `SmoothPartitionOfUnity.coordinateWeights ``Submission.SmoothPartitionOfUnity.coordinateWeights

omit [NormedSpace ℝ E] in
open _root_.SmoothPartitionOfUnity in
@[simp] theorem coordinateWeights_apply (z : U) (i : ι) :
    mu.coordinateWeights U e z i = mu i (e z) := by
  unfold coordinateWeights
  rw [Subtype.val_injective.extend_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SmoothPartitionOfUnity.coordinateWeights_apply then
    throwError "Refusing to shadow existing declaration SmoothPartitionOfUnity.coordinateWeights_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `SmoothPartitionOfUnity.coordinateWeights_apply ``Submission.SmoothPartitionOfUnity.coordinateWeights_apply

open _root_.SmoothPartitionOfUnity in
theorem contDiffOn_coordinateWeights [Fintype ι] (he : ContMDiff 𝓘(ℝ, E) I ∞ e) :
    ContDiffOn ℝ ∞ (mu.coordinateWeights U e) U := by
  apply contDiffOn_pi.mpr
  intro i z hz
  have hsub : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (fun z : U => mu.coordinateWeights U e z i) ⟨z, hz⟩ := by
    simpa only [coordinateWeights_apply, Function.comp_def] using ((mu i).contMDiff.comp he).contMDiffAt
  have hamb : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (fun z => mu.coordinateWeights U e z i) z :=
    (contMDiffAt_subtype_iff (U := U) (x := ⟨z, hz⟩)
      (f := fun z => mu.coordinateWeights U e z i)).mp hsub
  exact (contMDiffAt_iff_contDiffAt.mp hamb).contDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SmoothPartitionOfUnity.contDiffOn_coordinateWeights then
    throwError "Refusing to shadow existing declaration SmoothPartitionOfUnity.contDiffOn_coordinateWeights"
  Lean.modifyEnv fun env => Lean.addAlias env `SmoothPartitionOfUnity.contDiffOn_coordinateWeights ``Submission.SmoothPartitionOfUnity.contDiffOn_coordinateWeights

omit [NormedSpace ℝ E] in
open _root_.SmoothPartitionOfUnity in
theorem coordinateWeights_nonneg (z : U) (i : ι) :
    0 ≤ mu.coordinateWeights U e z i := by
  rw [coordinateWeights_apply]
  exact mu.nonneg i (e z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SmoothPartitionOfUnity.coordinateWeights_nonneg then
    throwError "Refusing to shadow existing declaration SmoothPartitionOfUnity.coordinateWeights_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `SmoothPartitionOfUnity.coordinateWeights_nonneg ``Submission.SmoothPartitionOfUnity.coordinateWeights_nonneg

omit [NormedSpace ℝ E] in
open _root_.SmoothPartitionOfUnity in
theorem sum_coordinateWeights_eq_one [Fintype ι] (z : U) (hz : e z ∈ K) :
    ∑ i, mu.coordinateWeights U e z i = 1 := by
  simpa only [coordinateWeights_apply, finsum_eq_sum_of_fintype] using mu.sum_eq_one hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SmoothPartitionOfUnity.sum_coordinateWeights_eq_one then
    throwError "Refusing to shadow existing declaration SmoothPartitionOfUnity.sum_coordinateWeights_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `SmoothPartitionOfUnity.sum_coordinateWeights_eq_one ``Submission.SmoothPartitionOfUnity.sum_coordinateWeights_eq_one

end SmoothPartitionOfUnity

end

end
