import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Topology.PartialHomeomorph.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Topology _root_.Manifold
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E F H H' P M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace P] [ChartedSpace H P]
  [TopologicalSpace M] [ChartedSpace H' M]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}

set_option backward.isDefEq.respectTransparency false in
theorem injective_mfderiv_of_leftInverseOn
    {f : P → M} (hf : ContMDiff I J ∞ f) {g : M → P} {S : Set M}
    (hg : ContMDiffOn J I ∞ g S) (hmap : ∀ p, f p ∈ S)
    (hleft : Function.LeftInverse g f) (p : P) :
    Function.Injective (mfderiv I J f p) := by
  have heq : g ∘ f = id := funext hleft
  have hcomp := mfderivWithin_comp p
    ((hg (f p) (hmap p)).mdifferentiableWithinAt (by simp))
    ((hf p).mdifferentiableAt (by simp)).mdifferentiableWithinAt
    (s := _root_.Set.univ) (fun x _ ↦ hmap x) (uniqueMDiffWithinAt_univ I)
  have hBA : (mfderivWithin J I g S (f p)).comp (mfderiv I J f p) =
      ContinuousLinearMap.id ℝ E := by
    have hcomp' : (mfderivWithin J I g S (f p)).comp (mfderiv I J f p) =
        (mfderiv I I (g ∘ f) p : E →L[ℝ] E) := by
      simpa only [mfderivWithin_univ] using hcomp.symm
    rw [heq, mfderiv_id] at hcomp'
    exact hcomp'
  intro u v huv
  have h := congrArg (mfderivWithin J I g S (f p)) huv
  change ((mfderivWithin J I g S (f p)).comp (mfderiv I J f p)) u =
    ((mfderivWithin J I g S (f p)).comp (mfderiv I J f p)) v at h
  change (mfderivWithin J I g S (f p)).comp (mfderiv I J f p) u =
    (mfderivWithin J I g S (f p)).comp (mfderiv I J f p) v at h
  have h' : (ContinuousLinearMap.id ℝ E) u = (ContinuousLinearMap.id ℝ E) v := hBA ▸ h
  exact h'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_leftInverseOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_leftInverseOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_leftInverseOn ``Submission.DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_leftInverseOn

theorem isEmbedding_and_injective_mfderiv_of_smooth_partialEquiv
    (e : PartialEquiv P M) (hes : e.source = _root_.Set.univ)
    (he : ContMDiff I J ∞ e) (hei : ContMDiffOn J I ∞ e.symm e.target) :
    IsEmbedding e ∧ ∀ p, Function.Injective (mfderiv I J e p) := by
  let h : PartialHomeomorph P M :=
    { toPartialEquiv := e
      continuousOn_toFun := he.continuous.continuousOn
      continuousOn_invFun := hei.continuousOn }
  refine ⟨h.isEmbedding hes, ?_⟩
  exact injective_mfderiv_of_leftInverseOn he hei
    (fun p ↦ e.map_source (hes ▸ _root_.Set.mem_univ p)) (fun p ↦ e.left_inv (hes ▸ _root_.Set.mem_univ p))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.isEmbedding_and_injective_mfderiv_of_smooth_partialEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.isEmbedding_and_injective_mfderiv_of_smooth_partialEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.isEmbedding_and_injective_mfderiv_of_smooth_partialEquiv ``Submission.DifferentialGeometry.Topology.Manifold.isEmbedding_and_injective_mfderiv_of_smooth_partialEquiv

end DifferentialGeometry.Topology.Manifold
