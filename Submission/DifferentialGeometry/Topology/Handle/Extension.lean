import Submission.DifferentialGeometry.Topology.Attachment.Basic
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import Submission.DifferentialGeometry.Topology.Embedding.Extension
import Submission.DifferentialGeometry.Topology.Handle.Embedding
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology

namespace DifferentialGeometry.Topology.Handle

attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

theorem exists_contDiff_closedCell_extension_bijective_fderiv (m : ℕ)
    {u : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))}
    (hu : Manifold.IsImmersion (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u) :
    ∃ F : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin (m + 1)),
      ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      (∀ x : ClosedCell (m + 1), F x.val = u x) ∧
      ∀ x : ClosedCell (m + 1), Function.Bijective (fderiv ℝ F x.val) := by
  obtain ⟨F, hF, hFc, _, hFu⟩ :=
    (closedCellInclusion_isSmoothEmbedding m).exists_contDiff_compact_extension_halfspace
      hu.contMDiff isCompact_univ isOpen_univ (Set.subset_univ _)
  have hcomp : F ∘ (Subtype.val : ClosedCell (m + 1) →
      EuclideanSpace ℝ (Fin (m + 1))) = u := by
    funext x
    exact hFu (Set.mem_univ x)
  refine ⟨F, hF, hFc, fun x => congrFun hcomp x, ?_⟩
  intro x
  let : FiniteDimensional ℝ (TangentSpace (𝓡∂ (m + 1)) x) := by
    change FiniteDimensional ℝ (EuclideanSpace ℝ (Fin (m + 1)))
    infer_instance
  have hi := DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_isImmersionAt
    (𝓡∂ (m + 1)) (𝓡 (m + 1)) u x (hu.isImmersionAt x)
  rw [← hcomp, mfderiv_comp x
    (hF.contMDiff.mdifferentiable (by simp) x.val)
    ((closedCellInclusion_contMDiff m).mdifferentiable (by simp) x),
    mfderiv_eq_fderiv] at hi
  have hs : Function.Surjective ((fderiv ℝ F x.val).comp
      (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1))
        (Subtype.val : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) x)) :=
    LinearMap.surjective_of_injective
      (f := ((fderiv ℝ F x.val).comp
        (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1))
          (Subtype.val : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) x)).toLinearMap) hi
  change Function.Surjective (fun v : TangentSpace (𝓡∂ (m + 1)) x =>
    fderiv ℝ F x.val (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1))
      (Subtype.val : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) x v)) at hs
  have hFsurj : Function.Surjective (fderiv ℝ F x.val) :=
    Function.Surjective.of_comp (f := fderiv ℝ F x.val)
      (g := mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1))
        (Subtype.val : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) x) hs
  exact ⟨(LinearMap.injective_iff_surjective
    (f := (fderiv ℝ F x.val).toLinearMap)).mpr hFsurj, hFsurj⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.exists_contDiff_closedCell_extension_bijective_fderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.exists_contDiff_closedCell_extension_bijective_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.exists_contDiff_closedCell_extension_bijective_fderiv ``Submission.DifferentialGeometry.Topology.Handle.exists_contDiff_closedCell_extension_bijective_fderiv

end DifferentialGeometry.Topology.Handle
