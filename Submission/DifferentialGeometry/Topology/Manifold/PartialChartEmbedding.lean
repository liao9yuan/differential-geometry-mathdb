import Submission.DifferentialGeometry.Topology.Covering.ImmersionLift
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Topology _root_.Manifold
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology

variable {E F H H' W M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace W] [ChartedSpace H W]
  [TopologicalSpace M] [ChartedSpace H' M]
  [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}

theorem contMDiff_comp_partialDiffeomorph
    (φ : PartialDiffeomorph J J M N ∞) {f : W → M}
    (hf : ContMDiff I J ∞ f) (hsub : _root_.Set.range f ⊆ φ.source) :
    ContMDiff I J ∞ (φ ∘ f) :=
  contMDiffOn_univ.mp (φ.contMDiffOn_toFun.comp hf.contMDiffOn (fun x _ ↦ hsub (_root_.Set.mem_range_self x)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.contMDiff_comp_partialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.contMDiff_comp_partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.contMDiff_comp_partialDiffeomorph ``Submission.DifferentialGeometry.Topology.contMDiff_comp_partialDiffeomorph

theorem isEmbedding_comp_partialDiffeomorph
    (φ : PartialDiffeomorph J J M N ∞) {f : W → M}
    (hf : _root_.Topology.IsEmbedding f) (hsub : _root_.Set.range f ⊆ φ.source) : _root_.Topology.IsEmbedding (φ ∘ f) := by
  let f' : W → φ.source := fun x ↦ ⟨f x, hsub (_root_.Set.mem_range_self x)⟩
  have hf' : _root_.Topology.IsEmbedding f' := IsEmbedding.subtypeVal.of_comp_iff.mp hf
  exact φ.toOpenPartialHomeomorph.isOpenEmbedding_restrict.isEmbedding.comp hf'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isEmbedding_comp_partialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isEmbedding_comp_partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isEmbedding_comp_partialDiffeomorph ``Submission.DifferentialGeometry.Topology.isEmbedding_comp_partialDiffeomorph

theorem isSmoothEmbedding_comp_partialDiffeomorph [IsManifold J ∞ N]
    (φ : PartialDiffeomorph J J M N ∞) {f : W → M}
    (hf : _root_.Manifold.IsSmoothEmbedding I J ∞ f) (hsub : _root_.Set.range f ⊆ φ.source) :
    IsSmoothEmbedding I J ∞ (φ ∘ f) := by
  have hlocal : IsLocalDiffeomorphOn J J ∞ φ.symm (_root_.Set.range (φ ∘ f)) := by
    rintro ⟨y, x, rfl⟩
    exact φ.symm.isLocalDiffeomorphAt J J ∞ (φ.map_source (hsub (_root_.Set.mem_range_self x)))
  exact ⟨(isImmersionOfComplement_of_lift_through_localDiffeomorphOn hlocal
    hf.isImmersion.isImmersionOfComplement_complement
    (contMDiff_comp_partialDiffeomorph φ hf.contMDiff hsub).continuous
    (fun x ↦ φ.left_inv (hsub (_root_.Set.mem_range_self x)))).isImmersion,
    isEmbedding_comp_partialDiffeomorph φ hf.isEmbedding hsub⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph ``Submission.DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph

theorem injective_mfderiv_comp_partialDiffeomorph
    (φ : PartialDiffeomorph J J M N ∞) {f : W → M}
    (hf : ContMDiff I J ∞ f) (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (hsub : _root_.Set.range f ⊆ φ.source) (x : W) :
    Function.Injective (mfderiv I J (φ ∘ f) x) := by
  have hmd : φ.toOpenPartialHomeomorph.MDifferentiable J J :=
    ⟨φ.contMDiffOn_toFun.mdifferentiableOn (by decide),
      φ.contMDiffOn_invFun.mdifferentiableOn (by decide)⟩
  change Function.Injective (mfderiv I J (φ.toOpenPartialHomeomorph ∘ f) x)
  rw [mfderiv_comp x (hmd.mdifferentiableAt (hsub (_root_.Set.mem_range_self x)))
    (hf.mdifferentiable (by decide) x)]
  exact (hmd.mfderiv_injective (hsub (_root_.Set.mem_range_self x))).comp (hinj x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.injective_mfderiv_comp_partialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.injective_mfderiv_comp_partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.injective_mfderiv_comp_partialDiffeomorph ``Submission.DifferentialGeometry.Topology.injective_mfderiv_comp_partialDiffeomorph

end DifferentialGeometry.Topology
