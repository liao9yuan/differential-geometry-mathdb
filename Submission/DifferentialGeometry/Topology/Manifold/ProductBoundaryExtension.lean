import Submission.DifferentialGeometry.Topology.Manifold.HalfSpaceExtension
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

variable {F HS S E HM M : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace HS] {J : ModelWithCorners ℝ F HS} [J.Boundaryless]
  [TopologicalSpace S] [ChartedSpace HS S] [IsManifold J ∞ S]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace HM] {I : ModelWithCorners ℝ E HM} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M]

theorem exists_contMDiffOn_extension_across_product_boundary
    {f : S × ℝ → M} {U : Set (S × ℝ)} {p : S}
    (hU : IsOpen U) (hp : (p, (0 : ℝ)) ∈ U)
    (hf : ContMDiffOn (J.prod 𝓘(ℝ)) I ∞ f (U ∩ (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ)))) :
    ∃ V : Set (S × ℝ), IsOpen V ∧ (p, (0 : ℝ)) ∈ V ∧ V ⊆ U ∧
      ∃ g : S × ℝ → M, ContMDiffOn (J.prod 𝓘(ℝ)) I ∞ g V ∧
        EqOn g f (V ∩ (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ))) := by
  let e := PartialDiffeomorph.extendedChart (I := J) p
  let φ := PartialDiffeomorph.prod e (Diffeomorph.refl 𝓘(ℝ) ℝ ∞).toPartialDiffeomorph
  have hps : (p, (0 : ℝ)) ∈ φ.source := by
    exact ⟨mem_extChartAt_source p, _root_.Set.mem_univ _⟩
  let A := φ.target ∩ φ.invFun ⁻¹' U
  have hA : IsOpen A := φ.toOpenPartialHomeomorph.isOpen_inter_preimage_symm hU
  have hpA : (e p, (0 : ℝ)) ∈ A := by
    refine ⟨φ.map_source hps, ?_⟩
    change φ.invFun (φ (p, 0)) ∈ U
    rw [φ.left_inv' hps]
    exact hp
  have hφi : ContMDiffOn 𝓘(ℝ, F × ℝ) (J.prod 𝓘(ℝ)) ∞ φ.invFun φ.target := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact φ.contMDiffOn_invFun
  have hφ : ContMDiffOn (J.prod 𝓘(ℝ)) 𝓘(ℝ, F × ℝ) ∞ φ φ.source := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact φ.contMDiffOn_toFun
  have hfc : ContMDiffOn 𝓘(ℝ, F × ℝ) I ∞ (f ∘ φ.invFun)
      (A ∩ (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ))) := by
    apply hf.comp (hφi.mono (fun _ hx => hx.1.1))
    intro x hx
    exact ⟨hx.1.2, hx.2⟩
  obtain ⟨W, hW, hpW, hWA, g, hg, heq⟩ :=
    exists_contMDiffOn_extension_across_halfSpace_boundary hA hpA hfc
  let V := φ.source ∩ φ ⁻¹' W
  have hV : IsOpen V := φ.toOpenPartialHomeomorph.isOpen_inter_preimage hW
  have hpV : (p, (0 : ℝ)) ∈ V := ⟨hps, hpW⟩
  have hVU : V ⊆ U := by
    intro x hx
    have hxU := (hWA hx.2).2
    change φ.invFun (φ x) ∈ U at hxU
    rwa [φ.left_inv' hx.1] at hxU
  refine ⟨V, hV, hpV, hVU, g ∘ φ, ?_, ?_⟩
  · exact hg.comp (hφ.mono _root_.Set.inter_subset_left) (fun _ hx => hx.2)
  · intro x hx
    change g (φ x) = f x
    rw [heq ⟨hx.1.2, hx.2⟩]
    change f (φ.invFun (φ x)) = f x
    rw [φ.left_inv' hx.1.1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_contMDiffOn_extension_across_product_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_contMDiffOn_extension_across_product_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_contMDiffOn_extension_across_product_boundary ``Submission.DifferentialGeometry.Topology.exists_contMDiffOn_extension_across_product_boundary

end DifferentialGeometry.Topology
