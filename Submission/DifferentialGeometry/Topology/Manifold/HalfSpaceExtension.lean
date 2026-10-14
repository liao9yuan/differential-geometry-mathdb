import Submission.DifferentialGeometry.Analysis.Calculus.SmoothExtension.HalfSpaceExtension
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Filter
open scoped _root_.Topology _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Topology

variable {X E M : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_contMDiffOn_extension_across_halfSpace_boundary
    {f : X × ℝ → M} {U : Set (X × ℝ)} {p : X}
    (hU : IsOpen U) (hp : (p, (0 : ℝ)) ∈ U)
    (hf : ContMDiffOn 𝓘(ℝ, X × ℝ) I ∞ f (U ∩ (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ)))) :
    ∃ V : Set (X × ℝ), IsOpen V ∧ (p, (0 : ℝ)) ∈ V ∧ V ⊆ U ∧
      ∃ g : X × ℝ → M, ContMDiffOn 𝓘(ℝ, X × ℝ) I ∞ g V ∧
        EqOn g f (V ∩ (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ))) := by
  let e : OpenPartialHomeomorph M E :=
    { toPartialEquiv := extChartAt I (f (p, 0))
      continuousOn_toFun := continuousOn_extChartAt _
      continuousOn_invFun := continuousOn_extChartAt_symm _
      open_source := isOpen_extChartAt_source _
      open_target := isOpen_extChartAt_target _ }
  have hpe : f (p, 0) ∈ e.source := mem_extChartAt_source _
  have he : ContMDiffOn I 𝓘(ℝ, E) ∞ e e.source := by
    change ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I (f (p, 0)))
      (extChartAt I (f (p, 0))).source
    rw [extChartAt_source]
    exact contMDiffOn_extChartAt (I := I) (n := ∞) (x := f (p, 0))
  have hei : ContMDiffOn 𝓘(ℝ, E) I ∞ e.symm e.target :=
    contMDiffOn_extChartAt_symm (I := I) (f (p, 0))
  obtain ⟨W, hW, hpW, hWf⟩ := mem_nhdsWithin.mp
    ((hf.continuousOn (p, 0) ⟨hp, _root_.Set.mem_univ _, show (0 : ℝ) ≤ 0 from le_rfl⟩).preimage_mem_nhdsWithin
      (e.open_source.mem_nhds hpe))
  let A := U ∩ W
  have hAf : _root_.Set.MapsTo f (A ∩ (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ))) e.source := by
    intro x hx
    exact hWf ⟨hx.1.2, hx.1.1, hx.2⟩
  have hfc : ContDiffOn ℝ ∞ (e ∘ f) (A ∩ (_root_.Set.univ ×ˢ _root_.Set.Ici (0 : ℝ))) :=
    (he.comp (hf.mono (_root_.Set.inter_subset_inter_left _ _root_.Set.inter_subset_left)) hAf).contDiffOn
  obtain ⟨V, hV, hpV, hVA, g, hg, heq⟩ :=
    DifferentialGeometry.Analysis.exists_contDiffOn_extension_across_halfSpace_boundary
      (hU.inter hW) ⟨hp, hpW⟩ hfc
  have hgp : g (p, 0) = e (f (p, 0)) := heq ⟨hpV, _root_.Set.mem_univ _, show (0 : ℝ) ≤ 0 from le_rfl⟩
  let N := V ∩ g ⁻¹' e.target
  have hN : IsOpen N := hg.continuousOn.isOpen_inter_preimage hV e.open_target
  have hpN : (p, (0 : ℝ)) ∈ N := by
    refine ⟨hpV, ?_⟩
    change g (p, 0) ∈ e.target
    rw [hgp]
    exact e.map_source hpe
  refine ⟨N, hN, hpN, (inter_subset_left.trans hVA).trans _root_.Set.inter_subset_left,
    e.symm ∘ g, hei.comp (hg.mono _root_.Set.inter_subset_left).contMDiffOn (fun x hx => hx.2), ?_⟩
  intro x hx
  change e.symm (g x) = f x
  rw [heq ⟨hx.1.1, hx.2⟩]
  exact e.left_inv (hAf ⟨hVA hx.1.1, hx.2⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_contMDiffOn_extension_across_halfSpace_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_contMDiffOn_extension_across_halfSpace_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_contMDiffOn_extension_across_halfSpace_boundary ``Submission.DifferentialGeometry.Topology.exists_contMDiffOn_extension_across_halfSpace_boundary

end DifferentialGeometry.Topology
