import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter _root_.Topology _root_.Manifold
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E F H G X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace H X] [ChartedSpace G Y]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}

theorem exists_partialDiffeomorph_of_injOn [Nonempty X]
    {f : X → Y} {S : Set X} {n : ℕ∞ω} (hS : IsOpen S)
    (hf : IsLocalDiffeomorphOn I J n f S) (hinj : _root_.Set.InjOn f S) :
    ∃ d : PartialDiffeomorph I J X Y n,
      d.source = S ∧ d.target = f '' S ∧ (d : X → Y) = f := by
  let e₀ := hinj.toPartialEquiv f S
  have hopen : IsOpenMap (S.domRestrict f) := by
    apply IsOpenMap.of_nhds_le
    intro x
    change 𝓝 (f x.1) ≤ Filter.map (f ∘ Subtype.val) (𝓝 x)
    rw [← Filter.map_map, hS.isOpenEmbedding_subtypeVal.map_nhds_eq]
    exact (hf.isLocalHomeomorphOn.map_nhds_eq x.2).ge
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict e₀ hf.contMDiffOn.continuousOn hopen hS
  have hi : ContMDiffOn J I n e.symm e.target := by
    intro y hy
    obtain ⟨d, hxd, heq⟩ := hf ⟨e.symm y, e.map_target hy⟩
    have hpoint : d (e.symm y) = y := (heq hxd).symm.trans (e.right_inv hy)
    have hdy : y ∈ d.target := by
      rw [← hpoint]
      exact d.toOpenPartialHomeomorph.map_source hxd
    have hleft : d.symm y = e.symm y := by
      conv_lhs => rw [← hpoint]
      exact d.toOpenPartialHomeomorph.left_inv hxd
    let U := d.target ∩ d.symm ⁻¹' S
    have hU : IsOpen U := d.toOpenPartialHomeomorph.isOpen_inter_preimage_symm hS
    have hyU : y ∈ U := ⟨hdy, by change d.symm y ∈ S; rw [hleft]; exact e.map_target hy⟩
    have hmatch : ∀ z ∈ U, e.symm z = d.symm z := by
      intro z hz
      have hdz := d.toOpenPartialHomeomorph.map_target hz.1
      have hright : f (d.symm z) = z := by
        exact (heq (show d.symm z ∈ d.source from hdz)).trans
          (d.toOpenPartialHomeomorph.right_inv hz.1)
      have hze : z ∈ e.target := ⟨d.symm z, hz.2, hright⟩
      exact hinj (e.map_target hze) hz.2 ((e.right_inv hze).trans hright.symm)
    exact ((d.symm.contMDiffOn.contMDiffAt (d.open_target.mem_nhds hdy)).congr_of_eventuallyEq
      (Filter.eventually_of_mem (hU.mem_nhds hyU) hmatch)).contMDiffWithinAt
  exact ⟨{ toPartialEquiv := e.toPartialEquiv
           open_source := hS
           open_target := e.open_target
           contMDiffOn_toFun := hf.contMDiffOn
           contMDiffOn_invFun := hi }, rfl, rfl, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_injOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_injOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_injOn ``Submission.DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_injOn

end DifferentialGeometry.Topology.Manifold
