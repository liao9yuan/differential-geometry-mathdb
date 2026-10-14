/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CompactEmbeddingApproximation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.InwardPushStages
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCellOn

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem isPLHomeomorphInto_of_isPLOn_compact_model {N : Type*} [TopologicalSpace N]
    [T2Space N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {f : EuclideanSpace ℝ (Fin 3) → N}
    (hf : IsPLOn 3 3 f P) (hP : IsCompact P) (hinj : _root_.Set.InjOn f P) :
    IsPLHomeomorphInto 3 f P := by
  classical
  rcases P.eq_empty_or_nonempty with rfl | hPne
  · exact isPLHomeomorphInto_empty f
  have hne : Nonempty (EuclideanSpace ℝ (Fin 3)) := ⟨hPne.choose⟩
  have hcont : ContinuousOn f P := fun z hz => (hf z hz).continuousWithinAt
  have hleft : _root_.Set.LeftInvOn (Function.invFunOn f P) f P := hinj.leftInvOn_invFunOn
  have hinvcont : ContinuousOn (Function.invFunOn f P) (f '' P) :=
    continuousOn_invFunOn_image_of_isCompact hP hcont hinj
  rw [isPLHomeomorphInto_iff_exists_inverse]
  refine ⟨hf, hinj, Function.invFunOn f P, ?_, hleft⟩
  rintro _ ⟨x, hx, rfl⟩
  set e := chartAt (EuclideanSpace ℝ (Fin 3)) (f x) with he
  have hey : f x ∈ e.source := mem_chart_source _ _
  change ChartedSpace.LiftPropWithinAt (piecewiseAffineProperty 3 3)
    (Function.invFunOn f P) (f '' P) (f x)
  rw [StructureGroupoid.liftPropWithinAt_self_target]
  refine ⟨hinvcont (f x) ⟨x, hx, rfl⟩, ?_⟩
  have hfx : ChartedSpace.LiftPropWithinAt (piecewiseAffineProperty 3 3) f P x := hf x hx
  rw [StructureGroupoid.liftPropWithinAt_self_source] at hfx
  obtain ⟨-, hFpa⟩ := hfx
  obtain ⟨U, hUopen, hxU, hUsub⟩ := mem_nhdsWithin.mp
    ((hcont x hx).preimage_mem_nhdsWithin (e.open_source.mem_nhds hey))
  obtain ⟨ι, hι, C, A, hCprop, hCnhds⟩ :=
    hFpa.inter_of_mem_nhds (hUopen.mem_nhds hxU)
  have hQpoly : IsPolyhedron (⋃ i, C i) := ⟨ι, hι, C, fun i => (hCprop i).1, rfl⟩
  have hQsub : (⋃ i, C i) ⊆ P ∩ U := _root_.Set.iUnion_subset fun i => (hCprop i).2.1
  have hQsrc : ∀ z ∈ ⋃ i, C i, f z ∈ e.source := fun z hz =>
    hUsub ⟨(hQsub hz).2, (hQsub hz).1⟩
  have hFQ : IsPiecewiseAffineOn (e ∘ f) (⋃ i, C i) := by
    intro z hz
    exact ⟨ι, hι, C, A, fun i => ⟨(hCprop i).1, _root_.Set.subset_iUnion C i,
      (hCprop i).2.2⟩, self_mem_nhdsWithin⟩
  have hFinj : _root_.Set.InjOn (e ∘ f) (⋃ i, C i) := by
    intro z hz w hw hzw
    change e (f z) = e (f w) at hzw
    have hzw' : f z = f w := by
      rw [← e.left_inv (hQsrc z hz), ← e.left_inv (hQsrc w hw), hzw]
    exact hinj (hQsub hz).1 (hQsub hw).1 hzw'
  have hinvpa : IsPiecewiseAffineOn (Function.invFunOn (e ∘ f) (⋃ i, C i))
      ((e ∘ f) '' ⋃ i, C i) :=
    (isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hQpoly hFQ hFinj.bijOn_image).2.2
  have hFQsub : (e ∘ f) '' (⋃ i, C i) ⊆ e.symm ⁻¹' (f '' P) := by
    rintro _ ⟨z, hz, rfl⟩
    simp only [_root_.Set.mem_preimage, Function.comp_apply, e.left_inv (hQsrc z hz)]
    exact ⟨z, (hQsub hz).1, rfl⟩
  have hGeq : _root_.Set.EqOn (Function.invFunOn f P ∘ e.symm)
      (Function.invFunOn (e ∘ f) (⋃ i, C i)) ((e ∘ f) '' ⋃ i, C i) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hFinj.leftInvOn_invFunOn hz]
    simp only [Function.comp_apply, e.left_inv (hQsrc z hz), hleft (hQsub hz).1]
  have hxPU : x ∈ P ∩ U := ⟨hx, hxU⟩
  have hxQ : x ∈ ⋃ i, C i := mem_of_mem_nhdsWithin hxPU hCnhds
  have hyQ : e (f x) ∈ (e ∘ f) '' ⋃ i, C i := by
    refine ⟨x, hxQ, ?_⟩
    simp only [Function.comp_apply]
  obtain ⟨V, hVopen, hxV, hVsub⟩ := mem_nhdsWithin.mp hCnhds
  have hPV : ∀ z ∈ P, z ∈ V ∩ U → z ∈ ⋃ i, C i := by
    intro z hz hzVU
    exact hVsub ⟨hzVU.1, hz, hzVU.2⟩
  have hVUopen : IsOpen (V ∩ U) := hVopen.inter hUopen
  have hclosed : IsClosed (f '' (P \ (V ∩ U))) :=
    ((hP.diff hVUopen).image_of_continuousOn (hcont.mono Set.sdiff_subset)).isClosed
  have hynot : f x ∉ f '' (P \ (V ∩ U)) := by
    rintro ⟨z, hz, hzx⟩
    have hzx' : z = x := hinj hz.1 hx hzx
    exact hz.2 (hzx' ▸ ⟨hxV, hxU⟩)
  have hOopen : IsOpen (e.target ∩ e.symm ⁻¹' (f '' (P \ (V ∩ U)))ᶜ) :=
    e.isOpen_inter_preimage_symm hclosed.isOpen_compl
  have hyO : e (f x) ∈ e.target ∩ e.symm ⁻¹' (f '' (P \ (V ∩ U)))ᶜ :=
    ⟨e.map_source hey, by simp only [_root_.Set.mem_preimage, e.left_inv hey]; exact hynot⟩
  have hkey : e.symm ⁻¹' (f '' P) ∩ e.target ∩ e.symm ⁻¹' (f '' (P \ (V ∩ U)))ᶜ ⊆
      (e ∘ f) '' ⋃ i, C i := by
    intro w hw
    rcases hw with ⟨⟨hwimage, hwtarget⟩, hwout⟩
    rcases hwimage with ⟨z, hz, hzw⟩
    have hzVU : z ∈ V ∩ U := by
      by_contra hcon
      exact hwout ⟨z, ⟨hz, hcon⟩, hzw⟩
    refine ⟨z, hPV z hz hzVU, ?_⟩
    simp only [Function.comp_apply, hzw]
    exact e.right_inv hwtarget
  obtain ⟨κ, hκ, D, B, hDprop, hDnhds⟩ := hinvpa (e (f x)) hyQ
  obtain ⟨W, hWopen, hyW, hWsub⟩ := mem_nhdsWithin.mp hDnhds
  refine ⟨κ, hκ, D, B, fun j => ⟨(hDprop j).1, ((hDprop j).2.1).trans hFQsub, ?_⟩, ?_⟩
  · exact fun w hw => (hGeq ((hDprop j).2.1 hw)).trans ((hDprop j).2.2 hw)
  · refine mem_nhdsWithin.mpr ⟨W ∩ (e.target ∩ e.symm ⁻¹' (f '' (P \ (V ∩ U)))ᶜ),
      hWopen.inter hOopen, ⟨hyW, hyO⟩, ?_⟩
    rintro w ⟨⟨hwW, hwout⟩, hwimage⟩
    exact hWsub ⟨hwW, hkey ⟨⟨hwimage, hwout.1⟩, hwout.2⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphInto_of_isPLOn_compact_model
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphInto_of_isPLOn_compact_model target :: scope.openDecls } }

universe u

variable {M₁ M₂ : Type u} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [TopologicalSpace M₂] [T2Space M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]

theorem IsPLHomeomorphInto.mono_of_isPLCellOn {d : ℕ} {Z S B : Set M₁} {G : M₁ → M₂}
    (hG : IsPLHomeomorphInto 3 G Z) (hS : IsPLCellOn d S B) (hSZ : S ⊆ Z) :
    IsPLHomeomorphInto 3 G S := by
  obtain ⟨P, r, u, hr, hu, hSe, -⟩ := hS
  have hPcompact : IsCompact P := (IsPLBall.isPolyhedron ⟨r, hr⟩).isCompact
  have hmap : _root_.Set.MapsTo u P Z := by
    intro x hx
    apply hSZ
    rw [hSe]
    exact ⟨x, hx, rfl⟩
  have hGu : IsPLOn 3 3 (G ∘ u) P :=
    IsPLOn.comp_of_mapsTo hG.isPLOn hu.isPLOn hmap
  have hGuinj : _root_.Set.InjOn (G ∘ u) P := by
    intro x hx y hy hxy
    exact hu.injOn hx hy (hG.injOn (hmap hx) (hmap hy) hxy)
  have hGuemb : IsPLHomeomorphInto 3 (G ∘ u) P :=
    isPLHomeomorphInto_of_isPLOn_compact_model hGu hPcompact hGuinj
  have huleft : _root_.Set.LeftInvOn (Function.invFunOn u P) u P := hu.injOn.leftInvOn_invFunOn
  have humap : _root_.Set.MapsTo (Function.invFunOn u P) (u '' P) P :=
    hu.injOn.bijOn_image.surjOn.mapsTo_invFunOn
  have huinv : IsPLOn 3 3 (Function.invFunOn u P) (u '' P) :=
    hu.isPLOn_inverse huleft
  have hGup : IsPLOn 3 3 ((G ∘ u) ∘ Function.invFunOn u P) (u '' P) :=
    IsPLOn.comp_of_mapsTo hGuemb.isPLOn huinv humap
  have hGimage : IsPLOn 3 3 G (u '' P) := fun y hy =>
    piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem (hGup y hy)
      (by
        rintro z ⟨x, hx, rfl⟩
        simp only [Function.comp_apply, huleft hx]) hy
  have hGpl : IsPLOn 3 3 G S := by
    rw [hSe]
    exact hGimage
  have hGim : G '' S = (G ∘ u) '' P := by
    rw [hSe]
    exact (_root_.Set.image_comp G u P).symm
  have hFleft : _root_.Set.LeftInvOn (Function.invFunOn (G ∘ u) P) (G ∘ u) P :=
    hGuemb.injOn.leftInvOn_invFunOn
  have hFinv : IsPLOn 3 3 (Function.invFunOn (G ∘ u) P) ((G ∘ u) '' P) :=
    hGuemb.isPLOn_inverse hFleft
  have hFmap : _root_.Set.MapsTo (Function.invFunOn (G ∘ u) P) ((G ∘ u) '' P) P :=
    hGuemb.injOn.bijOn_image.surjOn.mapsTo_invFunOn
  have hleftpl : IsPLOn 3 3 (u ∘ Function.invFunOn (G ∘ u) P) ((G ∘ u) '' P) :=
    IsPLOn.comp_of_mapsTo hu.isPLOn hFinv hFmap
  refine ⟨hGpl, hG.injOn.mono hSZ, ?_⟩
  intro y hy
  refine ⟨u ∘ Function.invFunOn (G ∘ u) P, hGim ▸ hleftpl y (hGim ▸ hy), ?_⟩
  intro x hx
  rw [hSe] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  change u (Function.invFunOn (G ∘ u) P ((G ∘ u) z)) = u z
  rw [hFleft hz]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.mono_of_isPLCellOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.mono_of_isPLCellOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.mono_of_isPLCellOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.mono_of_isPLCellOn

end DifferentialGeometry.Topology.PiecewiseLinear
