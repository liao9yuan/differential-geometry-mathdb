/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Manifold
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLImage

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology
open scoped _root_.Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {n m p : ℕ} {M N P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin p)) P]

theorem IsPLAt.comp_isPLWithinAt {f : M → N} {g : N → P} {s : Set M} {x : M}
    (hg : IsPLAt m p g (f x)) (hf : IsPLWithinAt n m f s x) :
    IsPLWithinAt n p (g ∘ f) s x := by
  let e := chartAt (EuclideanSpace ℝ (Fin n)) x
  let e' := chartAt (EuclideanSpace ℝ (Fin m)) (f x)
  let e'' := chartAt (EuclideanSpace ℝ (Fin p)) (g (f x))
  have hx : x ∈ e.source := mem_chart_source _ _
  have hfx : f x ∈ e'.source := mem_chart_source _ _
  have hgc : ContinuousAt g (f x) := by
    have hc := hg.continuousWithinAt
    rw [continuousWithinAt_univ] at hc
    exact hc
  refine ⟨hgc.comp_continuousWithinAt hf.continuousWithinAt, ?_⟩
  have hgcoord : IsPiecewiseAffineWithinAt (e'' ∘ g ∘ e'.symm) _root_.Set.univ (e' (f x)) := by
    have hc := hg.prop
    simp only [_root_.Set.preimage_univ] at hc
    exact hc
  have hpoint : (e' ∘ f ∘ e.symm) (e x) = e' (f x) := by
    change e' (f (e.symm (e x))) = e' (f x)
    rw [e.left_inv hx]
  rw [← hpoint] at hgcoord
  have hcomp := hgcoord.comp hf.prop
  rw [_root_.Set.preimage_univ, _root_.Set.inter_univ] at hcomp
  have hfc : ContinuousWithinAt f s (e.symm (e x)) := by
    rw [e.left_inv hx]
    exact hf.continuousWithinAt
  have hc : ContinuousWithinAt (f ∘ e.symm) (e.symm ⁻¹' s) (e x) :=
    hfc.comp (e.continuousAt_symm (e.map_source hx)).continuousWithinAt (fun _ hz => hz)
  have hneigh : e'.source ∈ 𝓝 (f (e.symm (e x))) := by
    rw [e.left_inv hx]
    exact e'.open_source.mem_nhds hfx
  have hevent : ∀ᶠ z in 𝓝[e.symm ⁻¹' s] (e x), f (e.symm z) ∈ e'.source :=
    hc.preimage_mem_nhdsWithin hneigh
  refine piecewiseAffineProperty_localInvariantProp.congr_nhdsWithin ?_ ?_ hcomp
  · filter_upwards [hevent] with z hz
    change e'' (g (e'.symm (e' (f (e.symm z))))) = e'' (g (f (e.symm z)))
    rw [e'.left_inv hz]
  · change e'' (g (e'.symm (e' (f (e.symm (e x)))))) = e'' (g (f (e.symm (e x))))
    rw [e.left_inv hx, e'.left_inv hfx]

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLAt
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLAt.comp_isPLWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLAt.comp_isPLWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLAt.comp_isPLWithinAt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLAt.comp_isPLWithinAt

theorem IsPL.comp_isPLOn {f : M → N} {g : N → P} {s : Set M}
    (hg : IsPL m p g) (hf : IsPLOn n m f s) : IsPLOn n p (g ∘ f) s :=
  fun x hx => IsPLAt.comp_isPLWithinAt (hg (f x)) (hf x hx)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPL
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPL.comp_isPLOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPL.comp_isPLOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPL.comp_isPLOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPL.comp_isPLOn

theorem IsPL.comp {f : M → N} {g : N → P} (hg : IsPL m p g) (hf : IsPL n m f) :
    IsPL n p (g ∘ f) := fun x => IsPLAt.comp_isPLWithinAt (hg (f x)) (hf x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPL.comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPL.comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPL.comp ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPL.comp

open _root_.Classical in
theorem IsPLOn.piecewise_postcomp_of_isClosed {f : M → N} {h : N → N} {A B : Set M}
    (hf : IsPLOn n m f (A ∪ B)) (hh : IsPL m m h) (hA : IsClosed A) (hB : IsClosed B)
    (hfix : ∀ x ∈ A ∩ B, ∀ᶠ y in 𝓝 (f x), h y = y) :
    IsPLOn n m (A.piecewise (h ∘ f) f) (A ∪ B) := by
  intro x hx
  by_cases hxA : x ∈ A
  · by_cases hxB : x ∈ B
    · have hevent : ∀ᶠ z in 𝓝[A ∪ B] x, h (f z) = f z :=
        (hf x hx).continuousWithinAt.eventually (hfix x ⟨hxA, hxB⟩)
      apply piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_eventuallyEq_of_mem
        (hf x hx) _ hx
      filter_upwards [hevent] with z hz
      by_cases hzA : z ∈ A
      · rw [_root_.Set.piecewise_eq_of_mem A (h ∘ f) f hzA]
        exact hz
      · exact _root_.Set.piecewise_eq_of_notMem A (h ∘ f) f hzA
    · apply piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_eventuallyEq_of_mem
        ((hh.comp_isPLOn hf) x hx) _ hx
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hB.isOpen_compl.mem_nhds
          hxB)]
        with z hz hzB
      exact _root_.Set.piecewise_eq_of_mem A (h ∘ f) f (hz.resolve_right hzB)
  · apply piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_eventuallyEq_of_mem
      (hf x hx) _ hx
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hA.isOpen_compl.mem_nhds hxA)] with z hz
    exact _root_.Set.piecewise_eq_of_notMem A (h ∘ f) f hz

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLOn
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLOn.piecewise_postcomp_of_isClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLOn.piecewise_postcomp_of_isClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLOn.piecewise_postcomp_of_isClosed ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLOn.piecewise_postcomp_of_isClosed

theorem IsPLWithinAt.mono_of_isPolyhedron {f : EuclideanSpace ℝ (Fin n) → N}
    {s t : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}
    (hf : IsPLWithinAt n m f s x) (ht : IsPolyhedron t) (hts : t ⊆ s) : IsPLWithinAt n m f t x := by
  refine ⟨hf.continuousWithinAt.mono hts, ?_⟩
  have hcoord := hf.prop
  change IsPiecewiseAffineWithinAt ((chartAt (EuclideanSpace ℝ (Fin m)) (f x)) ∘ f) s x at hcoord
  exact hcoord.mono_of_isPolyhedron ht hts

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLWithinAt
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLWithinAt.mono_of_isPolyhedron then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLWithinAt.mono_of_isPolyhedron"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLWithinAt.mono_of_isPolyhedron ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLWithinAt.mono_of_isPolyhedron

theorem IsPLOn.mono_of_isPolyhedron {f : EuclideanSpace ℝ (Fin n) → N}
    {s t : Set (EuclideanSpace ℝ (Fin n))} (hf : IsPLOn n m f s)
    (ht : IsPolyhedron t) (hts : t ⊆ s) : IsPLOn n m f t :=
  fun x hx => IsPLWithinAt.mono_of_isPolyhedron (hf x (hts hx)) ht hts

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLOn.mono_of_isPolyhedron then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLOn.mono_of_isPolyhedron"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLOn.mono_of_isPolyhedron ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLOn.mono_of_isPolyhedron

theorem isPLOn_iff_isPiecewiseAffineOn_comp_chart
    {f : EuclideanSpace ℝ (Fin n) → N} {s : Set (EuclideanSpace ℝ (Fin n))}
    (e : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m)))
    (he : e ∈ (plGroupoid m).maximalAtlas N) (hmap : _root_.Set.MapsTo f s e.source) :
    IsPLOn n m f s ↔ IsPiecewiseAffineOn (e ∘ f) s := by
  constructor
  · intro hf x hx
    have hc := (isPLWithinAt_iff_of_mem_maximalAtlas
      (StructureGroupoid.chart_mem_maximalAtlas (plGroupoid n) x) (mem_chart_source _ x)
      he (hmap hx)).mp (hf x hx)
    exact hc.2
  · intro hf
    have hcont : ContinuousOn f s :=
      (e.continuousOn_symm.comp hf.continuousOn (fun x hx => e.map_source (hmap hx))).congr
        (fun x hx => (e.left_inv (hmap hx)).symm)
    intro x hx
    apply (isPLWithinAt_iff_of_mem_maximalAtlas
      (StructureGroupoid.chart_mem_maximalAtlas (plGroupoid n) x) (mem_chart_source _ x)
      he (hmap hx)).mpr
    exact ⟨hcont x hx, hf x hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLOn_iff_isPiecewiseAffineOn_comp_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLOn_iff_isPiecewiseAffineOn_comp_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLOn_iff_isPiecewiseAffineOn_comp_chart ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLOn_iff_isPiecewiseAffineOn_comp_chart

theorem IsPLOn.exists_isPLHomeomorphOn_chart_image
    {f : EuclideanSpace ℝ (Fin n) → N} {s : Set (EuclideanSpace ℝ (Fin n))}
    (hf : IsPLOn n m f s) (hs : IsPolyhedron s) (hinj : _root_.Set.InjOn f s)
    (e : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m)))
    (he : e ∈ (plGroupoid m).maximalAtlas N) (hmap : _root_.Set.MapsTo f s e.source) :
    ∃ L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m)),
      L.faces.Finite ∧ L.space = (e ∘ f) '' s ∧ IsPLHomeomorphOn (e ∘ f) s L.space ∧
        L.space ⊆ e.target := by
  obtain ⟨K, hKfinite, hKs⟩ := hs.exists_simplicialComplex
  have : Finite K.faces := hKfinite.to_subtype
  have hcoord : IsPiecewiseAffineOn (e ∘ f) K.space := by
    rw [hKs]
    exact (isPLOn_iff_isPiecewiseAffineOn_comp_chart e he hmap).mp hf
  have hinjcoord : _root_.Set.InjOn (e ∘ f) K.space := by
    rw [hKs]
    exact e.injOn.comp hinj hmap
  obtain ⟨L, hLfinite, hLspace, hL⟩ := exists_isPLHomeomorphOn_image K hcoord hinjcoord
  rw [hKs] at hLspace hL
  refine ⟨L, hLfinite, hLspace, hL, ?_⟩
  rw [hLspace]
  rintro z ⟨x, hx, rfl⟩
  exact e.map_source (hmap hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLOn.exists_isPLHomeomorphOn_chart_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLOn.exists_isPLHomeomorphOn_chart_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLOn.exists_isPLHomeomorphOn_chart_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLOn.exists_isPLHomeomorphOn_chart_image

end DifferentialGeometry.Topology.PiecewiseLinear
