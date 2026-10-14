/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.StableCrossingBlockPerturbation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Manifold
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.OpenStar
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.StarComplex
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Subdivision
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.GluedCellGlobalInvariants

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology _root_.Metric
open scoped _root_.Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Model

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem exists_isOpen_inter_space_subset_closedStar (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] {z : E} (hz : z ∈ K.space) :
    ∃ w ∈ K.vertices, ∃ G : Set E, IsOpen G ∧ z ∈ G ∧ G ∩ K.space ⊆ closedStar K w := by
  obtain ⟨w, hw, hzw⟩ := exists_vertex_mem_openStar K hz
  refine ⟨w, hw, (avoidingUnion K w)ᶜ, (isClosed_avoidingUnion K w).isOpen_compl, hzw.2, ?_⟩
  rintro x ⟨hxG, hxK⟩
  exact openStar_subset_closedStar K hw ⟨hxK, hxG⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isOpen_inter_space_subset_closedStar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isOpen_inter_space_subset_closedStar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isOpen_inter_space_subset_closedStar ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isOpen_inter_space_subset_closedStar

open _root_.Classical in
theorem exists_injOn_closedStar_of_small_vertex_perturbation [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (φ₀ : E → F)
    (hinj : ∀ v ∈ K.vertices, _root_.Set.InjOn (simplicialMap K φ₀) (closedStar K v)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : E → F, (∀ v ∈ K.vertices, _root_.Dist.dist (φ v) (φ₀ v) < δ) →
      ∀ v ∈ K.vertices, _root_.Set.InjOn (simplicialMap K φ) (closedStar K v) := by
  obtain ⟨δ, hδ, h⟩ := exists_injOn_starComplex_of_small_vertex_perturbation K φ₀
    fun v hv => by
      rw [starComplex_space K v hv]
      exact hinj v hv
  refine ⟨δ, hδ, fun φ hφ v hv => ?_⟩
  have h1 := h φ hφ v hv
  rwa [starComplex_space K v hv] at h1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_injOn_closedStar_of_small_vertex_perturbation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_injOn_closedStar_of_small_vertex_perturbation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_injOn_closedStar_of_small_vertex_perturbation ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_injOn_closedStar_of_small_vertex_perturbation

open _root_.Classical in
theorem starInj_of_forall_injOn_nhds [FiniteDimensional ℝ E] {X : Type*} [MetricSpace X]
    (T : Geometry.SimplicialComplex ℝ E) [Finite T.faces] {D : E → X}
    (hD : ContinuousOn D T.space) (hTstar : StarInj T D) (P : (E → X) → Prop)
    (hloc : ∀ z ∈ T.space, ∃ G : Set E, IsOpen G ∧ z ∈ G ∧ ∀ g, P g → _root_.Set.InjOn g (T.space ∩ G)) :
    ∃ m : ℝ, 0 < m ∧ ∀ g, P g → (∀ x ∈ T.space, _root_.Dist.dist (g x) (D x) < m) → StarInj T g := by
  choose G hGo hzG hGinj using hloc
  have hTc : IsCompact T.space := (isPolyhedron_space T).isCompact
  obtain ⟨β, hβ, hleb⟩ := lebesgue_number_lemma_of_metric hTc
    (c := fun p : T.space => G p p.2) (fun p => hGo p p.2)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hzG x hx⟩)
  have hvert : T.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite T.faces)
  have hStS : ∀ v, (starComplex T v).space ⊆ T.space := fun v =>
    space_mono_of_faces_subset (starComplex_faces_subset T v)
  have hStc : ∀ v, IsCompact (starComplex T v).space := by
    intro v
    have : Finite (starComplex T v).faces := (starComplex_faces_finite T v).to_subtype
    exact (isPolyhedron_space (starComplex T v)).isCompact
  set P₀ : Set (E × E) := ⋃ v ∈ T.vertices,
    ((starComplex T v).space ×ˢ (starComplex T v).space) ∩ {p | β ≤ _root_.Dist.dist p.1 p.2} with hP₀
  have hP₀c : IsCompact P₀ := hvert.isCompact_biUnion fun v _ =>
    ((hStc v).prod (hStc v)).inter_right (isClosed_le continuous_const continuous_dist)
  have hP₀T : ∀ p ∈ P₀, p.1 ∈ T.space ∧ p.2 ∈ T.space := by
    intro p hp
    obtain ⟨v, -, hpv⟩ := mem_iUnion₂.mp hp
    exact ⟨hStS v hpv.1.1, hStS v hpv.1.2⟩
  have hnear : ∀ g, P g → ∀ v, ∀ x ∈ (starComplex T v).space, ∀ y ∈ (starComplex T v).space,
      dist x y < β → g x = g y → x = y := by
    intro g hg v x hx y hy hd hxy
    obtain ⟨p, hp⟩ := hleb x (hStS v hx)
    exact hGinj p p.2 g hg ⟨hStS v hx, hp (_root_.Metric.mem_ball_self hβ)⟩
      ⟨hStS v hy, hp (by rw [_root_.Metric.mem_ball, dist_comm]; exact hd)⟩ hxy
  by_cases hne : P₀.Nonempty
  · have hF1 : ContinuousOn (fun p : E × E => D p.1) P₀ :=
      hD.comp continuous_fst.continuousOn fun p hp => (hP₀T p hp).1
    have hF2 : ContinuousOn (fun p : E × E => D p.2) P₀ :=
      hD.comp continuous_snd.continuousOn fun p hp => (hP₀T p hp).2
    have hF : ContinuousOn (fun p : E × E => _root_.Dist.dist (D p.1) (D p.2)) P₀ :=
      continuous_dist.comp_continuousOn (hF1.prodMk hF2)
    obtain ⟨p₀, hp₀, hmin⟩ := hP₀c.exists_isMinOn hne hF
    obtain ⟨v₀, hv₀, hp₀v⟩ := mem_iUnion₂.mp hp₀
    have hm₁ : 0 < _root_.Dist.dist (D p₀.1) (D p₀.2) := by
      refine dist_pos.mpr fun heq => ?_
      have h1 : p₀.1 = p₀.2 := hTstar v₀ hv₀ hp₀v.1.1 hp₀v.1.2 heq
      have h2 : β ≤ _root_.Dist.dist p₀.1 p₀.2 := hp₀v.2
      rw [h1, dist_self] at h2
      linarith
    refine ⟨dist (D p₀.1) (D p₀.2) / 2, half_pos hm₁, fun g hg hgD => ?_⟩
    unfold StarInj
    intro v hv x hx y hy hxy
    by_cases hd : _root_.Dist.dist x y < β
    · exact hnear g hg v x hx y hy hd hxy
    · exfalso
      have hpP : (x, y) ∈ P₀ := mem_iUnion₂.mpr ⟨v, hv, ⟨hx, hy⟩, not_lt.mp hd⟩
      have h1 : _root_.Dist.dist (D p₀.1) (D p₀.2) ≤ _root_.Dist.dist (D x) (D y) := isMinOn_iff.mp hmin _ hpP
      have h2 : _root_.Dist.dist (D x) (D y) ≤ _root_.Dist.dist (D x) (g x) + _root_.Dist.dist (g y) (D y) := by
        calc _root_.Dist.dist (D x) (D y) ≤ _root_.Dist.dist (D x) (g x) + _root_.Dist.dist (g x) (D y) := dist_triangle _ _ _
          _ = _root_.Dist.dist (D x) (g x) + _root_.Dist.dist (g y) (D y) := by rw [hxy]
      have h3 := hgD x (hStS v hx)
      have h4 := hgD y (hStS v hy)
      rw [dist_comm] at h3
      linarith
  · refine ⟨1, one_pos, fun g hg _ => ?_⟩
    unfold StarInj
    intro v hv x hx y hy hxy
    by_cases hd : _root_.Dist.dist x y < β
    · exact hnear g hg v x hx y hy hd hxy
    · exact absurd ⟨(x, y), mem_iUnion₂.mpr ⟨v, hv, ⟨hx, hy⟩, not_lt.mp hd⟩⟩ hne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.starInj_of_forall_injOn_nhds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.starInj_of_forall_injOn_nhds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.starInj_of_forall_injOn_nhds ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.starInj_of_forall_injOn_nhds

theorem IsSubdivision.convexHull_carrierFace_subset {K K' L : Geometry.SimplicialComplex ℝ E}
    (h : IsSubdivision K' K) (hLK : L.faces ⊆ K.faces) {x : E} (hx : x ∈ L.space) :
    convexHull ℝ ((carrierFace K' x : Finset E) : Set E) ⊆ L.space := by
  obtain ⟨t, ht, hxt⟩ := L.mem_space_iff.mp hx
  have hxK : x ∈ K.space := K.convexHull_subset_space (hLK ht) hxt
  have hxK' : x ∈ K'.space := h.space_eq ▸ hxK
  exact (h.convexHull_subset_of_mem_openSimplex (hLK ht) (carrierFace_mem hxK')
    (mem_openSimplex_carrierFace hxK') hxt).trans (L.convexHull_subset_space ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsSubdivision.convexHull_carrierFace_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsSubdivision.convexHull_carrierFace_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsSubdivision.convexHull_carrierFace_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsSubdivision.convexHull_carrierFace_subset

theorem IsSubdivision.simplicialMap_eqOn_of_eqOn_vertices
    {K K' L : Geometry.SimplicialComplex ℝ E} (h : IsSubdivision K' K) (hLK : L.faces ⊆ K.faces)
    {φ ψ : E → F} (hφψ : ∀ v ∈ K'.vertices, v ∈ L.space → φ v = ψ v) :
    EqOn (simplicialMap K' φ) (simplicialMap K' ψ) L.space := by
  intro x hx
  have hxK : x ∈ K.space := by
    obtain ⟨t, ht, hxt⟩ := L.mem_space_iff.mp hx
    exact K.convexHull_subset_space (hLK ht) hxt
  have hxK' : x ∈ K'.space := h.space_eq ▸ hxK
  have hc := carrierFace_mem hxK'
  have hxc := mem_convexHull_carrierFace hxK'
  have hsub := h.convexHull_carrierFace_subset hLK hx
  rw [simplicialMap_eq_of_mem K' φ hc hxc, simplicialMap_eq_of_mem K' ψ hc hxc]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [hφψ v (K'.down_closed hc (Finset.singleton_subset_iff.mpr hv)
    (Finset.singleton_nonempty v)) (hsub (subset_convexHull ℝ _ hv))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsSubdivision.simplicialMap_eqOn_of_eqOn_vertices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsSubdivision.simplicialMap_eqOn_of_eqOn_vertices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsSubdivision.simplicialMap_eqOn_of_eqOn_vertices ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsSubdivision.simplicialMap_eqOn_of_eqOn_vertices

theorem simplicialMap_sub (K : Geometry.SimplicialComplex ℝ E) (φ ψ : E → F) {x : E}
    (hx : x ∈ K.space) :
    simplicialMap K (fun v => φ v - ψ v) x = simplicialMap K φ x - simplicialMap K ψ x := by
  have hc := carrierFace_mem hx
  have hxc := mem_convexHull_carrierFace hx
  rw [simplicialMap_eq_of_mem K _ hc hxc, simplicialMap_eq_of_mem K φ hc hxc,
    simplicialMap_eq_of_mem K ψ hc hxc, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun v _ => smul_sub _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.simplicialMap_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.simplicialMap_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.simplicialMap_sub ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.simplicialMap_sub

end Model

theorem OpenPartialHomeomorph.exists_pos_dist_symm_lt {X : Type*} [MetricSpace X]
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3)))
    {K₁ : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K₁) (hKt : K₁ ⊆ e.target) {θ : ℝ}
    (hθ : 0 < θ) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ k ∈ K₁, ∀ z, _root_.Dist.dist z k < τ →
      z ∈ e.target ∧ _root_.Dist.dist (e.symm z) (e.symm k) < θ := by
  obtain ⟨ρ, hρ, hsub⟩ := hK.exists_cthickening_subset_open e.open_target hKt
  have hKc : IsCompact (_root_.Metric.cthickening ρ K₁) := hK.cthickening
  have huc : UniformContinuousOn e.symm (_root_.Metric.cthickening ρ K₁) :=
    hKc.uniformContinuousOn_of_continuous (e.continuousOn_symm.mono hsub)
  obtain ⟨τ₁, hτ₁, hτ₁'⟩ := Metric.uniformContinuousOn_iff.mp huc θ hθ
  refine ⟨min ρ τ₁, lt_min hρ hτ₁, fun k hk z hz => ?_⟩
  have hzc : z ∈ _root_.Metric.cthickening ρ K₁ :=
    _root_.Metric.mem_cthickening_of_dist_le z k ρ K₁ hk (hz.le.trans (min_le_left _ _))
  have hkc : k ∈ _root_.Metric.cthickening ρ K₁ := _root_.Metric.self_subset_cthickening K₁ hk
  exact ⟨hsub hzc, hτ₁' z hzc k hkc (hz.trans_le (min_le_right _ _))⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.OpenPartialHomeomorph
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.OpenPartialHomeomorph.exists_pos_dist_symm_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.OpenPartialHomeomorph.exists_pos_dist_symm_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.OpenPartialHomeomorph.exists_pos_dist_symm_lt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.OpenPartialHomeomorph.exists_pos_dist_symm_lt

section Ambient

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem SingularTwoCell.isPiecewiseAffineWithinAt_chart_comp (D : SingularTwoCell M)
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    (hec : ec ∈ (plGroupoid 3).maximalAtlas M) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ D.domain) (hxs : D x ∈ ec.source) :
    IsPiecewiseAffineWithinAt (fun y => ec (D y)) (D.domain ∩ ⇑D ⁻¹' ec.source) x := by
  obtain ⟨hcont, hpl⟩ := D.isPLOn x hx
  set c := chartAt (EuclideanSpace ℝ (Fin 3)) (D x)
  have hcoord : IsPiecewiseAffineWithinAt (⇑c ∘ ⇑D) D.domain x := hpl
  have hT : c.symm ≫ₕ ec ∈ plGroupoid 3 :=
    StructureGroupoid.compatible_of_mem_maximalAtlas_right hec
  have hTpl := (mem_plGroupoid_iff.mp hT).1
  have hDxc : D x ∈ c.source := mem_chart_source _ _
  have hmem : c (D x) ∈ (c.symm ≫ₕ ec).source := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    refine ⟨c.map_source hDxc, ?_⟩
    rw [_root_.Set.mem_preimage, c.left_inv hDxc]
    exact hxs
  have hcomp := IsPiecewiseAffineWithinAt.comp (f := ⇑c ∘ ⇑D) (x := x) (hTpl (c (D x)) hmem)
    hcoord
  obtain ⟨W, hWo, hxW, hWsub⟩ :=
    mem_nhdsWithin.mp (hcont.preimage_mem_nhdsWithin (c.open_source.mem_nhds hDxc))
  have hset : (D.domain ∩ (⇑c ∘ ⇑D) ⁻¹' (c.symm ≫ₕ ec).source) ∩ W =
      (D.domain ∩ ⇑D ⁻¹' ec.source) ∩ W := by
    ext y
    constructor
    · rintro ⟨⟨hyD, hyT⟩, hyW⟩
      have hyc : D y ∈ c.source := hWsub ⟨hyW, hyD⟩
      refine ⟨⟨hyD, ?_⟩, hyW⟩
      rw [_root_.Set.mem_preimage, Function.comp_apply, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source] at hyT
      have h2 := hyT.2
      rw [_root_.Set.mem_preimage, c.left_inv hyc] at h2
      exact h2
    · rintro ⟨⟨hyD, hyE⟩, hyW⟩
      have hyc : D y ∈ c.source := hWsub ⟨hyW, hyD⟩
      refine ⟨⟨hyD, ?_⟩, hyW⟩
      rw [_root_.Set.mem_preimage, Function.comp_apply, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source]
      refine ⟨c.map_source hyc, ?_⟩
      rw [_root_.Set.mem_preimage, c.left_inv hyc]
      exact hyE
  have h1 := hcomp.inter_of_mem_nhds (hWo.mem_nhds hxW)
  rw [hset] at h1
  refine (h1.congr ?_).of_inter_of_mem_nhds (hWo.mem_nhds hxW)
  rintro y ⟨⟨hyD, -⟩, hyW⟩
  have hyc : D y ∈ c.source := hWsub ⟨hyW, hyD⟩
  simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans, c.left_inv hyc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.isPiecewiseAffineWithinAt_chart_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.isPiecewiseAffineWithinAt_chart_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.isPiecewiseAffineWithinAt_chart_comp ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.isPiecewiseAffineWithinAt_chart_comp

theorem SingularTwoCell.isPiecewiseAffineOn_chart_comp (D : SingularTwoCell M)
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    (hec : ec ∈ (plGroupoid 3).maximalAtlas M) {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hP : IsPolyhedron P) (hPD : P ⊆ D.domain) (hPs : P ⊆ ⇑D ⁻¹' ec.source) :
    IsPiecewiseAffineOn (fun y => ec (D y)) P := fun _ hx =>
  (D.isPiecewiseAffineWithinAt_chart_comp hec (hPD hx) (hPs hx)).mono_of_isPolyhedron hP
    fun _ hy => ⟨hPD hy, hPs hy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.isPiecewiseAffineOn_chart_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.isPiecewiseAffineOn_chart_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.isPiecewiseAffineOn_chart_comp ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.isPiecewiseAffineOn_chart_comp

end Ambient

end DifferentialGeometry.Topology.PiecewiseLinear
