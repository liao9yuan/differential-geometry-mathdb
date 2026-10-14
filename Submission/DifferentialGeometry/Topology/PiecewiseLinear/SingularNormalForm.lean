/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Combinatorial
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ExhaustionGeneral
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubdivision
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPiece
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PiecewiseAffineSimplicial
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem SingularTwoCell.exists_compact_piece_neighborhood
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [T2Space M] [Nonempty M] [HasGroupoid M (plGroupoid 3)] (D : SingularTwoCell M) :
    ∃ P : Set M, ∃ T : PLPiece 3 M P, IsCompact P ∧
      IsCombinatorialManifoldWithBoundary 3 T.piece.complex ∧
        D '' D.domain ⊆ interior P := by
  classical
  have hcompact : IsCompact (D '' D.domain) :=
    D.isPLBall_domain.isPolyhedron.isCompact.image_of_continuousOn D.continuousOn
  obtain ⟨P, hPcompact, ⟨T, hT⟩, hDP, _⟩ :=
    exists_isPolyhedralManifoldWithBoundary_neighborhood (m := 2) hcompact isOpen_univ
      (_root_.Set.subset_univ _)
  exact ⟨P, T, hPcompact, hT, hDP⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.exists_compact_piece_neighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.exists_compact_piece_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.exists_compact_piece_neighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.exists_compact_piece_neighborhood

open _root_.Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isSubdivision_affineOn_faces_finite
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Finite ι]
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary n K) (f : ι → E → F)
    (hf : ∀ i, IsPiecewiseAffineOn (f i) K.space) :
    ∃ K' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K ∧ K'.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary n K' ∧
        ∀ i, ∀ s ∈ K'.faces,
          ∃ A : E →ᵃ[ℝ] F, _root_.Set.EqOn (f i) A (convexHull ℝ (s : Set E)) := by
  obtain ⟨K', hK', hfin, hface⟩ :=
    DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_affineOn_faces_finite K f hf
  let _ : Finite K'.faces := hfin.to_subtype
  exact ⟨K', hK', hfin, hK.of_isSubdivision hK', hface⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isSubdivision_affineOn_faces_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isSubdivision_affineOn_faces_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isSubdivision_affineOn_faces_finite ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isSubdivision_affineOn_faces_finite

open _root_.Classical in
theorem IsPiecewiseAffineOn.exists_isSubdivision_affineOn_subcomplex
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] (hLK : L.space ⊆ K.space)
    {f : E → F} (hf : IsPiecewiseAffineOn f L.space) :
    ∃ K' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K ∧ K'.faces.Finite ∧
      (restrict K' L.space).space = L.space ∧
        ∀ s ∈ (restrict K' L.space).faces,
          ∃ A : E →ᵃ[ℝ] F, _root_.Set.EqOn f A (convexHull ℝ (s : Set E)) := by
  obtain ⟨L', hL', hfinL', hface⟩ := hf.exists_isSubdivision_affineOn_faces L
  let _ : Finite L'.faces := hfinL'.to_subtype
  obtain ⟨K', hK', hfinK', hrest⟩ :=
    exists_isSubdivision_restrict_isSubdivision K L' (hL'.space_eq ▸ hLK)
  rw [hL'.space_eq] at hrest
  refine ⟨K', hK', hfinK', hrest.space_eq.trans hL'.space_eq, ?_⟩
  intro s hs
  obtain ⟨t, ht, hst⟩ := hrest.exists_face_subset hs
  obtain ⟨A, hA⟩ := hface t ht
  exact ⟨A, hA.mono hst⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.exists_isSubdivision_affineOn_subcomplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.exists_isSubdivision_affineOn_subcomplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.exists_isSubdivision_affineOn_subcomplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.exists_isSubdivision_affineOn_subcomplex

open _root_.Classical in
theorem exists_isSubdivision_affineOn_subcomplexes_finset
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (I : Finset ι) (L : ι → Geometry.SimplicialComplex ℝ E)
    (hLfin : ∀ i ∈ I, (L i).faces.Finite) (hLK : ∀ i ∈ I, (L i).space ⊆ K.space)
    (f : ι → E → F) (hf : ∀ i ∈ I, IsPiecewiseAffineOn (f i) (L i).space) :
    ∃ K' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K ∧ K'.faces.Finite ∧
      ∀ i ∈ I, (restrict K' (L i).space).space = (L i).space ∧
        ∀ s ∈ (restrict K' (L i).space).faces,
          ∃ A : E →ᵃ[ℝ] F, _root_.Set.EqOn (f i) A (convexHull ℝ (s : Set E)) := by
  induction I using Finset.induction_on with
  | empty =>
      refine ⟨K, IsSubdivision.refl K, Set.toFinite K.faces, ?_⟩
      simp
  | @insert i I hi ih =>
      have hLfinI : ∀ j ∈ I, (L j).faces.Finite :=
        fun j hj => hLfin j (Finset.mem_insert_of_mem hj)
      have hLKI : ∀ j ∈ I, (L j).space ⊆ K.space :=
        fun j hj => hLK j (Finset.mem_insert_of_mem hj)
      have hfI : ∀ j ∈ I, IsPiecewiseAffineOn (f j) (L j).space :=
        fun j hj => hf j (Finset.mem_insert_of_mem hj)
      obtain ⟨K₁, hK₁, hfin₁, hface₁⟩ := ih hLfinI hLKI hfI
      let _ : Finite K₁.faces := hfin₁.to_subtype
      let _ : Finite (L i).faces :=
        (hLfin i (Finset.mem_insert_self i I)).to_subtype
      have hLiK₁ : (L i).space ⊆ K₁.space := by
        rw [hK₁.space_eq]
        exact hLK i (Finset.mem_insert_self i I)
      obtain ⟨K₂, hK₂, hfin₂, hspace₂, hface₂⟩ :=
        (hf i (Finset.mem_insert_self i I)).exists_isSubdivision_affineOn_subcomplex
          K₁ (L i) hLiK₁
      refine ⟨K₂, hK₂.trans hK₁, hfin₂, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ⟨hspace₂, hface₂⟩
      · have hprev := hface₁ j hj
        have hrest := hK₂.restrict (restrict K₁ (L j).space)
          (restrict_faces_subset K₁ (L j).space)
        rw [hprev.1] at hrest
        refine ⟨hrest.space_eq.trans hprev.1, ?_⟩
        intro s hs
        obtain ⟨t, ht, hst⟩ := hrest.exists_face_subset hs
        obtain ⟨A, hA⟩ := hprev.2 t ht
        exact ⟨A, hA.mono hst⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_affineOn_subcomplexes_finset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_affineOn_subcomplexes_finset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_affineOn_subcomplexes_finset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_affineOn_subcomplexes_finset

open _root_.Classical in
theorem exists_isSubdivision_affineOn_subcomplexes_finite
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Finite ι]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : ι → Geometry.SimplicialComplex ℝ E) (hLfin : ∀ i, (L i).faces.Finite)
    (hLK : ∀ i, (L i).space ⊆ K.space) (f : ι → E → F)
    (hf : ∀ i, IsPiecewiseAffineOn (f i) (L i).space) :
    ∃ K' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K ∧ K'.faces.Finite ∧
      ∀ i, (restrict K' (L i).space).space = (L i).space ∧
        ∀ s ∈ (restrict K' (L i).space).faces,
          ∃ A : E →ᵃ[ℝ] F, _root_.Set.EqOn (f i) A (convexHull ℝ (s : Set E)) := by
  let _ := Fintype.ofFinite ι
  obtain ⟨K', hK', hfin, hface⟩ :=
    exists_isSubdivision_affineOn_subcomplexes_finset K Finset.univ L
      (fun i _ => hLfin i) (fun i _ => hLK i) f (fun i _ => hf i)
  exact ⟨K', hK', hfin, fun i => hface i (Finset.mem_univ i)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_affineOn_subcomplexes_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_affineOn_subcomplexes_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_affineOn_subcomplexes_finite ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_affineOn_subcomplexes_finite

open _root_.Classical in
theorem PLPieceIn.exists_isSubdivision_affineOn_chart_stars
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {P : Set X} (T : PLPieceIn E n X P) :
    ∃ K₀ : Geometry.SimplicialComplex ℝ E, IsSubdivision K₀ T.complex ∧ K₀.faces.Finite ∧
      ∃ K' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K₀ ∧ K'.faces.Finite ∧
        ∀ v, {v} ∈ K₀.faces →
          ∃ e ∈ atlas (EuclideanSpace ℝ (Fin n)) X,
            closedStar K₀ v ⊆ T.map ⁻¹' e.source ∧
              (PiecewiseLinear.restrict K' (starComplex K₀ v).space).space =
                  (starComplex K₀ v).space ∧
                ∀ s ∈ (PiecewiseLinear.restrict K' (starComplex K₀ v).space).faces,
                  ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
                    EqOn (e ∘ T.map) A (convexHull ℝ (s : Set E)) := by
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  obtain ⟨K₀, hK₀, hfin₀, hcharts⟩ :=
    exists_isSubdivision_closedStar_subset (n := n) (X := X) T.complex T.continuousOn
  let _ : Finite K₀.faces := hfin₀.to_subtype
  let V := {v : E // {v} ∈ K₀.faces}
  have hVfinite : Set.Finite {v : E | {v} ∈ K₀.faces} :=
    Set.Finite.preimage Finset.singleton_injective.injOn hfin₀
  let _ : Finite V := hVfinite.to_subtype
  choose e he hstar using fun v : V => hcharts v v.property
  have hLfin : ∀ v : V, (starComplex K₀ v).faces.Finite :=
    fun v => starComplex_faces_finite K₀ v
  have hLK : ∀ v : V, (starComplex K₀ v).space ⊆ K₀.space := by
    intro v
    rw [starComplex_space K₀ v v.property]
    exact closedStar_subset_space K₀ v
  have hpiece : ∀ v : V,
      IsPiecewiseAffineOn (e v ∘ T.map) (starComplex K₀ v).space := by
    intro v
    let _ : Finite (starComplex K₀ v).faces := (hLfin v).to_subtype
    refine (T.isPiecewiseAffineOn_chart (e v) (he v)).mono_of_isPolyhedron
      (PiecewiseLinear.isPolyhedron_space (starComplex K₀ v)) ?_
    rw [starComplex_space K₀ v v.property]
    intro x hx
    exact ⟨hK₀.space_eq ▸ closedStar_subset_space K₀ v hx, hstar v hx⟩
  obtain ⟨K', hK', hfin', hlocal⟩ :=
    exists_isSubdivision_affineOn_subcomplexes_finite K₀ (fun v : V => starComplex K₀ v)
      hLfin hLK (fun v => e v ∘ T.map) hpiece
  refine ⟨K₀, hK₀, hfin₀, K', hK', hfin', ?_⟩
  intro v hv
  let w : V := ⟨v, hv⟩
  exact ⟨e w, he w, hstar w, (hlocal w).1, (hlocal w).2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_isSubdivision_affineOn_chart_stars then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_isSubdivision_affineOn_chart_stars"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_isSubdivision_affineOn_chart_stars ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_isSubdivision_affineOn_chart_stars

open _root_.Classical in
theorem PLPieceIn.exists_isSubdivision_affineOn_chart_faces
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {P : Set X} (T : PLPieceIn E n X P) :
    ∃ K' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' T.complex ∧ K'.faces.Finite ∧
      ∀ s ∈ K'.faces,
        ∃ e ∈ atlas (EuclideanSpace ℝ (Fin n)) X,
          convexHull ℝ (s : Set E) ⊆ T.map ⁻¹' e.source ∧
            ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
              EqOn (e ∘ T.map) A (convexHull ℝ (s : Set E)) := by
  obtain ⟨K₀, hK₀, _, K', hK', hfin', hstars⟩ :=
    T.exists_isSubdivision_affineOn_chart_stars
  refine ⟨K', hK'.trans hK₀, hfin', ?_⟩
  intro s hs
  obtain ⟨t, ht, hst⟩ := hK'.exists_face_subset hs
  obtain ⟨v, hv⟩ := K₀.nonempty_of_mem_faces ht
  have hvK₀ : {v} ∈ K₀.faces :=
    K₀.down_closed ht (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  obtain ⟨e, he, hstar, _, hlocal⟩ := hstars v hvK₀
  have htstar : convexHull ℝ (t : Set E) ⊆ closedStar K₀ v := by
    intro x hx
    exact _root_.Set.mem_biUnion (s := {r ∈ K₀.faces | v ∈ convexHull ℝ (r : Set E)})
      (t := fun r => convexHull ℝ (r : Set E))
      ⟨ht, subset_convexHull ℝ (t : Set E) hv⟩ hx
  have hsstar : convexHull ℝ (s : Set E) ⊆ closedStar K₀ v := hst.trans htstar
  refine ⟨e, he, hsstar.trans hstar, ?_⟩
  apply hlocal s
  refine ⟨hs, ?_⟩
  rw [starComplex_space K₀ v hvK₀]
  exact hsstar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_isSubdivision_affineOn_chart_faces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_isSubdivision_affineOn_chart_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_isSubdivision_affineOn_chart_faces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_isSubdivision_affineOn_chart_faces

open _root_.Classical in
theorem SingularTwoCell.exists_compact_piece_affine_chart_refinement
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [T2Space M] [Nonempty M] [HasGroupoid M (plGroupoid 3)] (D : SingularTwoCell M) :
    ∃ P : Set M, ∃ T : PLPiece 3 M P,
      ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin T.ambientDim)),
        IsCompact P ∧ IsSubdivision K T.piece.complex ∧ K.faces.Finite ∧
          IsCombinatorialManifoldWithBoundary 3 K ∧ D '' D.domain ⊆ interior P ∧
            ∀ s ∈ K.faces,
              ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M,
                convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin T.ambientDim))) ⊆
                    T.piece.map ⁻¹' e.source ∧
                  ∃ A : EuclideanSpace ℝ (Fin T.ambientDim) →ᵃ[ℝ]
                      EuclideanSpace ℝ (Fin 3),
                    _root_.Set.EqOn (e ∘ T.piece.map) A
                      (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin T.ambientDim)))) := by
  obtain ⟨P, T, hPcompact, hT, hDP⟩ := D.exists_compact_piece_neighborhood
  obtain ⟨K, hK, hfin, hchart⟩ := T.piece.exists_isSubdivision_affineOn_chart_faces
  let _ : Finite T.piece.complex.faces := T.piece.finite_faces.to_subtype
  let _ : Finite K.faces := hfin.to_subtype
  exact ⟨P, T, K, hPcompact, hK, hfin, hT.of_isSubdivision hK, hDP, hchart⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.exists_compact_piece_affine_chart_refinement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.exists_compact_piece_affine_chart_refinement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.exists_compact_piece_affine_chart_refinement ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SingularTwoCell.exists_compact_piece_affine_chart_refinement

def HasPLNormalDoubleCrossingAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (P : Set E) (B : Set F)
    (y : F) : Prop :=
  (y ∈ B ∧ ∃ M : Set F, HasPLBoundaryDoubleCrossingAt f P M y) ∨
    (y ∉ B ∧ HasPLDoubleCrossingAt f P y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.HasPLNormalDoubleCrossingAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.HasPLNormalDoubleCrossingAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.HasPLNormalDoubleCrossingAt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.HasPLNormalDoubleCrossingAt

theorem HasPLNormalDoubleCrossingAt.postcomp_openPartialHomeomorph
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {f : E → F} {P : Set E} {B : Set F} {y : F}
    (h : HasPLNormalDoubleCrossingAt f P B y) (e : OpenPartialHomeomorph F F)
    (he : IsPiecewiseAffineOn e e.source) (hf : _root_.Set.MapsTo f P e.source) (hy : y ∈ e.source) :
    HasPLNormalDoubleCrossingAt (e ∘ f) P (e '' (e.source ∩ B)) (e y) := by
  rcases h with ⟨hyB, M, hcross⟩ | ⟨hyB, hcross⟩
  · refine Or.inl ⟨⟨y, ⟨hy, hyB⟩, rfl⟩, e '' (e.source ∩ M), ?_⟩
    exact hcross.postcomp_openPartialHomeomorph e he hf
  · refine Or.inr ⟨?_, hcross.postcomp_openPartialHomeomorph e he hf⟩
    rintro ⟨z, ⟨hz, hzB⟩, hzy⟩
    exact hyB ((e.injOn hz hy hzy) ▸ hzB)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.HasPLNormalDoubleCrossingAt
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.HasPLNormalDoubleCrossingAt.postcomp_openPartialHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.HasPLNormalDoubleCrossingAt.postcomp_openPartialHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.HasPLNormalDoubleCrossingAt.postcomp_openPartialHomeomorph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.HasPLNormalDoubleCrossingAt.postcomp_openPartialHomeomorph

structure IsNormalSingularCell {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (D : SingularTwoCell M)
    (BdM B' : Set M) : Prop where
  locallyInjective : ∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, Set.InjOn D U
  fiber_le_two : ∀ y, (D.domain ∩ D ⁻¹' {y}).encard ≤ 2
  boundary_image_subset : Set.range D.boundary ⊆ B'
  image_inter_boundary : D '' D.domain ∩ BdM = Set.range D.boundary
  doublePointSet_triangulated :
    ∃ (P : Set M) (T : PLPiece 3 M P)
      (G : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin T.ambientDim))),
      G.faces.Finite ∧ G.faces ⊆ T.piece.complex.faces ∧
        IsCombinatorialManifoldWithBoundary 1 G ∧
          T.piece.map '' G.space = doublePointSet D D.domain ∧
            T.piece.map '' (boundaryComplex 1 G).space = doublePointSet D D.domain ∩ BdM
  crossing : ∀ y ∈ doublePointSet D D.domain,
    ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
      HasPLNormalDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source)
        (e '' (e.source ∩ BdM)) (e y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsNormalSingularCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsNormalSingularCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsNormalSingularCell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsNormalSingularCell

namespace IsNormalSingularCell

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B' : Set M}

theorem locallyInjective_restrict (h : IsNormalSingularCell D BdM B')
    {Q : Set (EuclideanSpace ℝ (Fin 2))} (hQ : Q ⊆ D.domain) :
    ∀ x ∈ Q, ∃ U ∈ 𝓝[Q] x, Set.InjOn D U := by
  intro x hx
  obtain ⟨U, hU, hinj⟩ := h.locallyInjective x (hQ hx)
  exact ⟨U, nhdsWithin_mono x hQ hU, hinj⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsNormalSingularCell.locallyInjective_restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsNormalSingularCell.locallyInjective_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsNormalSingularCell.locallyInjective_restrict ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsNormalSingularCell.locallyInjective_restrict

theorem fiber_le_two_restrict (h : IsNormalSingularCell D BdM B')
    {Q : Set (EuclideanSpace ℝ (Fin 2))} (hQ : Q ⊆ D.domain) (y : M) :
    (Q ∩ D ⁻¹' {y}).encard ≤ 2 :=
  (_root_.Set.encard_le_encard (_root_.Set.inter_subset_inter hQ Subset.rfl)).trans (h.fiber_le_two y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsNormalSingularCell.fiber_le_two_restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsNormalSingularCell.fiber_le_two_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsNormalSingularCell.fiber_le_two_restrict ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsNormalSingularCell.fiber_le_two_restrict

theorem doublePointSet_mono {Q : Set (EuclideanSpace ℝ (Fin 2))}
    (hQ : Q ⊆ D.domain) : doublePointSet D Q ⊆ doublePointSet D D.domain := by
  rintro y ⟨x, hx, z, hz, hxz, hxy, hzy⟩
  exact ⟨x, hQ hx, z, hQ hz, hxz, hxy, hzy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsNormalSingularCell.doublePointSet_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsNormalSingularCell.doublePointSet_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsNormalSingularCell.doublePointSet_mono ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsNormalSingularCell.doublePointSet_mono

theorem exists_crossing_chart (h : IsNormalSingularCell D BdM B')
    {y : M} (hy : y ∈ doublePointSet D D.domain) :
    ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
      HasPLNormalDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source)
        (e '' (e.source ∩ BdM)) (e y) :=
  h.crossing y hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsNormalSingularCell.exists_crossing_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsNormalSingularCell.exists_crossing_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsNormalSingularCell.exists_crossing_chart ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsNormalSingularCell.exists_crossing_chart

end IsNormalSingularCell

end DifferentialGeometry.Topology.PiecewiseLinear
