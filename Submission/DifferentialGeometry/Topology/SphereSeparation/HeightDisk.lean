import Submission.DifferentialGeometry.Topology.SphereSeparation.HeightSection
import Submission.DifferentialGeometry.Topology.PlanarJordan.InnermostSmoothDisk
import Submission.DifferentialGeometry.Topology.Handle.Embedding
import Submission.DifferentialGeometry.Topology.Embedding.Graph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

private theorem exists_innermost_height_level_disk_coordinates {e : SphereTwo → EuclideanThree}
    (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {a : ℝ} (hne : ∃ x, e x 2 = a)
    (hr : ∀ x, e x 2 = a → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0) :
    ∃ (η : AddCircle (1 : ℝ) → SphereTwo) (γ : AddCircle (1 : ℝ) → Schoenflies.Plane)
      (Φ : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane),
      _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η ∧
      (∀ z, e (η z) = (EuclideanSpace.equivProdLast 2).symm (γ z, a)) ∧
      _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ ∧
      Φ '' _root_.Metric.sphere (0 : Schoenflies.Plane) 1 = _root_.Set.range γ ∧
      Φ '' _root_.Metric.ball (0 : Schoenflies.Plane) 1 = Schoenflies.inside (_root_.Set.range γ) ∧
      Φ '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1 = closure (Schoenflies.inside (_root_.Set.range γ)) ∧
      ∃ δ : ℝ, 0 < δ ∧
        (fun y : Schoenflies.Plane => (EuclideanSpace.equivProdLast 2).symm (y, a)) ⁻¹' _root_.Set.range e ∩
          cthickening δ (Φ '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1) = _root_.Set.range γ := by
  classical
  obtain ⟨hfinite, η, γ, hη, hγ, hcompat, hdisj, hcover⟩ :=
    exists_planar_height_level_circle_parametrizations he a hr
  let I := ConnectedComponents {x : SphereTwo // e x 2 = a}
  let : Finite I := hfinite
  let : Fintype I := Fintype.ofFinite I
  have hnonempty : Nonempty I := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨ConnectedComponents.mk (⟨x, hx⟩ : {x : SphereTwo // e x 2 = a})⟩
  let : Nonempty I := hnonempty
  obtain ⟨i, _, Φ, hΦ, hball, hclosed, δ, hδ, hclear⟩ :=
    PlanarJordan.exists_innermost_smooth_disk (Finset.univ : Finset I) Finset.univ_nonempty
      γ (fun i _ => hγ i) (fun i _ j _ hij => hdisj hij)
  refine ⟨η i, γ i, Φ, hη i, hcompat i, hγ i, hΦ, hball, hclosed, δ, hδ, ?_⟩
  rw [← hcover]
  ext y
  constructor
  · rintro ⟨hy, hyD⟩
    obtain ⟨j, hyj⟩ := mem_iUnion.mp hy
    by_cases hji : j = i
    · exact hji ▸ hyj
    · exact False.elim (disjoint_left.mp (hclear j (Finset.mem_univ j) hji) hyD hyj)
  · intro hy
    refine ⟨mem_iUnion.mpr ⟨i, hy⟩, _root_.Metric.self_subset_cthickening _ ?_⟩
    rw [← hΦ] at hy
    exact _root_.Set.image_mono _root_.Metric.sphere_subset_closedBall hy

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_level_disk_coordinates
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_level_disk_coordinates target :: scope.openDecls } }

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

theorem exists_innermost_height_level_disk {e : SphereTwo → EuclideanThree}
    (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {a : ℝ} (hne : ∃ x, e x 2 = a)
    (hr : ∀ x, e x 2 = a → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0) :
    ∃ (η : AddCircle (1 : ℝ) → SphereTwo) (γ : AddCircle (1 : ℝ) → Schoenflies.Plane)
      (Φ : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane) (b : ClosedCell 2 → EuclideanThree),
      _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η ∧
      (∀ z, e (η z) = (EuclideanSpace.equivProdLast 2).symm (γ z, a)) ∧
      _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ ∧
      _root_.Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 3) ∞ b ∧
      (∀ x, b x = (EuclideanSpace.equivProdLast 2).symm (Φ x.val, a)) ∧
      (∀ x, b x 2 = a) ∧
      Φ '' _root_.Metric.sphere (0 : Schoenflies.Plane) 1 = _root_.Set.range γ ∧
      Φ '' _root_.Metric.ball (0 : Schoenflies.Plane) 1 = Schoenflies.inside (_root_.Set.range γ) ∧
      Φ '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1 = closure (Schoenflies.inside (_root_.Set.range γ)) ∧
      _root_.Set.range (b ∘ cellBoundaryInclusion 2) =
        (fun y : Schoenflies.Plane => (EuclideanSpace.equivProdLast 2).symm (y, a)) '' _root_.Set.range γ ∧
      _root_.Set.range (b ∘ cellBoundaryInclusion 2) = e '' _root_.Set.range η ∧
      _root_.Set.range b ∩ _root_.Set.range e = _root_.Set.range (b ∘ cellBoundaryInclusion 2) ∧
      ∃ δ : ℝ, 0 < δ ∧ _root_.Metric.cthickening δ (_root_.Set.range b) ∩ (_root_.Set.range e ∩ {z | z 2 = a}) =
        range (b ∘ cellBoundaryInclusion 2) := by
  obtain ⟨η, γ, Φ, hη, hcompat, hγ, hΦ, hball, hclosed, δ, hδ, hclear⟩ :=
    exists_innermost_height_level_disk_coordinates he hne hr
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  let lift : Schoenflies.Plane → EuclideanThree := fun y => L.symm (y, a)
  let b : ClosedCell 2 → EuclideanThree := fun x => lift (Φ x.val)
  have hb : _root_.Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 3) ∞ b := by
    have h := ((Handle.closedCellInclusion_isSmoothEmbedding 1).diffeomorph_comp Φ).graph
      (contDiff_const : ContDiff ℝ ∞ (fun _ : Schoenflies.Plane => a))
    exact h.continuousLinearEquiv_comp L.symm
  have hlift : Isometry lift := EuclideanSpace.isometry_equivProdLast_symm_const 2 a
  have hheight (x : ClosedCell 2) : b x 2 = a :=
    EuclideanSpace.equivProdLast_symm_last 2 _
  have hbrange : _root_.Set.range b = lift '' (Φ '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1) := by
    change _root_.Set.range (lift ∘ Φ ∘ (Subtype.val : ClosedCell 2 → Schoenflies.Plane)) = _
    rw [_root_.Set.range_comp, _root_.Set.range_comp, range_closedCell]
  have hboundary : _root_.Set.range (b ∘ cellBoundaryInclusion 2) = lift '' _root_.Set.range γ := by
    have hh : b ∘ cellBoundaryInclusion 2 =
        lift ∘ Φ ∘ (Subtype.val : CellBoundary 2 → Schoenflies.Plane) := rfl
    rw [hh, _root_.Set.range_comp, _root_.Set.range_comp, range_cellBoundary, hΦ]
  have hclear' : _root_.Metric.cthickening δ (_root_.Set.range b) ∩ (_root_.Set.range e ∩ {z | z 2 = a}) =
      range (b ∘ cellBoundaryInclusion 2) := by
    rw [hbrange, hboundary]
    ext z
    constructor
    · rintro ⟨hzD, hze, hza⟩
      let y := (L z).1
      have hzy : lift y = z := by
        apply L.injective
        rw [L.apply_symm_apply]
        exact Prod.ext rfl hza.symm
      have hyD : y ∈ _root_.Metric.cthickening δ (Φ '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1) := by
        rw [← hzy, _root_.Metric.mem_cthickening_iff, Metric.infEDist_image hlift] at hzD
        exact hzD
      have hyγ : y ∈ _root_.Set.range γ := hclear.subset ⟨by change lift y ∈ _root_.Set.range e; rw [hzy]; exact hze, hyD⟩
      exact ⟨y, hyγ, hzy⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hye, hyD⟩ := hclear.symm.subset hy
      refine ⟨?_, hye, EuclideanSpace.equivProdLast_symm_last 2 _⟩
      rw [_root_.Metric.mem_cthickening_iff, Metric.infEDist_image hlift]
      exact hyD
  have hsection : _root_.Set.range b ∩ _root_.Set.range e = _root_.Set.range (b ∘ cellBoundaryInclusion 2) := by
    apply Subset.antisymm
    · rintro z ⟨hz, hze⟩
      obtain ⟨x, rfl⟩ := hz
      exact hclear'.subset ⟨self_subset_cthickening _ (_root_.Set.mem_range_self x), hze, hheight x⟩
    · rintro z ⟨x, rfl⟩
      exact ⟨mem_range_self _, (hclear'.symm.subset (_root_.Set.mem_range_self x)).2.1⟩
  have hsource : _root_.Set.range (b ∘ cellBoundaryInclusion 2) = e '' _root_.Set.range η := by
    rw [hboundary, ← _root_.Set.range_comp, ← _root_.Set.range_comp]
    congr 1
    exact (funext hcompat).symm
  exact ⟨η, γ, Φ, b, hη, hcompat, hγ, hb, fun _ => rfl, hheight, hΦ, hball, hclosed,
    hboundary, hsource, hsection, δ, hδ, hclear'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_level_disk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_level_disk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_level_disk ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_level_disk

theorem exists_innermost_height_level_disk_family {e : SphereTwo → EuclideanThree}
    (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {a : ℝ} (hne : ∃ x, e x 2 = a)
    (hr : ∀ x, e x 2 = a → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0)
    {W : Set ℝ} (hW : IsOpen W) (haW : a ∈ W) :
    ∃ ε : ℝ, 0 < ε ∧ _root_.Set.Icc (a - ε) (a + ε) ⊆ W ∧
      ∃ (η : AddCircle (1 : ℝ) → SphereTwo) (γ : AddCircle (1 : ℝ) → Schoenflies.Plane)
        (Φ : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane)
        (D : EuclideanThree ≃ₘ[ℝ] EuclideanThree) (b : ℝ → ClosedCell 2 → EuclideanThree),
        _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η ∧
        (∀ z, e (η z) = (EuclideanSpace.equivProdLast 2).symm (γ z, a)) ∧
        _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ ∧
        Φ '' _root_.Metric.sphere (0 : Schoenflies.Plane) 1 = _root_.Set.range γ ∧
        Φ '' _root_.Metric.ball (0 : Schoenflies.Plane) 1 = Schoenflies.inside (_root_.Set.range γ) ∧
        Φ '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1 = closure (Schoenflies.inside (_root_.Set.range γ)) ∧
        (∀ z, D z 2 = z 2) ∧ (∀ z, z 2 = a → D z = z) ∧
        (∀ t x, b t x = D ((EuclideanSpace.equivProdLast 2).symm (Φ x.val, t))) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 2)) (𝓡 3) ∞
          (fun p : ℝ × ClosedCell 2 => b p.1 p.2) ∧
        (∀ t, _root_.Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 3) ∞ (b t)) ∧
        (∀ t x, b t x 2 = t) ∧
        _root_.Set.range (b a ∘ cellBoundaryInclusion 2) = e '' _root_.Set.range η ∧
        (∀ t ∈ _root_.Set.Icc (a - ε) (a + ε),
          _root_.Set.range (b t) ∩ _root_.Set.range e = _root_.Set.range (b t ∘ cellBoundaryInclusion 2)) ∧
        (∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ _root_.Set.Icc (a - ε) (a + ε),
          (fun y : Schoenflies.Plane => D ((EuclideanSpace.equivProdLast 2).symm (y, t))) ⁻¹'
            _root_.Set.range e ∩ _root_.Metric.cthickening δ (Φ '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1) = _root_.Set.range γ) ∧
        ∃ K : Set EuclideanThree, IsCompact K ∧ K ⊆ {z | z 2 ∈ W} ∧ _root_.Set.EqOn D id Kᶜ := by
  obtain ⟨η, γ, Φ, hη, hcompat, hγ, hΦ, hball, hclosed, δ, hδ, hclear⟩ :=
    exists_innermost_height_level_disk_coordinates he hne hr
  obtain ⟨ε, hε, hεW, D, hD, hDa, hlevels, K, hK, hKW, hfix⟩ :=
    exists_height_preserving_regular_level_diffeomorph he hr hW haW
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  let lift : ℝ → Schoenflies.Plane → EuclideanThree := fun t y => D (L.symm (y, t))
  let b : ℝ → ClosedCell 2 → EuclideanThree := fun t x => lift t (Φ x.val)
  have hb (t : ℝ) : _root_.Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 3) ∞ (b t) := by
    have h := ((Handle.closedCellInclusion_isSmoothEmbedding 1).diffeomorph_comp Φ).graph
      (contDiff_const : ContDiff ℝ ∞ (fun _ : Schoenflies.Plane => t))
    exact (h.continuousLinearEquiv_comp L.symm).diffeomorph_comp D
  have hbjoint : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 2)) (𝓡 3) ∞
      (fun p : ℝ × ClosedCell 2 => b p.1 p.2) := by
    exact D.contMDiff.comp (L.symm.contDiff.contMDiff.comp
      ((Φ.contMDiff.comp ((Handle.closedCellInclusion_isSmoothEmbedding 1).contMDiff.comp
        contMDiff_snd)).prodMk_space contMDiff_fst))
  have hboundary (t : ℝ) : _root_.Set.range (b t ∘ cellBoundaryInclusion 2) = lift t '' _root_.Set.range γ := by
    have hh : b t ∘ cellBoundaryInclusion 2 =
        lift t ∘ Φ ∘ (Subtype.val : CellBoundary 2 → Schoenflies.Plane) := rfl
    rw [hh, _root_.Set.range_comp, _root_.Set.range_comp, range_cellBoundary, hΦ]
  have hclear' (t : ℝ) (ht : t ∈ _root_.Set.Icc (a - ε) (a + ε)) :
      lift t ⁻¹' _root_.Set.range e ∩ _root_.Metric.cthickening δ (Φ '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1) =
        range γ := by
    rw [show lift t ⁻¹' _root_.Set.range e =
      (fun y : Schoenflies.Plane => L.symm (y, a)) ⁻¹' _root_.Set.range e from
        preimage_height_section_eq D.injective hD (hlevels t ht)]
    exact hclear
  have hsource : _root_.Set.range (b a ∘ cellBoundaryInclusion 2) = e '' _root_.Set.range η := by
    rw [hboundary, ← _root_.Set.range_comp, ← _root_.Set.range_comp]
    congr 1
    funext z
    change D (L.symm (γ z, a)) = e (η z)
    rw [hDa _ (EuclideanSpace.equivProdLast_symm_last 2 _)]
    exact (hcompat z).symm
  have hsection (t : ℝ) (ht : t ∈ _root_.Set.Icc (a - ε) (a + ε)) :
      range (b t) ∩ _root_.Set.range e = _root_.Set.range (b t ∘ cellBoundaryInclusion 2) := by
    rw [hboundary]
    apply Subset.antisymm
    · rintro z ⟨⟨x, rfl⟩, hxe⟩
      exact ⟨Φ x.val, (hclear' t ht).subset ⟨hxe,
        _root_.Metric.self_subset_cthickening _ ⟨x.val, by simpa using x.property, rfl⟩⟩, rfl⟩
    · rintro z ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hΦ.symm.subset hy
      refine ⟨⟨⟨x, ?_⟩, rfl⟩, ((hclear' t ht).symm.subset hy).1⟩
      simpa using _root_.Metric.sphere_subset_closedBall hx
  refine ⟨ε, hε, hεW, η, γ, Φ, D, b, hη, hcompat, hγ, hΦ, hball, hclosed,
    hD, hDa, fun _ _ => rfl, hbjoint, hb, ?_, hsource, hsection,
    ⟨δ, hδ, hclear'⟩, K, hK, hKW, hfix⟩
  intro t x
  exact (hD _).trans (EuclideanSpace.equivProdLast_symm_last 2 _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_level_disk_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_level_disk_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_level_disk_family ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_level_disk_family

end DifferentialGeometry.Topology.SphereSeparation
