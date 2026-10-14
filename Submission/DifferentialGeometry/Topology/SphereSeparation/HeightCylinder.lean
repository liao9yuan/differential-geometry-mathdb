import Submission.DifferentialGeometry.Topology.SphereSeparation.HeightDisk
import Submission.DifferentialGeometry.Topology.SphereSeparation.CylinderSides
import Submission.DifferentialGeometry.Analysis.Calculus.Interpolation.RadialContraction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

theorem exists_innermost_height_cylinder_chart {e : SphereTwo → EuclideanThree}
    (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {a : ℝ} (hne : ∃ x, e x 2 = a)
    (hr : ∀ x, e x 2 = a → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0)
    {W : Set ℝ} (hW : IsOpen W) (haW : a ∈ W) :
    ∃ ε : ℝ, 0 < ε ∧ _root_.Set.Icc (a - ε) (a + ε) ⊆ W ∧
      ∃ R : ℝ, 1 < R ∧ ∃ (η : AddCircle (1 : ℝ) → SphereTwo)
        (Ψ : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] EuclideanThree),
        _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η ∧
        (∀ p, Ψ p 2 = a + p.2) ∧
        Ψ '' (_root_.Metric.sphere (0 : Schoenflies.Plane) 1 ×ˢ {0}) = e '' _root_.Set.range η ∧
        Ψ ⁻¹' _root_.Set.range e ∩ (_root_.Metric.closedBall (0 : Schoenflies.Plane) R ×ˢ _root_.Set.Icc (-ε) ε) =
          sphere (0 : Schoenflies.Plane) 1 ×ˢ _root_.Set.Icc (-ε) ε := by
  obtain ⟨ε, hε, hεW, η, γ, Φ, D, b, hη, hcompat, hγ, hΦ, hball, hclosed,
    hD, hDa, hb, hbsmooth, hbemb, hbheight, hsource, hsection,
    ⟨δ, hδ, hclear⟩, K, hK, hKW, hfix⟩ :=
      exists_innermost_height_level_disk_family he hne hr hW haW
  have hopen : IsOpen (Φ ⁻¹' _root_.Metric.thickening δ (Φ '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1)) :=
    isOpen_thickening.preimage Φ.continuous
  have hsub : _root_.Metric.closedBall (0 : Schoenflies.Plane) 1 ⊆
      Φ ⁻¹' _root_.Metric.thickening δ (Φ '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1) := by
    intro x hx
    change Φ x ∈ _root_.Metric.thickening δ (Φ '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1)
    exact _root_.Metric.self_subset_thickening hδ (Φ '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1)
      (_root_.Set.mem_image_of_mem Φ hx)
  obtain ⟨R, hR, hRU⟩ := DifferentialGeometry.Analysis.exists_larger_closedBall_subset_open
    (by norm_num : (0 : ℝ) ≤ 1) hopen hsub
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  let T : ℝ ≃ₘ[ℝ] ℝ :=
    { toEquiv := Equiv.addRight a
      contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
      contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff }
  let P := Φ.prodCongr T
  let P' : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] (Schoenflies.Plane × ℝ) :=
    { toEquiv := P.toEquiv
      contMDiff_toFun := by
        rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
        exact P.contMDiff
      contMDiff_invFun := by
        rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
        exact P.symm.contMDiff }
  let Ψ := P'.trans (L.symm.toDiffeomorph.trans D)
  have hΨ (x : Schoenflies.Plane) (t : ℝ) : Ψ (x, t) = D (L.symm (Φ x, a + t)) := by
    change D (L.symm (Φ x, t + a)) = _
    rw [add_comm t a]
  have hclear' (x : Schoenflies.Plane) (hx : x ∈ _root_.Metric.closedBall 0 R)
      (t : ℝ) (ht : t ∈ _root_.Set.Icc (-ε) ε) : Ψ (x, t) ∈ _root_.Set.range e ↔ x ∈ _root_.Metric.sphere 0 1 := by
    have ht' : a + t ∈ _root_.Set.Icc (a - ε) (a + ε) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hxD : Φ x ∈ _root_.Metric.cthickening δ (Φ '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1) :=
      _root_.Metric.thickening_subset_cthickening _ _ (hRU hx)
    have hmem : Ψ (x, t) ∈ _root_.Set.range e ↔ Φ x ∈ _root_.Set.range γ := by
      rw [hΨ]
      exact ⟨fun h => (hclear (a + t) ht').subset ⟨h, hxD⟩,
        fun h => ((hclear (a + t) ht').symm.subset h).1⟩
    rw [hmem, ← hΦ]
    exact Φ.injective.mem_set_image
  refine ⟨ε, hε, hεW, R, hR, η, Ψ, hη, ?_, ?_, ?_⟩
  · rintro ⟨x, t⟩
    rw [hΨ, hD]
    exact EuclideanSpace.equivProdLast_symm_last 2 _
  · rw [← hsource]
    ext z
    constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      obtain rfl : t = 0 := ht
      refine ⟨⟨x, by simpa using hx⟩, ?_⟩
      rw [Function.comp_apply, hb, hΨ, add_zero]
      rfl
    · rintro ⟨x, rfl⟩
      refine ⟨(x.val, 0), ⟨by simpa using x.property, rfl⟩, ?_⟩
      rw [hΨ, Function.comp_apply, hb, add_zero]
      rfl
  · ext p
    rcases p with ⟨x, t⟩
    constructor
    · rintro ⟨hxe, hx, ht⟩
      exact ⟨(hclear' x hx t ht).mp hxe, ht⟩
    · rintro ⟨hx, ht⟩
      have hxR : x ∈ _root_.Metric.closedBall 0 R := _root_.Metric.closedBall_subset_closedBall hR.le (_root_.Metric.sphere_subset_closedBall hx)
      exact ⟨(hclear' x hxR t ht).mpr hx, hxR, ht⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_cylinder_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_cylinder_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_cylinder_chart ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_cylinder_chart

theorem exists_innermost_height_cylinder_chart_with_radial_sides {e : SphereTwo → EuclideanThree}
    (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) (d : SphereSides (_root_.Set.range e))
    {a : ℝ} (hne : ∃ x, e x 2 = a)
    (hr : ∀ x, e x 2 = a → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0)
    {W : Set ℝ} (hW : IsOpen W) (haW : a ∈ W) :
    ∃ ε : ℝ, 0 < ε ∧ _root_.Set.Icc (a - ε) (a + ε) ⊆ W ∧
      ∃ R : ℝ, 1 < R ∧ ∃ (η : AddCircle (1 : ℝ) → SphereTwo)
        (Ψ : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] EuclideanThree),
        _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η ∧
        (∀ p, Ψ p 2 = a + p.2) ∧
        Ψ '' (_root_.Metric.sphere (0 : Schoenflies.Plane) 1 ×ˢ {0}) = e '' _root_.Set.range η ∧
        Ψ ⁻¹' _root_.Set.range e ∩ (_root_.Metric.closedBall (0 : Schoenflies.Plane) R ×ˢ _root_.Set.Icc (-ε) ε) =
          _root_.Metric.sphere (0 : Schoenflies.Plane) 1 ×ˢ _root_.Set.Icc (-ε) ε ∧
        (((∀ p ∈ _root_.Metric.ball (0 : Schoenflies.Plane) R ×ˢ _root_.Set.Ioo (-ε) ε,
            Ψ p ∈ d.compactSide ↔ ‖p.1‖ < 1) ∧
          (∀ p ∈ _root_.Metric.ball (0 : Schoenflies.Plane) R ×ˢ _root_.Set.Ioo (-ε) ε,
            Ψ p ∈ d.endSide ↔ 1 < ‖p.1‖) ∧
          (∀ p ∈ _root_.Metric.ball (0 : Schoenflies.Plane) R ×ˢ _root_.Set.Ioo (-ε) ε,
            Ψ p ∈ closure d.compactSide ↔ ‖p.1‖ ≤ 1)) ∨
        ((∀ p ∈ _root_.Metric.ball (0 : Schoenflies.Plane) R ×ˢ _root_.Set.Ioo (-ε) ε,
            Ψ p ∈ d.endSide ↔ ‖p.1‖ < 1) ∧
          (∀ p ∈ _root_.Metric.ball (0 : Schoenflies.Plane) R ×ˢ _root_.Set.Ioo (-ε) ε,
            Ψ p ∈ d.compactSide ↔ 1 < ‖p.1‖) ∧
          (∀ p ∈ _root_.Metric.ball (0 : Schoenflies.Plane) R ×ˢ _root_.Set.Ioo (-ε) ε,
            Ψ p ∈ closure d.compactSide ↔ 1 ≤ ‖p.1‖))) := by
  obtain ⟨ε, hε, hεW, R, hR, η, Ψ, hη, hheight, hboundary, hsphere⟩ :=
    exists_innermost_height_cylinder_chart he hne hr hW haW
  refine ⟨ε, hε, hεW, R, hR, η, Ψ, hη, hheight, hboundary, hsphere, ?_⟩
  apply d.radial_sides_of_cylinder_chart Ψ.toHomeomorph (by
    rw [← Module.finrank_eq_rank']
    norm_num [Schoenflies.Plane, Module.finrank_fin_fun]) hε zero_lt_one hR
  intro x hx t ht
  have hxR : x ∈ _root_.Metric.closedBall (0 : Schoenflies.Plane) R := _root_.Metric.ball_subset_closedBall hx
  have htε : t ∈ _root_.Set.Icc (-ε) ε := _root_.Set.Ioo_subset_Icc_self ht
  constructor
  · intro hxS
    have hp : (x, t) ∈ _root_.Metric.sphere (0 : Schoenflies.Plane) 1 ×ˢ _root_.Set.Icc (-ε) ε :=
      hsphere.subset ⟨hxS, hxR, htε⟩
    exact mem_sphere_zero_iff_norm.mp hp.1
  · intro hxn
    have hp : (x, t) ∈ Ψ ⁻¹' _root_.Set.range e ∩
        (_root_.Metric.closedBall (0 : Schoenflies.Plane) R ×ˢ _root_.Set.Icc (-ε) ε) :=
      hsphere.symm.subset ⟨mem_sphere_zero_iff_norm.mpr hxn, htε⟩
    exact hp.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_cylinder_chart_with_radial_sides then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_cylinder_chart_with_radial_sides"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_cylinder_chart_with_radial_sides ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_innermost_height_cylinder_chart_with_radial_sides

end DifferentialGeometry.Topology.SphereSeparation
