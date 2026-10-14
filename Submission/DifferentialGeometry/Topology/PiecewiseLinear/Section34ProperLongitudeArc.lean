import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CutCircleArc

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsCylindricalDiagram.preimage_circle_inter_ends_eq_pair
    {f : E × ℝ → F} {P : Set E} {S J : Set F} (hf : IsCylindricalDiagram f P S)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) {a : E} (ha : a ∈ P)
    (hinter : J ∩ f '' (P ×ˢ ({0} : Set ℝ)) = {f (a, 0)}) :
    (P ×ˢ ({0, 1} : Set ℝ)) ∩ f ⁻¹' J = {(a, 0), (a, 1)} := by
  have hp : f (a, 0) ∈ J := (hinter.symm.subset (_root_.Set.mem_singleton _)).1
  ext x
  constructor
  · rintro ⟨⟨hxP, ht | ht⟩, hxJ⟩
    · have hxp : f x = f (a, 0) := hinter.subset ⟨hxJ, x, ⟨hxP, ht⟩, rfl⟩
      have hxI : x ∈ P ×ˢ _root_.Set.Icc (0 : ℝ) 1 :=
        ⟨hxP, by rw [ht]; exact ⟨le_rfl, zero_le_one⟩⟩
      have hb := ((hf.eq_iff_fst_eq_and_circle_eq hends hxI
        ⟨ha, le_rfl, zero_le_one⟩).mp hxp).1
      exact Or.inl (Prod.ext hb ht)
    · have hfzero : f (x.1, 0) = f x :=
        (hends x.1 hxP).trans (congrArg f (Prod.ext rfl ht.symm))
      have hxp : f x = f (a, 0) := hinter.subset
        ⟨hxJ, (x.1, 0), ⟨hxP, rfl⟩, hfzero⟩
      have hxI : x ∈ P ×ˢ _root_.Set.Icc (0 : ℝ) 1 :=
        ⟨hxP, by rw [ht]; exact ⟨zero_le_one, le_rfl⟩⟩
      have hb := ((hf.eq_iff_fst_eq_and_circle_eq hends hxI
        ⟨ha, le_rfl, zero_le_one⟩).mp hxp).1
      exact Or.inr (Prod.ext hb ht)
  · rintro (rfl | rfl)
    · exact ⟨⟨ha, Or.inl rfl⟩, hp⟩
    · exact ⟨⟨ha, Or.inr rfl⟩, by change f (a, 1) ∈ J; rw [← hends a ha]; exact hp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.preimage_circle_inter_ends_eq_pair then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.preimage_circle_inter_ends_eq_pair"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.preimage_circle_inter_ends_eq_pair ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.preimage_circle_inter_ends_eq_pair

theorem IsCylindricalDiagram.image_open_preimage_circle_eq_sdiff
    {f : E × ℝ → F} {P : Set E} {S J : Set F} (hf : IsCylindricalDiagram f P S)
    (hJS : J ⊆ S) {p : F}
    (hinter : J ∩ f '' (P ×ˢ ({0} : Set ℝ)) = {p}) :
    f '' ((P ×ˢ _root_.Set.Ioo (0 : ℝ) 1) ∩ f ⁻¹' J) = J \ {p} := by
  have hp := hinter.symm.subset (_root_.Set.mem_singleton p)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨hx.2, ?_⟩
    intro hxp
    obtain ⟨z, hz, hzp⟩ := hp.2
    have hzI : z ∈ P ×ˢ _root_.Set.Icc (0 : ℝ) 1 :=
      ⟨hz.1, by rw [hz.2]; exact ⟨le_rfl, zero_le_one⟩⟩
    rcases hf.eq_or_endpoints x ⟨hx.1.1, hx.1.2.1.le, hx.1.2.2.le⟩ z hzI
        (hxp.trans hzp.symm) with h | h | h
    · exact hx.1.2.1.ne' ((congrArg Prod.snd h).trans hz.2)
    · exact hx.1.2.1.ne' h.1
    · exact hx.1.2.2.ne h.1
  · rintro ⟨hy, hyp⟩
    obtain ⟨x, hx, rfl⟩ := hf.image_eq.symm.subset (hJS hy)
    have hzero : x.2 ≠ 0 := fun ht =>
      hyp (hinter.subset ⟨hy, x, ⟨hx.1, ht⟩, rfl⟩)
    have hone : x.2 ≠ 1 := fun ht => hyp (hinter.subset
      ⟨hy, hf.image_top_eq_bottom.subset ⟨x, ⟨hx.1, ht⟩, rfl⟩⟩)
    exact ⟨x, ⟨⟨hx.1, lt_of_le_of_ne hx.2.1 hzero.symm,
      lt_of_le_of_ne hx.2.2 hone⟩, hy⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.image_open_preimage_circle_eq_sdiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.image_open_preimage_circle_eq_sdiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.image_open_preimage_circle_eq_sdiff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.image_open_preimage_circle_eq_sdiff

theorem IsCylindricalDiagram.exists_proper_cut_arc_of_singleton_seam
    {E : Type} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {f : E × ℝ → F} {P : Set E} {S J : Set F} {n : ℕ}
    (hf : IsCylindricalDiagram f P S) (hP : IsPLBall n P)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) (hJ : IsPLSphere 1 J) (hJS : J ⊆ S)
    {p : F} (hinter : J ∩ f '' (P ×ˢ ({0} : Set ℝ)) = {p})
    (hnon : ¬ (⟨inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)).Nullhomotopic) :
    ∃ (a : E) (γ : ℝ → E × ℝ), a ∈ P ∧ f (a, 0) = p ∧
      IsPLHomeomorphOn γ (_root_.Set.Icc 0 1) ((P ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ f ⁻¹' J) ∧
      γ 0 = (a, 0) ∧ γ 1 = (a, 1) ∧
      γ '' _root_.Set.Ioo 0 1 = (P ×ˢ _root_.Set.Ioo (0 : ℝ) 1) ∩ f ⁻¹' J ∧
      (γ '' _root_.Set.Icc 0 1) ∩ (P ×ˢ ({0, 1} : Set ℝ)) = {(a, 0), (a, 1)} ∧
      (f ∘ γ) '' _root_.Set.Ioo 0 1 = J \ {p} := by
  obtain ⟨a, γ, ha, hap, hγ, hγ0, hγ1⟩ :=
    hf.exists_isPLHomeomorphOn_Icc_preimage_circle_of_singleton_seam
      hP hends hJ hJS hinter hnon
  have hend := hf.preimage_circle_inter_ends_eq_pair hends ha (hap.symm ▸ hinter)
  have hopen : γ '' _root_.Set.Ioo 0 1 = (P ×ˢ _root_.Set.Ioo (0 : ℝ) 1) ∩ f ⁻¹' J := by
    rw [hγ.image_Ioo_eq_sdiff_endpoints zero_lt_one, hγ0, hγ1, ← hend]
    ext x
    simp only [_root_.Set.mem_sdiff, _root_.Set.mem_inter_iff, _root_.Set.mem_prod, _root_.Set.mem_Icc, _root_.Set.mem_Ioo,
      _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_preimage]
    constructor
    · rintro ⟨⟨⟨hxP, hx0, hx1⟩, hxJ⟩, hnot⟩
      exact ⟨⟨hxP, lt_of_le_of_ne hx0 (fun h => hnot ⟨⟨hxP, Or.inl h.symm⟩, hxJ⟩),
        lt_of_le_of_ne hx1 (fun h => hnot ⟨⟨hxP, Or.inr h⟩, hxJ⟩)⟩, hxJ⟩
    · rintro ⟨⟨hxP, hx0, hx1⟩, hxJ⟩
      exact ⟨⟨⟨hxP, hx0.le, hx1.le⟩, hxJ⟩,
        fun h => h.1.2.elim hx0.ne' hx1.ne⟩
  refine ⟨a, γ, ha, hap, hγ, hγ0, hγ1, hopen, ?_, ?_⟩
  · rw [hγ.image_eq, ← hend]
    ext x
    simp only [_root_.Set.mem_inter_iff, _root_.Set.mem_prod, _root_.Set.mem_Icc, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff]
    constructor
    · exact fun h => ⟨h.2, h.1.2⟩
    · rintro ⟨⟨hxP, hx | hx⟩, hxJ⟩
      · exact ⟨⟨⟨hxP, by rw [hx]; exact ⟨le_rfl, zero_le_one⟩⟩, hxJ⟩,
          hxP, Or.inl hx⟩
      · exact ⟨⟨⟨hxP, by rw [hx]; exact ⟨zero_le_one, le_rfl⟩⟩, hxJ⟩,
          hxP, Or.inr hx⟩
  · rw [_root_.Set.image_comp, hopen]
    exact hf.image_open_preimage_circle_eq_sdiff hJS hinter

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_proper_cut_arc_of_singleton_seam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_proper_cut_arc_of_singleton_seam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_proper_cut_arc_of_singleton_seam ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_proper_cut_arc_of_singleton_seam

end DifferentialGeometry.Topology.PiecewiseLinear
