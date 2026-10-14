import Submission.DifferentialGeometry.Geometry.Neck.DisjointSphereAnnulus
import Submission.DifferentialGeometry.Geometry.Neck.SpatialLevelOverlap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p₀ p₁ : M}

omit [T2Space M] in
private theorem SpatialNeck.half_collar_disjoint_of_level_slab
    (nk₀ : SpatialNeck g eps p₀) (nk₁ : SpatialNeck g eps p₁)
    (a b ν₀ ν₁ : ℝ) (ha : |a| ≤ 3) (hb : |b| ≤ 3)
    (hν₀ : ν₀ = 1 ∨ ν₀ = -1) (hν₁ : ν₁ = 1 ∨ ν₁ = -1)
    (hdisjoint : Disjoint (_root_.Set.range (fun q : Sphere 2 => nk₀.map (q, a)))
      (_root_.Set.range (fun q : Sphere 2 => nk₁.map (q, b))))
    (havoid₀ : Disjoint
      (nk₀.map '' {z : Cylinder | 0 < ν₀ * (z.2 - a) ∧ ν₀ * (z.2 - a) < 1 / 2})
      (_root_.Set.range (fun q : Sphere 2 => nk₁.map (q, b))))
    (havoid₁ : Disjoint
      (nk₁.map '' {z : Cylinder | 0 < ν₁ * (z.2 - b) ∧ ν₁ * (z.2 - b) < 1 / 2})
      (_root_.Set.range (fun q : Sphere 2 => nk₀.map (q, a))))
    (hslab : ∀ u₀ u₁ s₀ s₁, |s₀| ≤ 1 / 8 → |s₁| ≤ 1 / 8 →
      nk₀.map (u₀, a + s₀) = nk₁.map (u₁, b + s₁) →
      nk₀.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (a - 1) (a + 1)) ⊆
        nk₁.map '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹) ∧
      ∀ q, |(nk₁.map.symm (nk₀.map (q, a))).2 - b| < 1 / 2) :
    Disjoint
      (nk₀.map '' {z : Cylinder | 0 < ν₀ * (z.2 - a) ∧ ν₀ * (z.2 - a) ≤ 1 / 8})
      (nk₁.map '' {z : Cylinder | 0 < ν₁ * (z.2 - b) ∧ ν₁ * (z.2 - b) ≤ 1 / 8}) := by
  rw [_root_.Set.disjoint_left]
  rintro x ⟨⟨q₀, c₀⟩, hc₀, rfl⟩ ⟨⟨q₁, c₁⟩, hc₁, hmeet⟩
  let t₀ := ν₀ * (c₀ - a)
  let t₁ := ν₁ * (c₁ - b)
  have ht₀ : 0 < t₀ ∧ t₀ ≤ 1 / 8 := hc₀
  have ht₁ : 0 < t₁ ∧ t₁ ≤ 1 / 8 := hc₁
  have heq₀ : a + ν₀ * t₀ = c₀ := by rcases hν₀ with rfl | rfl <;> dsimp [t₀] <;> ring
  have heq₁ : b + ν₁ * t₁ = c₁ := by rcases hν₁ with rfl | rfl <;> dsimp [t₁] <;> ring
  have habs₀ : |ν₀ * t₀| ≤ 1 / 8 := by
    rcases hν₀ with rfl | rfl <;> simpa [abs_of_pos ht₀.1] using ht₀.2
  have habs₁ : |ν₁ * t₁| ≤ 1 / 8 := by
    rcases hν₁ with rfl | rfl <;> simpa [abs_of_pos ht₁.1] using ht₁.2
  obtain ⟨hsub, hcenter⟩ := hslab q₀ q₁ (ν₀ * t₀) (ν₁ * t₁) habs₀ habs₁
    (by rw [heq₀, heq₁]; exact hmeet.symm)
  have hlen : (4 : ℝ) < eps⁻¹ :=
    (lt_inv_comm₀ (by norm_num) nk₀.eps_pos).mpr (by linarith [nk₀.eps_small])
  let γ : ℝ → M := fun t => nk₀.map (q₀, a + ν₀ * t)
  have hγsrc (t : ℝ) (ht : t ∈ _root_.Set.Icc (0 : ℝ) t₀) :
      (q₀, a + ν₀ * t) ∈ nk₀.map.source := by
    apply nk₀.domain
    refine ⟨mem_univ _, ?_, ?_⟩ <;> rcases hν₀ with rfl | rfl <;>
      nlinarith [(abs_le.mp ha).1, (abs_le.mp ha).2, ht.1, ht.2, ht₀.2]
  have hγcontrol (t : ℝ) (ht : t ∈ _root_.Set.Icc (0 : ℝ) t₀) :
      γ t ∈ nk₁.map '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹) := by
    apply hsub
    refine ⟨(q₀, a + ν₀ * t), ⟨mem_univ _, ?_, ?_⟩, rfl⟩ <;>
      rcases hν₀ with rfl | rfl <;> nlinarith [ht.1, ht.2, ht₀.2]
  have hγtarget (t : ℝ) (ht : t ∈ _root_.Set.Icc (0 : ℝ) t₀) : γ t ∈ nk₁.map.target := by
    obtain ⟨z, hz, hzγ⟩ := hγcontrol t ht
    exact hzγ ▸ nk₁.map.map_source (nk₁.domain hz)
  have hγcont : ContinuousOn γ (_root_.Set.Icc (0 : ℝ) t₀) :=
    nk₀.map.contMDiffOn_toFun.continuousOn.comp
      (continuous_const.prodMk
        (continuous_const.add (continuous_const.mul continuous_id))).continuousOn
      hγsrc
  let f : ℝ → ℝ := fun t => ν₁ * ((nk₁.map.symm (γ t)).2 - b)
  have hf : ContinuousOn f (_root_.Set.Icc (0 : ℝ) t₀) := continuousOn_const.mul
    ((continuous_snd.continuousOn.comp
      (nk₁.map.contMDiffOn_invFun.continuousOn.comp hγcont hγtarget)
      (fun _ _ => _root_.Set.mem_univ _)).sub continuousOn_const)
  have hsource₁ : (q₁, c₁) ∈ nk₁.map.source := by
    rw [← heq₁]
    apply nk₁.domain
    refine ⟨mem_univ _, ?_, ?_⟩ <;> rcases hν₁ with rfl | rfl <;>
      nlinarith [(abs_le.mp hb).1, (abs_le.mp hb).2, ht₁.1, ht₁.2]
  have hfinal : f t₀ = t₁ := by
    dsimp only [f, γ]
    rw [heq₀, ← hmeet]
    have hinv := nk₁.map.left_inv hsource₁
    change nk₁.map.symm (nk₁.map (q₁, c₁)) = (q₁, c₁) at hinv
    rw [hinv]
  have hzero : 0 < f 0 := by
    by_contra hn
    have hf0 : f 0 ≤ 0 := le_of_not_gt hn
    obtain ⟨t, ht, hft⟩ := isPreconnected_Icc.intermediate_value
      (show (0 : ℝ) ∈ _root_.Set.Icc 0 t₀ from ⟨le_rfl, ht₀.1.le⟩)
      (show t₀ ∈ _root_.Set.Icc (0 : ℝ) t₀ from ⟨ht₀.1.le, le_rfl⟩)
      hf ⟨hf0, hfinal.symm ▸ ht₁.1.le⟩
    have hheight : (nk₁.map.symm (γ t)).2 = b := by
      change ν₁ * ((nk₁.map.symm (γ t)).2 - b) = 0 at hft
      rcases hν₁ with rfl | rfl <;> nlinarith
    have hsphere : γ t ∈ _root_.Set.range (fun q : Sphere 2 => nk₁.map (q, b)) := by
      refine ⟨(nk₁.map.symm (γ t)).1, ?_⟩
      change nk₁.map ((nk₁.map.symm (γ t)).1, b) = γ t
      rw [← hheight]
      exact nk₁.map.right_inv (hγtarget t ht)
    by_cases ht0 : t = 0
    · have hbase : γ t = nk₀.map (q₀, a) := by simp [γ, ht0]
      exact disjoint_left.mp hdisjoint ⟨q₀, hbase.symm⟩ hsphere
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      apply disjoint_left.mp havoid₀ ?_ hsphere
      refine ⟨(q₀, a + ν₀ * t), ?_, rfl⟩
      change 0 < ν₀ * (a + ν₀ * t - a) ∧ ν₀ * (a + ν₀ * t - a) < 1 / 2
      rcases hν₀ with rfl | rfl <;> constructor <;> nlinarith [ht.2, ht₀.2]
  have hsmall : |f 0| < 1 / 2 := by
    have h := hcenter q₀
    rcases hν₁ with rfl | rfl
    · simpa [f, γ] using h
    · simpa [f, γ, abs_sub_comm] using h
  apply disjoint_left.mp havoid₁ ?_ ⟨q₀, rfl⟩
  refine ⟨nk₁.map.symm (γ 0), ⟨hzero, (abs_lt.mp hsmall).2⟩, ?_⟩
  exact (nk₁.map.right_inv (hγtarget 0 ⟨le_rfl, ht₀.1.le⟩)).trans (by simp [γ])

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.half_collar_disjoint_of_level_slab
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.half_collar_disjoint_of_level_slab target :: scope.openDecls } }


universe u

theorem exists_spatial_neck_disjoint_half_collars_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p₀ p₁ : M)
          (nk₀ : SpatialNeck g eps p₀) (nk₁ : SpatialNeck g eps p₁)
          (a b ν₀ ν₁ A : ℝ), |a| ≤ 3 → |b| ≤ 3 →
          (ν₀ = 1 ∨ ν₀ = -1) → (ν₁ = 1 ∨ ν₁ = -1) →
          A < (1 - 4323 * eps) * metricScalarAt g p₀ →
          A < (1 - 4323 * eps) * metricScalarAt g p₁ →
          Disjoint (_root_.Set.range (fun q : Sphere 2 => nk₀.map (q, a)))
            (_root_.Set.range (fun q : Sphere 2 => nk₁.map (q, b))) →
          ∀ V : Set M, IsPreconnected V →
            (V ∩ {x | metricScalarAt g x ≤ A}).Nonempty →
            Disjoint V (_root_.Set.range (fun q : Sphere 2 => nk₀.map (q, a)) ∪
              _root_.Set.range (fun q : Sphere 2 => nk₁.map (q, b))) →
            (∀ r : ℝ, 0 < r → ∃ q : Sphere 2, ∃ t ∈ _root_.Set.Ioo (0 : ℝ) r,
              nk₀.map (q, a + ν₀ * t) ∈ V) →
            (∀ r : ℝ, 0 < r → ∃ q : Sphere 2, ∃ t ∈ _root_.Set.Ioo (0 : ℝ) r,
              nk₁.map (q, b + ν₁ * t) ∈ V) →
            Disjoint
              (nk₀.map '' {z : Cylinder | 0 ≤ ν₀ * (z.2 - a) ∧ ν₀ * (z.2 - a) ≤ 1 / 8})
              (nk₁.map '' {z : Cylinder | 0 ≤ ν₁ * (z.2 - b) ∧ ν₁ * (z.2 - b) ≤ 1 / 8}) := by
  obtain ⟨eta₀, heta₀, havoid⟩ := exists_spatial_neck_half_collar_avoids_sphere_tolerance.{u}
  obtain ⟨eta₁, heta₁, hslab⟩ := exists_spatial_neck_level_slab_tolerance.{u}
  refine ⟨min eta₀ eta₁, lt_min heta₀ heta₁, ?_⟩
  intro eps heps M _ _ _ _ g p₀ p₁ nk₀ nk₁ a b ν₀ ν₁ A
    ha hb hν₀ hν₁ hA₀ hA₁ hdisjoint V hV hlow hVavoid hgerm₀ hgerm₁
  have hav₀ := havoid eps (heps.trans (min_le_left _ _)) M g p₀ p₁ nk₀ nk₁
    a b ν₀ A ha hb hν₀ hA₀ hdisjoint V hV hlow hVavoid hgerm₀
  have hav₁ := havoid eps (heps.trans (min_le_left _ _)) M g p₁ p₀ nk₁ nk₀
    b a ν₁ A hb ha hν₁ hA₁ hdisjoint.symm V hV hlow
    (_root_.Set.union_comm _ _ ▸ hVavoid) hgerm₁
  have hsmall := nk₀.half_collar_disjoint_of_level_slab nk₁ a b ν₀ ν₁ ha hb hν₀ hν₁
    hdisjoint hav₀ hav₁
    (hslab eps (heps.trans (min_le_right _ _)) M g p₀ p₁ nk₀ nk₁ · · a b · · ha hb)
  rw [_root_.Set.disjoint_left]
  rintro x ⟨z₀, hz₀, rfl⟩ ⟨z₁, hz₁, hmeet⟩
  by_cases h₀ : ν₀ * (z₀.2 - a) = 0
  · have hz₀a : z₀.2 = a := by rcases hν₀ with rfl | rfl <;> nlinarith
    have hx₀ : nk₀.map z₀ ∈ _root_.Set.range (fun q : Sphere 2 => nk₀.map (q, a)) :=
      ⟨z₀.1, by rw [← hz₀a]⟩
    by_cases h₁ : ν₁ * (z₁.2 - b) = 0
    · have hz₁b : z₁.2 = b := by rcases hν₁ with rfl | rfl <;> nlinarith
      apply disjoint_left.mp hdisjoint hx₀
      exact ⟨z₁.1, by rw [← hz₁b]; exact hmeet⟩
    · apply disjoint_left.mp hav₁ ?_ hx₀
      exact ⟨z₁, ⟨lt_of_le_of_ne hz₁.1 (Ne.symm h₁), by linarith [hz₁.2]⟩, hmeet⟩
  · by_cases h₁ : ν₁ * (z₁.2 - b) = 0
    · have hz₁b : z₁.2 = b := by rcases hν₁ with rfl | rfl <;> nlinarith
      apply disjoint_left.mp hav₀
        ⟨z₀, ⟨lt_of_le_of_ne hz₀.1 (Ne.symm h₀), by linarith [hz₀.2]⟩, rfl⟩
      exact ⟨z₁.1, by rw [← hz₁b]; exact hmeet⟩
    · exact disjoint_left.mp hsmall
        ⟨z₀, ⟨lt_of_le_of_ne hz₀.1 (Ne.symm h₀), hz₀.2⟩, rfl⟩
        ⟨z₁, ⟨lt_of_le_of_ne hz₁.1 (Ne.symm h₁), hz₁.2⟩, hmeet⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_disjoint_half_collars_tolerance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_disjoint_half_collars_tolerance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_disjoint_half_collars_tolerance ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatial_neck_disjoint_half_collars_tolerance

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
