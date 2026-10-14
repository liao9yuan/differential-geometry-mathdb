import Submission.DifferentialGeometry.Topology.PiecewiseLinear.HeightIndex

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affineMap_eq_iff_of_mem_openSimplex_of_ge (a : E →ᵃ[ℝ] ℝ) {s : Finset E}
    {x : E} (hx : x ∈ openSimplex s) {r : ℝ} (hside : ∀ v ∈ s, r ≤ a v) :
    a x = r ↔ ∀ v ∈ s, a v = r := by
  obtain ⟨μ, hμpos, hμsum, hμx⟩ := hx
  have hsum : ∑ v ∈ s, μ v * (a v - r) = a x - r := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hμsum, one_mul]
    have ha := affineMap_apply_sum_smul a hμsum
    simp only [smul_eq_mul, hμx] at ha
    rw [ha]
  constructor
  · intro hax
    rw [hax, sub_self] at hsum
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun v hv => mul_nonneg (hμpos v hv).le (sub_nonneg.mpr (hside v hv)))).mp hsum
    intro v hv
    exact sub_eq_zero.mp ((mul_eq_zero.mp (hzero v hv)).resolve_left (hμpos v hv).ne')
  · intro hverts
    have hzero : ∑ v ∈ s, μ v * (a v - r) = 0 :=
      Finset.sum_eq_zero fun v hv => by rw [hverts v hv, sub_self, _root_.MulZeroClass.mul_zero]
    exact sub_eq_zero.mp (hsum.symm.trans hzero)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.affineMap_eq_iff_of_mem_openSimplex_of_ge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.affineMap_eq_iff_of_mem_openSimplex_of_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.affineMap_eq_iff_of_mem_openSimplex_of_ge ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.affineMap_eq_iff_of_mem_openSimplex_of_ge

theorem affineMap_eq_iff_of_mem_openSimplex_of_le (a : E →ᵃ[ℝ] ℝ) {s : Finset E}
    {x : E} (hx : x ∈ openSimplex s) {r : ℝ} (hside : ∀ v ∈ s, a v ≤ r) :
    a x = r ↔ ∀ v ∈ s, a v = r := by
  simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_inj] using
    affineMap_eq_iff_of_mem_openSimplex_of_ge (-a) hx
      (fun v hv => neg_le_neg (hside v hv))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.affineMap_eq_iff_of_mem_openSimplex_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.affineMap_eq_iff_of_mem_openSimplex_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.affineMap_eq_iff_of_mem_openSimplex_of_le ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.affineMap_eq_iff_of_mem_openSimplex_of_le

theorem eq_height_iff_of_affine_on_faces (R : Geometry.SimplicialComplex ℝ E)
    (a b : E →ᵃ[ℝ] ℝ) (r t : ℝ) {h : E → E}
    (hfaces : ∀ s ∈ R.faces, ∃ c : E →ᵃ[ℝ] E, _root_.Set.EqOn h c (convexHull ℝ (s : Set E)))
    (hside : ∀ s ∈ R.faces, convexHull ℝ (s : Set E) ⊆ {x | a x ≤ r} ∨
      convexHull ℝ (s : Set E) ⊆ {x | r ≤ a x})
    (hverts : ∀ v ∈ R.vertices, (a v ≤ r → b (h v) ≤ t) ∧
      (r ≤ a v → t ≤ b (h v)) ∧ (a v = r ↔ b (h v) = t))
    {x : E} (hx : x ∈ R.space) : a x = r ↔ b (h x) = t := by
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex R hx
  obtain ⟨c, hc⟩ := hfaces s hs
  have hvs : ∀ v ∈ s, v ∈ R.vertices := fun v hv =>
    R.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hcvert : ∀ v ∈ s, c v = h v := fun v hv => (hc (subset_convexHull ℝ _ hv)).symm
  have heq : (∀ v ∈ s, a v = r) ↔ ∀ v ∈ s, (b.comp c) v = t := by
    apply forall₂_congr
    intro v hv
    change a v = r ↔ b (c v) = t
    rw [hcvert v hv]
    exact (hverts v (hvs v hv)).2.2
  rw [hc (openSimplex_subset_convexHull s hxs)]
  change a x = r ↔ (b.comp c) x = t
  rcases hside s hs with hle | hge
  · have hleft : ∀ v ∈ s, a v ≤ r := fun v hv => hle (subset_convexHull ℝ _ hv)
    have hright : ∀ v ∈ s, (b.comp c) v ≤ t := by
      intro v hv
      change b (c v) ≤ t
      rw [hcvert v hv]
      exact (hverts v (hvs v hv)).1 (hleft v hv)
    rw [affineMap_eq_iff_of_mem_openSimplex_of_le a hxs hleft,
      affineMap_eq_iff_of_mem_openSimplex_of_le (b.comp c) hxs hright]
    exact heq
  · have hleft : ∀ v ∈ s, r ≤ a v := fun v hv => hge (subset_convexHull ℝ _ hv)
    have hright : ∀ v ∈ s, t ≤ (b.comp c) v := by
      intro v hv
      change t ≤ b (c v)
      rw [hcvert v hv]
      exact (hverts v (hvs v hv)).2.1 (hleft v hv)
    rw [affineMap_eq_iff_of_mem_openSimplex_of_ge a hxs hleft,
      affineMap_eq_iff_of_mem_openSimplex_of_ge (b.comp c) hxs hright]
    exact heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eq_height_iff_of_affine_on_faces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eq_height_iff_of_affine_on_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eq_height_iff_of_affine_on_faces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eq_height_iff_of_affine_on_faces

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem levelPolygons_image_of_image_fiber [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (h : E ≃ₜ F) (hh : IsPLHomeomorphOn h _root_.Set.univ _root_.Set.univ)
    {S : Set E} {T : Set F} {a : E → ℝ} {b : F → ℝ} {r t : ℝ}
    (hfiber : h '' (S ∩ {x | a x = r}) = T ∩ {y | b y = t}) :
    levelPolygons T b t = (fun J => h '' J) '' levelPolygons S a r := by
  ext J
  constructor
  · rintro ⟨hJ, hJT⟩
    have hJ' : IsPLSphere 1 (h.symm '' J) :=
      hJ.of_isPLHomeomorphOn (hh.homeomorph_symm.restrict hJ.isPolyhedron (_root_.Set.subset_univ J))
    refine ⟨h.symm '' J, ⟨hJ', ?_⟩, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hxy⟩ := hfiber.symm.subset (hJT hy)
      rwa [← hxy, h.symm_apply_apply]
    · change h '' (h.symm '' J) = J
      rw [_root_.Set.image_image]
      simp only [h.apply_symm_apply, _root_.Set.image_id']
  · rintro ⟨J, ⟨hJ, hJS⟩, rfl⟩
    exact ⟨hJ.of_isPLHomeomorphOn (hh.restrict hJ.isPolyhedron (_root_.Set.subset_univ J)),
      (_root_.Set.image_mono hJS).trans hfiber.subset⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.levelPolygons_image_of_image_fiber then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.levelPolygons_image_of_image_fiber"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.levelPolygons_image_of_image_fiber ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.levelPolygons_image_of_image_fiber

theorem encard_levelPolygons_eq_of_image_fiber [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (h : E ≃ₜ F) (hh : IsPLHomeomorphOn h _root_.Set.univ _root_.Set.univ)
    {S : Set E} {T : Set F} {a : E → ℝ} {b : F → ℝ} {r t : ℝ}
    (hfiber : h '' (S ∩ {x | a x = r}) = T ∩ {y | b y = t}) :
    (levelPolygons T b t).encard = (levelPolygons S a r).encard := by
  rw [levelPolygons_image_of_image_fiber h hh hfiber]
  exact (Set.image_injective.mpr h.injective).injOn.encard_image

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.encard_levelPolygons_eq_of_image_fiber then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.encard_levelPolygons_eq_of_image_fiber"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.encard_levelPolygons_eq_of_image_fiber ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.encard_levelPolygons_eq_of_image_fiber

end DifferentialGeometry.Topology.PiecewiseLinear
