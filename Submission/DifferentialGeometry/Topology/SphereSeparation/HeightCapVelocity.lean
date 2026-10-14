import Submission.DifferentialGeometry.Topology.SphereSeparation.HeightCapTransport
import Submission.DifferentialGeometry.Topology.Diffeomorph.QuadraticFiberFlow

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Filter _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.Topology.Morse
open _root_.Submission.DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Topology.SphereSeparation

private theorem quadraticLevelScaling_mem_ball_of_close
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c α r : ℝ} (hα : α = 1 ∨ α = -1) (hr : 0 < r)
    {x : E} (hx : ‖x‖ = r) {t : ℝ}
    (ht : t ∈ _root_.Set.Ioo (c + α / 2 * r ^ 2 - r ^ 2 / 4)
      (c + α / 2 * r ^ 2 + r ^ 2 / 4)) :
    0 < (t - c) / (c + α / 2 * r ^ 2 - c) ∧
      quadraticLevelScaling (c + α / 2 * r ^ 2) c x t ∈ _root_.Metric.ball 0 (2 * r) := by
  have huc : c + α / 2 * r ^ 2 ≠ c := by
    rcases hα with rfl | rfl <;> nlinarith [sq_pos_of_pos hr]
  have hpos : 0 < (t - c) / (c + α / 2 * r ^ 2 - c) := by
    rcases hα with rfl | rfl
    · exact div_pos (by nlinarith [ht.1, sq_pos_of_pos hr]) (by nlinarith [sq_pos_of_pos hr])
    · exact div_pos_of_neg_of_neg (by nlinarith [ht.2, sq_pos_of_pos hr])
        (by nlinarith [sq_pos_of_pos hr])
  refine ⟨hpos, ?_⟩
  have hn := quadraticLevelScaling_height huc
    (show c + α / 2 * ‖x‖ ^ 2 = c + α / 2 * r ^ 2 by rw [hx]) hpos.le
  rw [_root_.Metric.mem_ball, dist_zero_right]
  apply (sq_lt_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * r)).mp
  rcases hα with rfl | rfl <;> nlinarith [ht.1, ht.2, sq_pos_of_pos hr]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.quadraticLevelScaling_mem_ball_of_close
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.quadraticLevelScaling_mem_ball_of_close target :: scope.openDecls } }

private theorem hasDerivAt_of_radial_level_transport
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : E → M) (e : M → E × ℝ) (Φ : ℝ → Equiv M M)
    (A : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (hA : ∀ z, (A z).2 = z.2)
    {c α a r ε : ℝ} (hα : α = 1 ∨ α = -1) (hr : 0 < r)
    (hnormal : ∀ y ∈ _root_.Metric.ball (0 : E) (2 * r), e (χ y) = A (y, c + α / 2 * ‖y‖ ^ 2))
    (hlevel : χ '' _root_.Metric.sphere 0 r = {z | (e z).2 = c + α / 2 * r ^ 2})
    (hΦu : Φ (c + α / 2 * r ^ 2) '' {z | (e z).2 = a} =
      {z | (e z).2 = c + α / 2 * r ^ 2})
    (hradial : ∀ x ∈ _root_.Metric.sphere (0 : E) r, ∀ s t : ℝ, s - t ∈ _root_.Set.Ioo (-ε) ε →
      Φ t ((Φ s).symm (χ x)) = χ (quadraticRadialCurve (-α⁻¹) x (s - t)))
    {t : ℝ}
    (ht : t ∈ _root_.Set.Ioo (c + α / 2 * r ^ 2 - _root_.Min.min ε (r ^ 2 / 4))
      (c + α / 2 * r ^ 2 + _root_.Min.min ε (r ^ 2 / 4)))
    {z : M} (hz : (e z).2 = a) :
    HasDerivAt (fun s => (e (Φ s z)).1)
      (A.quadraticFiberVectorField c (t, (e (Φ t z)).1)) t := by
  let u := c + α / 2 * r ^ 2
  have huc : u ≠ c := by rcases hα with rfl | rfl <;> dsimp [u] <;> nlinarith [sq_pos_of_pos hr]
  obtain ⟨x, hx, hχx⟩ := hlevel.symm.subset (hΦu.subset ⟨z, hz, rfl⟩)
  have hxn : ‖x‖ = r := mem_sphere_zero_iff_norm.mp hx
  have hxt : c + α / 2 * ‖x‖ ^ 2 = u := by rw [hxn]
  have htime : t ∈ _root_.Set.Ioo (u - r ^ 2 / 4) (u + r ^ 2 / 4) := by
    dsimp [u]
    constructor <;> linarith [ht.1, ht.2, min_le_right ε (r ^ 2 / 4)]
  obtain ⟨hpos, hsource⟩ := quadraticLevelScaling_mem_ball_of_close hα hr hxn htime
  apply Diffeomorph.hasDerivAt_fst_comp_of_quadratic_transport χ _root_.Metric.isOpen_ball e A hA huc hnormal hxt
    isOpen_Ioo (S := _root_.Set.Ioo (u - ε) (u + ε)) ?_ ?_ hpos hsource
  · intro s hs
    have hs' : u - s ∈ _root_.Set.Ioo (-ε) ε := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have heq : (Φ u).symm (χ x) = z := by rw [hχx]; exact (Φ u).symm_apply_apply z
    simpa only [heq] using hradial x hx u s hs'
  · dsimp [u]
    constructor <;> linarith [ht.1, ht.2, min_le_left ε (r ^ 2 / 4)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.hasDerivAt_of_radial_level_transport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.hasDerivAt_of_radial_level_transport target :: scope.openDecls } }

theorem exists_height_transport_with_quadratic_cap_velocity
    {e : SphereTwo → EuclideanThree} (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {p q : SphereTwo}
    (hp : IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) p)
    (hq : IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) q)
    (hmin : ∀ x, x ≠ p → e p 2 < e x 2)
    (hmax : ∀ x, x ≠ q → e x 2 < e q 2) (hpq : p ≠ q)
    (hcrit : ∀ x, IsCriticalPointAt (𝓡 2) (fun y => e y 2) x → x = p ∨ x = q) :
    ∃ r : ℝ, 0 < r ∧ e p 2 + r ^ 2 / 2 < e q 2 - r ^ 2 / 2 ∧
      ∃ A₀ A₁ : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ),
        (∀ z, (A₀ z).2 = z.2) ∧ (∀ z, (A₁ z).2 = z.2) ∧
        (EuclideanSpace.equivProdLast 2 ∘ e) '' {x | e x 2 ≤ e p 2 + r ^ 2 / 2} =
          (fun y => A₀ (y, e p 2 + 1 / 2 * ‖y‖ ^ 2)) '' _root_.Metric.closedBall 0 r ∧
        (EuclideanSpace.equivProdLast 2 ∘ e) '' {x | e q 2 - r ^ 2 / 2 ≤ e x 2} =
          (fun y => A₁ (y, e q 2 + (-1) / 2 * ‖y‖ ^ 2)) '' _root_.Metric.closedBall 0 r ∧
        ∃ Φ : ℝ → SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo,
          ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun z : ℝ × SphereTwo => Φ z.1 z.2) ∧
          ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun z : ℝ × SphereTwo => (Φ z.1).symm z.2) ∧
          Φ (e p 2 + r ^ 2 / 2) = Diffeomorph.refl (𝓡 2) SphereTwo ∞ ∧
          (∀ t ∈ _root_.Set.Icc (e p 2 + r ^ 2 / 2) (e q 2 - r ^ 2 / 2),
            Φ t '' {x | e x 2 = e p 2 + r ^ 2 / 2} = {x | e x 2 = t}) ∧
          ∃ δ : ℝ, 0 < δ ∧ δ ≤ r ^ 2 / 4 ∧
            4 * δ < (e q 2 - r ^ 2 / 2) - (e p 2 + r ^ 2 / 2) ∧
            (∀ t ∈ _root_.Set.Ioo (e p 2 + r ^ 2 / 2 - δ) (e p 2 + r ^ 2 / 2 + δ),
              ∀ z, e z 2 = e p 2 + r ^ 2 / 2 →
                HasDerivAt (fun s => (EuclideanSpace.equivProdLast 2 (e (Φ s z))).1)
                  (A₀.quadraticFiberVectorField (e p 2)
                    (t, (EuclideanSpace.equivProdLast 2 (e (Φ t z))).1)) t) ∧
            (∀ t ∈ _root_.Set.Ioo (e q 2 - r ^ 2 / 2 - δ) (e q 2 - r ^ 2 / 2 + δ),
              ∀ z, e z 2 = e p 2 + r ^ 2 / 2 →
                HasDerivAt (fun s => (EuclideanSpace.equivProdLast 2 (e (Φ s z))).1)
                  (A₁.quadraticFiberVectorField (e q 2)
                    (t, (EuclideanSpace.equivProdLast 2 (e (Φ t z))).1)) t) := by
  obtain ⟨r, hr, hab, χ₀, χ₁, B₀, B₁, hs₀, hs₁, _, _, hB₀, hB₁, hn₀, hn₁,
      hcap₀, hcap₁, hl₀, hl₁, Φ, ε, hε, hΦ, hΦinv, hΦa, hΦlevels, hradial₀, hradial₁⟩ :=
    exists_height_transport_radial_at_extrema he hp hq hmin hmax hpq hcrit
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  have hLe (z : SphereTwo) : ((L ∘ e) z).2 = e z 2 := rfl
  let A₀ := L.symm.toDiffeomorph.trans (B₀.trans L.toDiffeomorph)
  let A₁ := L.symm.toDiffeomorph.trans (B₁.trans L.toDiffeomorph)
  have hA₀ (z : EuclideanSpace ℝ (Fin 2) × ℝ) : (A₀ z).2 = z.2 :=
    (hB₀ (L.symm z)).trans (EuclideanSpace.equivProdLast_symm_last 2 z)
  have hA₁ (z : EuclideanSpace ℝ (Fin 2) × ℝ) : (A₁ z).2 = z.2 :=
    (hB₁ (L.symm z)).trans (EuclideanSpace.equivProdLast_symm_last 2 z)
  have hn₀' (y : EuclideanSpace ℝ (Fin 2)) (hy : y ∈ _root_.Metric.ball 0 (2 * r)) :
      L (e (χ₀ y)) = A₀ (y, e p 2 + 1 / 2 * ‖y‖ ^ 2) :=
    congrArg L (hn₀ y (hs₀.symm ▸ hy)).2.symm
  have hn₁' (y : EuclideanSpace ℝ (Fin 2)) (hy : y ∈ _root_.Metric.ball 0 (2 * r)) :
      L (e (χ₁ y)) = A₁ (y, e q 2 + (-1) / 2 * ‖y‖ ^ 2) :=
    congrArg L (hn₁ y (hs₁.symm ▸ hy)).2.symm
  let a := e p 2 + r ^ 2 / 2
  let b := e q 2 - r ^ 2 / 2
  let δ := _root_.Min.min (_root_.Min.min ε (r ^ 2 / 4)) ((b - a) / 8)
  have hδ : 0 < δ := lt_min (lt_min hε (by positivity)) (by dsimp [a, b]; linarith)
  have hδε : δ ≤ _root_.Min.min ε (r ^ 2 / 4) := min_le_left _ _
  have hδr : δ ≤ r ^ 2 / 4 := hδε.trans (min_le_right _ _)
  have hδab : 4 * δ < b - a := by
    have h := min_le_right (_root_.Min.min ε (r ^ 2 / 4)) ((b - a) / 8)
    change δ ≤ (b - a) / 8 at h
    dsimp [a, b] at *
    linarith
  refine ⟨r, hr, hab, A₀, A₁, hA₀, hA₁, ?_, ?_, Φ, hΦ, hΦinv, hΦa, hΦlevels,
    δ, hδ, hδr, hδab, ?_, ?_⟩
  · rw [← hcap₀, _root_.Set.image_image]
    apply _root_.Set.image_congr
    intro y hy
    exact hn₀' y (_root_.Metric.closedBall_subset_ball (by linarith : r < 2 * r) hy)
  · rw [← hcap₁, _root_.Set.image_image]
    apply _root_.Set.image_congr
    intro y hy
    exact hn₁' y (_root_.Metric.closedBall_subset_ball (by linarith : r < 2 * r) hy)
  · intro t ht z hz
    have hu : e p 2 + 1 / 2 * r ^ 2 = a := by dsimp [a]; ring
    apply hasDerivAt_of_radial_level_transport χ₀ (L ∘ e) (fun s => (Φ s).toEquiv)
      A₀ hA₀ (ε := ε) (a := a) (Or.inl rfl) hr hn₀'
      (by simpa only [hLe, hu] using hl₀) ?_ ?_ ?_ hz
    · simpa only [Diffeomorph.coe_toEquiv, hLe, hu] using hΦlevels a ⟨le_rfl, hab.le⟩
    · simp only [Diffeomorph.coe_toEquiv, inv_one]
      convert! hradial₀ using 1
    · rw [hu]
      constructor <;> linarith [ht.1, ht.2]
  · intro t ht z hz
    have hu : e q 2 + (-1) / 2 * r ^ 2 = b := by dsimp [b]; ring
    apply hasDerivAt_of_radial_level_transport χ₁ (L ∘ e) (fun s => (Φ s).toEquiv)
      A₁ hA₁ (ε := ε) (a := a) (Or.inr rfl) hr hn₁'
      (by simpa only [hLe, hu] using hl₁) ?_ ?_ ?_ hz
    · simpa only [Diffeomorph.coe_toEquiv, hLe, hu] using hΦlevels b ⟨hab.le, le_rfl⟩
    · simp only [Diffeomorph.coe_toEquiv, inv_neg, inv_one, neg_neg]
      convert! hradial₁ using 1
    · rw [hu]
      constructor <;> linarith [ht.1, ht.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_height_transport_with_quadratic_cap_velocity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_height_transport_with_quadratic_cap_velocity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_height_transport_with_quadratic_cap_velocity ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_height_transport_with_quadratic_cap_velocity

end DifferentialGeometry.Topology.SphereSeparation
