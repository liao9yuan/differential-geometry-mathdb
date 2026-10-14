import Submission.DifferentialGeometry.Topology.Manifold.EmbeddedHypersurface.LocalDefining
import Submission.DifferentialGeometry.Topology.Manifold.ModelWithCorners
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import Submission.DifferentialGeometry.External.Schoenflies.GeneralCrosscut
import Submission.DifferentialGeometry.Topology.Manifold.AddCircle
import Submission.DifferentialGeometry.Topology.PlanarJordan.RegularCurve
import Submission.DifferentialGeometry.Topology.PlanarJordan.Regions
import Submission.DifferentialGeometry.Topology.PlanarJordan.BandCutCorners
import Submission.DifferentialGeometry.Topology.Manifold.SectorRoundingFrontier
import Submission.DifferentialGeometry.Topology.Manifold.AmbientCornerRounding
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.DisjointUnion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology

namespace DifferentialGeometry.Topology.PlanarJordan

noncomputable section

local instance instChartedSpaceFinTwo : ChartedSpace PUnit.{1} (Fin 2) := ChartedSpace.ofDiscreteTopology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.instChartedSpaceFinTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.instChartedSpaceFinTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.instChartedSpaceFinTwo ``Submission.DifferentialGeometry.Topology.PlanarJordan.instChartedSpaceFinTwo

private def cornerCoordinates (a b : ℝ) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) where
  toFun z := (1 - a * z.1, b * z.2)
  invFun z := (a * (1 - z.1), b * z.2)
  left_inv := by
    intro z
    ext <;> dsimp
    · calc
        a * (1 - (1 - a * z.1)) = a ^ 2 * z.1 := by ring
        _ = z.1 := by rw [ha, one_mul]
    · calc
        b * (b * z.2) = b ^ 2 * z.2 := by ring
        _ = z.2 := by rw [hb, one_mul]
  right_inv := by
    intro z
    ext <;> dsimp
    · calc
        1 - a * (a * (1 - z.1)) = 1 - a ^ 2 * (1 - z.1) := by ring
        _ = z.1 := by rw [ha]; ring
    · calc
        b * (b * z.2) = b ^ 2 * z.2 := by ring
        _ = z.2 := by rw [hb, one_mul]
  contMDiff_toFun := (by fun_prop : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (1 - a * z.1, b * z.2))).contMDiff
  contMDiff_invFun := (by fun_prop : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (a * (1 - z.1), b * z.2))).contMDiff

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PlanarJordan.cornerCoordinates
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PlanarJordan.cornerCoordinates target :: scope.openDecls } }

private def taggedCornerChart (D : Schoenflies.Plane ≃ₘ[ℝ] (ℝ × ℝ))
    (i : Fin 2) (U : Set (ℝ × ℝ)) (hU : IsOpen U) :
    PartialDiffeomorph 𝓘(ℝ, Schoenflies.Plane) (𝓘(ℝ, PUnit.{1}).prod 𝓘(ℝ, ℝ × ℝ))
      Schoenflies.Plane (Fin 2 × (ℝ × ℝ)) ∞ where
  toFun x := (i, D x)
  invFun x := D.symm x.2
  source := D ⁻¹' U
  target := {i} ×ˢ U
  map_source' := fun _ hx => ⟨rfl, hx⟩
  map_target' := by intro p hp; simpa using hp.2
  left_inv' := fun _ _ => D.symm_apply_apply _
  right_inv' := by
    rintro ⟨j, z⟩ ⟨hj, hz⟩
    change (i, D (D.symm z)) = (j, z)
    rw [D.apply_symm_apply]
    exact Prod.ext hj.symm rfl
  open_source := hU.preimage D.continuous
  open_target := (isOpen_discrete ({i} : Set (Fin 2))).prod hU
  contMDiffOn_toFun := (contMDiff_const.prodMk D.contMDiff).contMDiffOn
  contMDiffOn_invFun := (D.symm.contMDiff.comp contMDiff_snd).contMDiffOn

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PlanarJordan.taggedCornerChart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PlanarJordan.taggedCornerChart target :: scope.openDecls } }

theorem exists_band_corner_chart
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane) {b r k : ℝ}
    (hb : b ^ 2 = 1) (hr : 0 < r) (hrlt : r < 1) (hk : 0 < k) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, Schoenflies.Plane) (𝓘(ℝ, PUnit.{1}).prod 𝓘(ℝ, ℝ × ℝ))
        Schoenflies.Plane (Fin 2 × (ℝ × ℝ)) ∞,
      e.source = B '' ((_root_.Set.Ioo (-1 - r) (-1 + r) ∪ _root_.Set.Ioo (1 - r) (1 + r)) ×ˢ _root_.Set.Ioo (-k) k) ∧
      e.target = _root_.Set.univ ×ˢ (_root_.Set.Ioo (-r) r ×ˢ _root_.Set.Ioo (-k) k) ∧
      (∀ z ∈ _root_.Set.Ioo (-r) r ×ˢ _root_.Set.Ioo (-k) k, e.symm (0, z) = B (-1 * (1 - z.1), b * z.2)) ∧
      (∀ z ∈ _root_.Set.Ioo (-r) r ×ˢ _root_.Set.Ioo (-k) k, e.symm (1, z) = B (1 - z.1, b * z.2)) ∧
      e.symm '' (_root_.Set.univ ×ˢ {(0 : ℝ × ℝ)}) = {B (-1, 0), B (1, 0)} := by
  let D₀ := B.symm.trans (cornerCoordinates (-1) b (by norm_num) hb)
  let D₁ := B.symm.trans (cornerCoordinates 1 b (by norm_num) hb)
  let U : Set (ℝ × ℝ) := _root_.Set.Ioo (-r) r ×ˢ _root_.Set.Ioo (-k) k
  let e₀ := taggedCornerChart D₀ 0 U (isOpen_Ioo.prod isOpen_Ioo)
  let e₁ := taggedCornerChart D₁ 1 U (isOpen_Ioo.prod isOpen_Ioo)
  have hs : Disjoint e₀.source e₁.source := by
    rw [_root_.Set.disjoint_left]
    intro p hp₀ hp₁
    change D₀ p ∈ U at hp₀
    change D₁ p ∈ U at hp₁
    have h₀ := hp₀.1.2
    have h₁ := hp₁.1.2
    change 1 - -1 * (B.symm p).1 < r at h₀
    change 1 - 1 * (B.symm p).1 < r at h₁
    linarith
  have ht : Disjoint e₀.target e₁.target := by
    rw [_root_.Set.disjoint_left]
    intro p hp₀ hp₁
    have h₀ : p.1 = 0 := hp₀.1
    have h₁ : p.1 = 1 := hp₁.1
    exact (by decide : (0 : Fin 2) ≠ 1) (h₀.symm.trans h₁)
  let e := e₀.disjointUnion e₁ hs ht
  have hEi₀ (z : ℝ × ℝ) (hz : z ∈ U) : e.symm (0, z) = B (-1 * (1 - z.1), b * z.2) :=
    e₀.disjointUnion_symm_apply_of_mem_left e₁ hs ht ⟨rfl, hz⟩
  have hEi₁ (z : ℝ × ℝ) (hz : z ∈ U) : e.symm (1, z) = B (1 - z.1, b * z.2) := by
    have h := e₀.disjointUnion_symm_apply_of_mem_right e₁ hs ht (x := (1, z)) ⟨rfl, hz⟩
    change e.symm (1, z) = B (1 * (1 - z.1), b * z.2) at h
    simpa only [one_mul] using h
  have hby (y : ℝ) : b * y ∈ _root_.Set.Ioo (-k) k ↔ y ∈ _root_.Set.Ioo (-k) k := by
    rcases sq_eq_one_iff.mp hb with rfl | rfl
    · simp
    · simp only [neg_one_mul, _root_.Set.mem_Ioo]
      constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> linarith
  have hS₀ (p : Schoenflies.Plane) : p ∈ e₀.source ↔
      (B.symm p).1 ∈ _root_.Set.Ioo (-1 - r) (-1 + r) ∧ (B.symm p).2 ∈ _root_.Set.Ioo (-k) k := by
    change ((1 - -1 * (B.symm p).1) ∈ _root_.Set.Ioo (-r) r ∧ b * (B.symm p).2 ∈ _root_.Set.Ioo (-k) k) ↔ _
    rw [hby]
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, hy⟩
    · rintro ⟨hx, hy⟩
      exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, hy⟩
  have hS₁ (p : Schoenflies.Plane) : p ∈ e₁.source ↔
      (B.symm p).1 ∈ _root_.Set.Ioo (1 - r) (1 + r) ∧ (B.symm p).2 ∈ _root_.Set.Ioo (-k) k := by
    change ((1 - 1 * (B.symm p).1) ∈ _root_.Set.Ioo (-r) r ∧ b * (B.symm p).2 ∈ _root_.Set.Ioo (-k) k) ↔ _
    rw [hby]
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨⟨by linarith [hx.2], by linarith [hx.1]⟩, hy⟩
    · rintro ⟨hx, hy⟩
      exact ⟨⟨by linarith [hx.2], by linarith [hx.1]⟩, hy⟩
  refine ⟨e, ?_, ?_, hEi₀, hEi₁, ?_⟩
  · ext p
    change (p ∈ e₀.source ∨ p ∈ e₁.source) ↔ _
    rw [hS₀, hS₁]
    constructor
    · rintro (hp | hp)
      · exact ⟨B.symm p, ⟨Or.inl hp.1, hp.2⟩, B.apply_symm_apply p⟩
      · exact ⟨B.symm p, ⟨Or.inr hp.1, hp.2⟩, B.apply_symm_apply p⟩
    · rintro ⟨z, ⟨hz, hy⟩, rfl⟩
      rw [B.symm_apply_apply]
      exact hz.elim (fun hx => Or.inl ⟨hx, hy⟩) (fun hx => Or.inr ⟨hx, hy⟩)
  · ext ⟨i, z⟩
    change ((i, z) ∈ ({0} ×ˢ U) ∪ ({1} ×ˢ U)) ↔ (i, z) ∈ _root_.Set.univ ×ˢ U
    fin_cases i <;> simp
  · have hzero : (0 : ℝ × ℝ) ∈ U := ⟨⟨neg_neg_of_pos hr, hr⟩, neg_neg_of_pos hk, hk⟩
    ext p
    constructor
    · rintro ⟨⟨i, z⟩, ⟨_, hz⟩, rfl⟩
      obtain rfl := mem_singleton_iff.mp hz
      fin_cases i
      · change e.symm (0, 0) ∈ {B (-1, 0), B (1, 0)}
        rw [hEi₀ 0 hzero]
        simp
      · change e.symm (1, 0) ∈ {B (-1, 0), B (1, 0)}
        rw [hEi₁ 0 hzero]
        simp
    · intro hp
      rcases mem_insert_iff.mp hp with rfl | hp
      · refine ⟨(0, 0), ⟨mem_univ _, rfl⟩, ?_⟩
        simpa using hEi₀ 0 hzero
      · obtain rfl := mem_singleton_iff.mp hp
        refine ⟨(1, 0), ⟨mem_univ _, rfl⟩, ?_⟩
        simpa using hEi₁ 0 hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_band_corner_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_band_corner_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_band_corner_chart ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_band_corner_chart

theorem exists_homeomorph_smoothing_band_corners
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane) {b r k : ℝ}
    (hb : b ^ 2 = 1) (hr : 0 < r) (hrlt : r < 1) (hk : 0 < k) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, Schoenflies.Plane) (𝓘(ℝ, PUnit.{1}).prod 𝓘(ℝ, ℝ × ℝ))
        Schoenflies.Plane (Fin 2 × (ℝ × ℝ)) ∞,
      e.source = B '' ((_root_.Set.Ioo (-1 - r) (-1 + r) ∪ _root_.Set.Ioo (1 - r) (1 + r)) ×ˢ _root_.Set.Ioo (-k) k) ∧
      e.target = _root_.Set.univ ×ˢ (_root_.Set.Ioo (-r) r ×ˢ _root_.Set.Ioo (-k) k) ∧
      (∀ z ∈ _root_.Set.Ioo (-r) r ×ˢ _root_.Set.Ioo (-k) k, e.symm (0, z) = B (-1 * (1 - z.1), b * z.2)) ∧
      (∀ z ∈ _root_.Set.Ioo (-r) r ×ˢ _root_.Set.Ioo (-k) k, e.symm (1, z) = B (1 - z.1, b * z.2)) ∧
      e.symm '' (_root_.Set.univ ×ˢ {(0 : ℝ × ℝ)}) = {B (-1, 0), B (1, 0)} ∧
      ∃ δ : ℝ, ∃ hδ : 0 < δ, δ < _root_.Min.min r k ∧ ∃ H : Schoenflies.Plane ≃ₜ Schoenflies.Plane,
        (∀ x ∈ e.source, H x = e.symm ((e x).1, Homeomorph.smoothAbsCorner hδ (e x).2)) ∧
        (∀ x ∈ e.source, H.symm x =
          e.symm ((e x).1, (Homeomorph.smoothAbsCorner hδ).symm (e x).2)) ∧
        IsCompact (e.symm '' (_root_.Set.univ ×ˢ _root_.Metric.closedBall (0 : ℝ × ℝ) δ)) ∧
        e.symm '' (_root_.Set.univ ×ˢ _root_.Metric.closedBall (0 : ℝ × ℝ) δ) ⊆ e.source ∧
        _root_.Set.EqOn H id (e.symm '' (_root_.Set.univ ×ˢ _root_.Metric.closedBall (0 : ℝ × ℝ) δ))ᶜ ∧
        _root_.Set.EqOn H.symm id (e.symm '' (_root_.Set.univ ×ˢ _root_.Metric.closedBall (0 : ℝ × ℝ) δ))ᶜ ∧
        (∀ x ∉ ({B (-1, 0), B (1, 0)} : Set Schoenflies.Plane),
          IsLocalDiffeomorphAt 𝓘(ℝ, Schoenflies.Plane) 𝓘(ℝ, Schoenflies.Plane) ∞ H x ∧
          IsLocalDiffeomorphAt 𝓘(ℝ, Schoenflies.Plane) 𝓘(ℝ, Schoenflies.Plane) ∞ H.symm (H x)) ∧
        (∀ A : Set Schoenflies.Plane,
          (∀ a ∈ ({-1, 1} : Set ℝ), ∀ z ∈ _root_.Set.Ioo (a - r) (a + r) ×ˢ _root_.Set.Ioo (-k) k,
            B z ∈ A ↔ a * z.1 ≤ 1 ∧ 0 ≤ b * z.2) →
          H '' A = e.toOpenPartialHomeomorph.smoothAbsQuadrantSet A δ) ∧
        (∀ A : Set Schoenflies.Plane,
          (∀ a ∈ ({-1, 1} : Set ℝ), ∀ z ∈ _root_.Set.Ioo (a - r) (a + r) ×ˢ _root_.Set.Ioo (-k) k,
            B z ∈ A ↔ 1 ≤ a * z.1 ∨ b * z.2 ≤ 0) →
          H '' A = (A \ e.source) ∪ e.symm ''
            (e.target ∩ {p | p.2.1 + p.2.2 ≤ Real.smoothAbs δ (p.2.1 - p.2.2)})) := by
  obtain ⟨e, hsource, htarget, hleft, hright, hzero⟩ := exists_band_corner_chart B hb hr hrlt hk
  let δ := _root_.Min.min r k / 2
  have hδ : 0 < δ := half_pos (lt_min hr hk)
  have hδlt : δ < _root_.Min.min r k := half_lt_self (lt_min hr hk)
  have hstrip : (_root_.Set.univ : Set (Fin 2)) ×ˢ _root_.Metric.closedBall (0 : ℝ × ℝ) δ ⊆ e.target := by
    rw [htarget]
    rintro ⟨i, x, y⟩ ⟨_, hz⟩
    have hh : _root_.Max.max |x| |y| ≤ δ := by
      simp only [_root_.Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq] at hz
      change _root_.Max.max |x - 0| |y - 0| ≤ δ at hz
      simpa only [sub_zero] using hz
    have hx := (le_max_left |x| |y|).trans hh
    have hy := (le_max_right |x| |y|).trans hh
    have hdr := hδlt.trans_le (min_le_left r k)
    have hdk := hδlt.trans_le (min_le_right r k)
    exact ⟨mem_univ _, ⟨by linarith [(abs_le.mp hx).1], by linarith [(abs_le.mp hx).2]⟩,
      by linarith [(abs_le.mp hy).1], by linarith [(abs_le.mp hy).2]⟩
  obtain ⟨H, hH, hHi, hK, hKs, hfix, hfixi, hquad, hreflex, hd⟩ :=
    e.exists_homeomorph_smoothAbs_corner hδ hstrip
  have hby (y : ℝ) : b * y ∈ _root_.Set.Ioo (-k) k ↔ y ∈ _root_.Set.Ioo (-k) k := by
    rcases sq_eq_one_iff.mp hb with rfl | rfl
    · simp
    · simp only [neg_one_mul, _root_.Set.mem_Ioo]
      constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> linarith
  have hbmul (y : ℝ) : b * (b * y) = y := by
    calc
      b * (b * y) = b ^ 2 * y := by ring
      _ = y := by rw [hb, one_mul]
  have hzleft (z : ℝ × ℝ) (hz : z ∈ _root_.Set.Ioo (-r) r ×ˢ _root_.Set.Ioo (-k) k) :
      (-1 * (1 - z.1), b * z.2) ∈ _root_.Set.Ioo (-1 - r) (-1 + r) ×ˢ _root_.Set.Ioo (-k) k :=
    ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, (hby z.2).mpr hz.2⟩
  have hzright (z : ℝ × ℝ) (hz : z ∈ _root_.Set.Ioo (-r) r ×ˢ _root_.Set.Ioo (-k) k) :
      (1 - z.1, b * z.2) ∈ _root_.Set.Ioo (1 - r) (1 + r) ×ˢ _root_.Set.Ioo (-k) k :=
    ⟨⟨by linarith [hz.1.2], by linarith [hz.1.1]⟩, (hby z.2).mpr hz.2⟩
  refine ⟨e, hsource, htarget, hleft, hright, hzero, δ, hδ, hδlt, H,
    hH, hHi, hK, hKs, hfix, hfixi, ?_, ?_, ?_⟩
  · intro x hx
    apply hd x
    rwa [hzero]
  · intro A hA
    apply hquad A
    rintro ⟨i, z⟩ hp
    have hz : z ∈ _root_.Set.Ioo (-r) r ×ˢ _root_.Set.Ioo (-k) k := (htarget ▸ hp).2
    fin_cases i
    · change e.symm (0, z) ∈ A ↔ _
      rw [hleft z hz, hA (-1) (by simp) _ (hzleft z hz)]
      simp only [neg_one_mul, neg_neg, hbmul]
      constructor <;> rintro ⟨h₀, h₁⟩ <;> exact ⟨by linarith, h₁⟩
    · change e.symm (1, z) ∈ A ↔ _
      rw [hright z hz, hA 1 (by simp) _ (hzright z hz)]
      simp only [one_mul, hbmul]
      constructor <;> rintro ⟨h₀, h₁⟩ <;> exact ⟨by linarith, h₁⟩
  · intro A hA
    apply hreflex A
    rintro ⟨i, z⟩ hp
    have hz : z ∈ _root_.Set.Ioo (-r) r ×ˢ _root_.Set.Ioo (-k) k := (htarget ▸ hp).2
    fin_cases i
    · change e.symm (0, z) ∈ A ↔ _
      rw [hleft z hz, hA (-1) (by simp) _ (hzleft z hz)]
      simp only [neg_one_mul, neg_neg, hbmul]
      exact or_congr (by constructor <;> intro h <;> linarith) Iff.rfl
    · change e.symm (1, z) ∈ A ↔ _
      rw [hright z hz, hA 1 (by simp) _ (hzright z hz)]
      simp only [one_mul, hbmul]
      exact or_congr (by constructor <;> intro h <;> linarith) Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_smoothing_band_corners then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_smoothing_band_corners"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_smoothing_band_corners ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_smoothing_band_corners

private theorem smoothAbs_profile_fderiv_ne_zero (δ : ℝ) (q : ℝ × ℝ) :
    fderiv ℝ (fun z : ℝ × ℝ => Real.smoothAbs δ (z.1 - z.2) - (z.1 + z.2)) q ≠ 0 := by
  let f : (ℝ × ℝ) → ℝ := fun z => Real.smoothAbs δ (z.1 - z.2) - (z.1 + z.2)
  have hf : ContDiff ℝ ∞ f :=
    ((Real.smoothAbs.contDiff δ).comp (contDiff_fst.sub contDiff_snd)).sub
      (contDiff_fst.add contDiff_snd)
  have hc : HasDerivAt (fun t : ℝ => (q.1 + t, q.2 + t)) (1, 1) 0 :=
    ((hasDerivAt_id 0).const_add q.1).prodMk ((hasDerivAt_id 0).const_add q.2)
  have heq : (fun t : ℝ => f (q.1 + t, q.2 + t)) =
      fun t => f q - 2 * t := by
    funext t
    dsimp [f]
    rw [show q.1 + t - (q.2 + t) = q.1 - q.2 by ring]
    ring
  have hd := (hf.differentiable (by simp) (q.1 + 0, q.2 + 0)).hasFDerivAt.comp_hasDerivAt 0 hc
  have hd' : HasDerivAt (fun t : ℝ => f q - 2 * t) (-2) 0 := by
    simpa only [zero_sub, mul_one, id_eq, Pi.sub_apply] using!
      (hasDerivAt_const 0 (f q)).sub ((hasDerivAt_id 0).const_mul 2)
  have hd'' : fderiv ℝ f q (1, 1) = -2 := by
    have hp : (q.1 + (0 : ℝ), q.2 + (0 : ℝ)) = q := by simp
    simp only [Function.comp_def] at hd
    rw [heq] at hd
    simpa only [hp] using hd.unique hd'
  intro hz
  change fderiv ℝ f q = 0 at hz
  rw [hz, zero_apply] at hd''
  norm_num at hd''

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PlanarJordan.smoothAbs_profile_fderiv_ne_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PlanarJordan.smoothAbs_profile_fderiv_ne_zero target :: scope.openDecls } }

private theorem exists_regular_defining_function_of_corner_frontier
    (e : PartialDiffeomorph 𝓘(ℝ, Schoenflies.Plane) (𝓘(ℝ, PUnit.{1}).prod 𝓘(ℝ, ℝ × ℝ))
      Schoenflies.Plane (Fin 2 × (ℝ × ℝ)) ∞)
    {δ : ℝ} {C : Set Schoenflies.Plane}
    (hfront : e.toOpenPartialHomeomorph.IsImage C
      {p | Real.smoothAbs δ (p.2.1 - p.2.2) = p.2.1 + p.2.2})
    {p : Schoenflies.Plane} (hp : p ∈ e.source) :
    ∃ U : Set Schoenflies.Plane, IsOpen U ∧ p ∈ U ∧
      ∃ f : Schoenflies.Plane → ℝ, ContDiffOn ℝ ∞ f U ∧
        (∀ x ∈ U, x ∈ C ↔ f x = 0) ∧ fderiv ℝ f p ≠ 0 := by
  let f : Schoenflies.Plane → ℝ := fun x =>
    Real.smoothAbs δ ((e x).2.1 - (e x).2.2) - ((e x).2.1 + (e x).2.2)
  have he : ContDiffOn ℝ ∞ (fun x => (e x).2) e.source :=
    contMDiffOn_iff_contDiffOn.mp (contMDiff_snd.comp_contMDiffOn e.contMDiffOn)
  have hf : ContDiffOn ℝ ∞ f e.source :=
    ((Real.smoothAbs.contDiff δ).comp_contDiffOn (he.fst.sub he.snd)).sub (he.fst.add he.snd)
  refine ⟨e.source, e.open_source, hp, f, hf, ?_, ?_⟩
  · intro x hx
    exact (hfront hx).symm.trans sub_eq_zero.symm
  · let z := (e p).2
    let i := (e p).1
    let k : (ℝ × ℝ) → Schoenflies.Plane := fun y => e.symm (i, y)
    have hk : ContDiffAt ℝ ∞ k z := contMDiffAt_iff_contDiffAt.mp
      ((e.symm.contMDiffOn.contMDiffAt (e.open_target.mem_nhds (e.map_source hp))).comp z
        (contMDiffAt_const.prodMk contMDiffAt_id))
    have hkp : k z = p := e.left_inv hp
    have hnb : ∀ᶠ y in 𝓝 z, (i, y) ∈ e.target :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
        (e.open_target.mem_nhds (e.map_source hp))
    let g : (ℝ × ℝ) → ℝ := fun y => Real.smoothAbs δ (y.1 - y.2) - (y.1 + y.2)
    have hfg : (f ∘ k) =ᶠ[𝓝 z] g := hnb.mono fun y hy => by
      dsimp only [Function.comp_apply, f, k, g]
      have hei : e (e.symm (i, y)) = (i, y) := e.right_inv hy
      simp only [hei]
    have hfp := (hf.contDiffAt (e.open_source.mem_nhds hp)).differentiableAt (by simp)
    intro hz
    apply smoothAbs_profile_fderiv_ne_zero δ z
    change fderiv ℝ g z = 0
    rw [← hfg.fderiv_eq, fderiv_comp z (hkp.symm ▸ hfp) (hk.differentiableAt (by simp)), hkp, hz]
    exact ContinuousLinearMap.zero_comp _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_regular_defining_function_of_corner_frontier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PlanarJordan.exists_regular_defining_function_of_corner_frontier target :: scope.openDecls } }

private theorem isJordanCurve_image_homeomorph {J : Set Schoenflies.Plane}
    (hJ : Schoenflies.IsJordanCurve J) (H : Schoenflies.Plane ≃ₜ Schoenflies.Plane) :
    Schoenflies.IsJordanCurve (H '' J) := by
  obtain ⟨f, hf, rfl⟩ := hJ
  refine ⟨H ∘ f, ⟨H.continuous.comp_continuousOn hf.continuousOn, ?_, ?_⟩, ?_⟩
  · simp only [Function.comp_apply, hf.closes]
  · exact H.injective.injOn.comp hf.injOn (_root_.Set.mapsTo_univ _ _)
  · rw [_root_.Set.image_comp]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_image_homeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_image_homeomorph target :: scope.openDecls } }

theorem exists_circle_embedding_of_corner_rounding
    {δ : ℝ}
    (e : PartialDiffeomorph 𝓘(ℝ, Schoenflies.Plane) (𝓘(ℝ, PUnit.{1}).prod 𝓘(ℝ, ℝ × ℝ))
      Schoenflies.Plane (Fin 2 × (ℝ × ℝ)) ∞)
    {J : Set Schoenflies.Plane} (hJ : Schoenflies.IsJordanCurve J)
    (hreg : ∀ p ∈ J, p ∉ e.source →
      ∃ U : Set Schoenflies.Plane, ∃ f : Schoenflies.Plane → ℝ,
        IsOpen U ∧ p ∈ U ∧ ContDiffOn ℝ ∞ f U ∧
        (∀ x ∈ U, x ∈ J ↔ f x = 0) ∧ fderiv ℝ f p ≠ 0)
    (H : Schoenflies.Plane ≃ₜ Schoenflies.Plane)
    {K : Set Schoenflies.Plane} (hK : IsClosed K) (hKs : K ⊆ e.source)
    (hfix : _root_.Set.EqOn H.symm id Kᶜ)
    (himage : e.toOpenPartialHomeomorph.IsImage (H '' closure (Schoenflies.inside J))
        {p | Real.smoothAbs δ (p.2.1 - p.2.2) ≤ p.2.1 + p.2.2} ∨
      e.toOpenPartialHomeomorph.IsImage (H '' closure (Schoenflies.inside J))
        {p | p.2.1 + p.2.2 ≤ Real.smoothAbs δ (p.2.1 - p.2.2)}) :
    ∃ γ : AddCircle (1 : ℝ) → Schoenflies.Plane,
      _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ ∧
        range γ = H '' J := by
  have hfront : e.toOpenPartialHomeomorph.IsImage (H '' J)
      {p | Real.smoothAbs δ (p.2.1 - p.2.2) = p.2.1 + p.2.2} := by
    rcases himage with hi | hi
    · have hh := hi.frontier
      rw [Real.smoothAbs.frontier_quadrant, ← H.image_frontier,
        (Schoenflies.jordan_curve_theorem hJ).frontier_closure_inside] at hh
      exact hh
    · have hh := hi.frontier
      rw [Real.smoothAbs.frontier_complementary_quadrant, ← H.image_frontier,
        (Schoenflies.jordan_curve_theorem hJ).frontier_closure_inside] at hh
      exact hh
  apply exists_circle_embedding_of_local_regular_defining_functions (isJordanCurve_image_homeomorph hJ H)
  intro p hp
  by_cases hps : p ∈ e.source
  · obtain ⟨U, hU, hpU, f, hf, hz, hr⟩ :=
      exists_regular_defining_function_of_corner_frontier e hfront hps
    exact ⟨U, f, hU, hpU, hf, hz, hr⟩
  · have hpK : p ∈ Kᶜ := fun h => hps (hKs h)
    have hHp : H.symm p = p := hfix hpK
    have hpJ : p ∈ J := by
      have hh : H.symm p ∈ J := mem_image_equiv.mp hp
      rwa [hHp] at hh
    obtain ⟨U, f, hU, hpU, hf, hz, hr⟩ := hreg p hpJ hps
    refine ⟨U ∩ Kᶜ, f, hU.inter hK.isOpen_compl, ⟨hpU, hpK⟩,
      hf.mono _root_.Set.inter_subset_left, ?_, hr⟩
    intro x hx
    have hHx : H.symm x = x := hfix hx.2
    have hm : x ∈ H '' J ↔ H.symm x ∈ J := _root_.Set.mem_image_equiv
    rw [hm, hHx]
    exact hz x hx.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_circle_embedding_of_corner_rounding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_circle_embedding_of_corner_rounding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_circle_embedding_of_corner_rounding ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_circle_embedding_of_corner_rounding

private theorem exists_smooth_rounding_of_band_corner_curve
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane) {b r k : ℝ}
    (hb : b ^ 2 = 1) (hr : 0 < r) (hrlt : r < 1) (hk : 0 < k)
    {J : Set Schoenflies.Plane} (hJ : Schoenflies.IsJordanCurve J)
    (hreg : ∀ p ∈ J, p ∉ ({B (-1, 0), B (1, 0)} : Set Schoenflies.Plane) →
      ∃ U : Set Schoenflies.Plane, ∃ f : Schoenflies.Plane → ℝ,
        IsOpen U ∧ p ∈ U ∧ ContDiffOn ℝ ∞ f U ∧
        (∀ x ∈ U, x ∈ J ↔ f x = 0) ∧ fderiv ℝ f p ≠ 0)
    (hprofile :
      (∀ a ∈ ({-1, 1} : Set ℝ), ∀ z ∈ _root_.Set.Ioo (a - r) (a + r) ×ˢ _root_.Set.Ioo (-k) k,
        B z ∈ closure (Schoenflies.inside J) ↔ a * z.1 ≤ 1 ∧ 0 ≤ b * z.2) ∨
      (∀ a ∈ ({-1, 1} : Set ℝ), ∀ z ∈ _root_.Set.Ioo (a - r) (a + r) ×ˢ _root_.Set.Ioo (-k) k,
        B z ∈ closure (Schoenflies.inside J) ↔ 1 ≤ a * z.1 ∨ b * z.2 ≤ 0)) :
    ∃ H : Schoenflies.Plane ≃ₜ Schoenflies.Plane, ∃ K : Set Schoenflies.Plane,
      IsCompact K ∧
      K ⊆ B '' ((_root_.Set.Ioo (-1 - r) (-1 + r) ∪ _root_.Set.Ioo (1 - r) (1 + r)) ×ˢ _root_.Set.Ioo (-k) k) ∧
      _root_.Set.EqOn H id Kᶜ ∧ _root_.Set.EqOn H.symm id Kᶜ ∧
      ∃ e : PartialDiffeomorph 𝓘(ℝ, Schoenflies.Plane) (𝓘(ℝ, PUnit.{1}).prod 𝓘(ℝ, ℝ × ℝ))
          Schoenflies.Plane (Fin 2 × (ℝ × ℝ)) ∞,
        e.source = B '' ((_root_.Set.Ioo (-1 - r) (-1 + r) ∪ _root_.Set.Ioo (1 - r) (1 + r)) ×ˢ _root_.Set.Ioo (-k) k) ∧
        e.target = _root_.Set.univ ×ˢ (_root_.Set.Ioo (-r) r ×ˢ _root_.Set.Ioo (-k) k) ∧
        (∀ z ∈ _root_.Set.Ioo (-r) r ×ˢ _root_.Set.Ioo (-k) k, e.symm (0, z) = B (-1 * (1 - z.1), b * z.2)) ∧
        (∀ z ∈ _root_.Set.Ioo (-r) r ×ˢ _root_.Set.Ioo (-k) k, e.symm (1, z) = B (1 - z.1, b * z.2)) ∧
        e.symm '' (_root_.Set.univ ×ˢ {(0 : ℝ × ℝ)}) = {B (-1, 0), B (1, 0)} ∧
        ∃ δ : ℝ, ∃ hδ : 0 < δ, δ < _root_.Min.min r k ∧
          K = e.symm '' (_root_.Set.univ ×ˢ _root_.Metric.closedBall (0 : ℝ × ℝ) δ) ∧
          (∀ x ∈ e.source, H x = e.symm ((e x).1, Homeomorph.smoothAbsCorner hδ (e x).2)) ∧
          (∀ x ∈ e.source, H.symm x =
            e.symm ((e x).1, (Homeomorph.smoothAbsCorner hδ).symm (e x).2)) ∧
          (∀ x ∉ ({B (-1, 0), B (1, 0)} : Set Schoenflies.Plane),
            IsLocalDiffeomorphAt 𝓘(ℝ, Schoenflies.Plane) 𝓘(ℝ, Schoenflies.Plane) ∞ H x ∧
            IsLocalDiffeomorphAt 𝓘(ℝ, Schoenflies.Plane) 𝓘(ℝ, Schoenflies.Plane) ∞ H.symm (H x)) ∧
      ∃ γ : AddCircle (1 : ℝ) → Schoenflies.Plane,
        _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ ∧
          range γ = H '' J := by
  obtain ⟨e, hsource, htarget, hleft, hright, hzero, δ, hδ, hδlt, H,
    hH, hHi, hK, hKs, hfix, hfixi, hloc, hquad, hreflex⟩ :=
      exists_homeomorph_smoothing_band_corners B hb hr hrlt hk
  have hpoints : ({B (-1, 0), B (1, 0)} : Set Schoenflies.Plane) ⊆ e.source := by
    rw [← hzero]
    rintro _ ⟨⟨i, z⟩, ⟨_, hz⟩, rfl⟩
    have hz0 : z = 0 := hz
    apply e.map_target
    rw [htarget, hz0]
    exact ⟨mem_univ _, ⟨neg_neg_of_pos hr, hr⟩, neg_neg_of_pos hk, hk⟩
  have himage : e.toOpenPartialHomeomorph.IsImage (H '' closure (Schoenflies.inside J))
        {p | Real.smoothAbs δ (p.2.1 - p.2.2) ≤ p.2.1 + p.2.2} ∨
      e.toOpenPartialHomeomorph.IsImage (H '' closure (Schoenflies.inside J))
        {p | p.2.1 + p.2.2 ≤ Real.smoothAbs δ (p.2.1 - p.2.2)} := by
    rcases hprofile with hprofile | hprofile
    · left
      rw [hquad _ hprofile]
      intro x hx
      exact (e.toOpenPartialHomeomorph.mem_smoothAbsQuadrantSet_iff _ _ hx).symm
    · right
      rw [hreflex _ hprofile]
      intro x hx
      constructor
      · intro hq
        exact Or.inr ⟨e x, ⟨e.map_source hx, hq⟩, e.left_inv hx⟩
      · rintro (⟨_, hn⟩ | ⟨q, hq, hqx⟩)
        · exact (hn hx).elim
        · have he : e x = q := by
            rw [← hqx]
            exact e.right_inv hq.1
          change (e x) ∈ {p | p.2.1 + p.2.2 ≤ Real.smoothAbs δ (p.2.1 - p.2.2)}
          rw [he]
          exact hq.2
  obtain ⟨γ, hγ, hrange⟩ := exists_circle_embedding_of_corner_rounding e hJ
    (fun p hp hps => hreg p hp (fun h => hps (hpoints h))) H hK.isClosed hKs hfixi himage
  exact ⟨H, _, hK, hsource ▸ hKs, hfix, hfixi, e, hsource, htarget, hleft, hright, hzero,
    δ, hδ, hδlt, rfl, hH, hHi, hloc, γ, hγ, hrange⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_smooth_rounding_of_band_corner_curve
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PlanarJordan.exists_smooth_rounding_of_band_corner_curve target :: scope.openDecls } }

end

end DifferentialGeometry.Topology.PlanarJordan

section

open _root_.Manifold _root_.Submission.Manifold _root_.Submission.Schoenflies
open _root_.Submission.DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.PlanarJordan

private theorem exists_local_defining_function_circle
    {γ : AddCircle (1 : ℝ) → Plane}
    (hγ : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) ∞ γ)
    {p : Plane} (hp : p ∈ _root_.Set.range γ) :
    ∃ U : Set Plane, ∃ f : Plane → ℝ,
      IsOpen U ∧ p ∈ U ∧ ContDiffOn ℝ ∞ f U ∧
      (∀ x ∈ U, x ∈ _root_.Set.range γ ↔ f x = 0) ∧ fderiv ℝ f p ≠ 0 := by
  let L : ℝ ≃L[ℝ] MorseModel 1 := ContinuousLinearEquiv.ofFinrankEq (by simp [MorseModel])
  let I := (𝓘(ℝ, ℝ)).transContinuousLinearEquiv L
  let J := (𝓘(ℝ, Plane)).transContinuousLinearEquiv (EuclideanSpace.equiv (Fin 2) ℝ)
  let D₁ : AddCircle (1 : ℝ) ≃ₘ⟮𝓘(ℝ, ℝ), I⟯ AddCircle (1 : ℝ) :=
    ContinuousLinearEquiv.toTransContinuousLinearEquiv 𝓘(ℝ, ℝ) _ L
  let D₂ : Plane ≃ₘ⟮𝓘(ℝ, Plane), J⟯ Plane :=
    ContinuousLinearEquiv.toTransContinuousLinearEquiv 𝓘(ℝ, Plane) _
      (EuclideanSpace.equiv (Fin 2) ℝ)
  have hD₁ := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
    D₁.symm.isLocalDiffeomorph D₁.symm.injective
  have hD₂ := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
    D₂.isLocalDiffeomorph D₂.injective
  have hγ' : _root_.Manifold.IsSmoothEmbedding I J ∞ γ := hD₂.comp (hγ.comp hD₁ (by simp)) (by simp)
  obtain ⟨t, rfl⟩ := hp
  obtain ⟨U, hU, htU, f, hf, hz, hr⟩ :=
    DifferentialGeometry.Manifold.EmbeddedHypersurface.exists_local_definingFunction I J hγ' t
  have hf' : ContDiffOn ℝ ∞ f U := by
    have h : ContMDiffOn 𝓘(ℝ, Plane) 𝓘(ℝ, ℝ) ∞ f U := by simpa [J] using hf
    exact h.contDiffOn
  refine ⟨U, f, hU, htU, hf', fun x hx => (hz x hx).symm, ?_⟩
  intro hdf
  have hmd : MDifferentiableAt 𝓘(ℝ, Plane) 𝓘(ℝ, ℝ) f (γ t) :=
    (hf'.contDiffAt (hU.mem_nhds htU)).contMDiffAt.mdifferentiableAt (by simp)
  have hd := mfderiv_comp (γ t) hmd (D₂.symm.contMDiff.mdifferentiableAt (by simp))
  change mfderiv J 𝓘(ℝ, ℝ) f (γ t) = _ at hd
  have hfzero : mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, ℝ) f (D₂.symm (γ t)) = 0 := by
    change mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, ℝ) f (γ t) = 0
    rwa [mfderiv_eq_fderiv]
  apply hr (γ t) htU
  rw [hd, hfzero, ContinuousLinearMap.zero_comp]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_local_defining_function_circle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PlanarJordan.exists_local_defining_function_circle target :: scope.openDecls } }

theorem exists_local_defining_function_cut_loop_away_endpoints
    {γ : AddCircle (1 : ℝ) → Plane}
    (hγ : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) ∞ γ)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) {a b : ℝ}
    {A₀ A₁ : Set Plane}
    (hcut : IsCutPair (_root_.Set.range γ) (B (a, 0)) (B (b, 0)) A₀ A₁)
    (havoid : B '' (_root_.Set.Ioo a b ×ˢ {(0 : ℝ)}) ⊆ (_root_.Set.range γ)ᶜ)
    {p : Plane} (hp : p ∈ A₀ ∪ B '' (_root_.Set.Icc a b ×ˢ {(0 : ℝ)}))
    (hpends : p ∉ ({B (a, 0), B (b, 0)} : Set Plane)) :
    ∃ U : Set Plane, ∃ f : Plane → ℝ,
      IsOpen U ∧ p ∈ U ∧ ContDiffOn ℝ ∞ f U ∧
      (∀ x ∈ U, x ∈ A₀ ∪ B '' (_root_.Set.Icc a b ×ˢ {(0 : ℝ)}) ↔ f x = 0) ∧
      fderiv ℝ f p ≠ 0 := by
  let P := B '' (_root_.Set.Icc a b ×ˢ {(0 : ℝ)})
  have hPclosed : IsClosed P := ((isCompact_Icc.prod isCompact_singleton).image B.continuous).isClosed
  have hmiddle {x : Plane} (hx : x ∈ P)
      (hne : x ∉ ({B (a, 0), B (b, 0)} : Set Plane)) :
      x ∈ B '' (_root_.Set.Ioo a b ×ˢ {(0 : ℝ)}) := by
    obtain ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩ := hx
    have hu0 : u = 0 := hu
    subst u
    have hta : t ≠ a := by
      intro h
      apply hne
      simp only [h, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, true_or]
    have htb : t ≠ b := by
      intro h
      apply hne
      simp only [h, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, or_true]
    exact ⟨(t, 0), ⟨⟨lt_of_le_of_ne ht.1 hta.symm, lt_of_le_of_ne ht.2 htb⟩, rfl⟩, rfl⟩
  rcases hp with hpA | hpP
  · have hpC := hcut.fst_subset hpA
    have hpnotP : p ∉ P := fun hpP => havoid (hmiddle hpP hpends) hpC
    have hpnotA₁ : p ∉ A₁ := fun hpA₁ => hpends (hcut.inter_eq ▸ ⟨hpA, hpA₁⟩)
    obtain ⟨V, f, hV, hpV, hf, hzero, hr⟩ := exists_local_defining_function_circle hγ hpC
    let U := V ∩ A₁ᶜ ∩ Pᶜ
    refine ⟨U, f, (hV.inter hcut.snd.isArc.isClosed.isOpen_compl).inter hPclosed.isOpen_compl,
      ⟨⟨hpV, hpnotA₁⟩, hpnotP⟩, hf.mono (fun _ hx => hx.1.1), ?_, hr⟩
    intro x hx
    rw [← hzero x hx.1.1]
    constructor
    · intro h
      rcases h with hxA | hxP
      · exact hcut.fst_subset hxA
      · exact (hx.2 hxP).elim
    · intro hxC
      have hxunion : x ∈ A₀ ∪ A₁ := hcut.union_eq.symm ▸ hxC
      exact Or.inl (hxunion.resolve_right hx.1.2)
  · obtain ⟨z, hz, hpz⟩ := hmiddle hpP hpends
    have hpC : p ∉ _root_.Set.range γ := havoid ⟨z, hz, hpz⟩
    let f : Plane → ℝ := fun x => (B.symm x).2
    let U : Set Plane := (B.symm ⁻¹' (_root_.Set.Ioo a b ×ˢ _root_.Set.univ)) ∩ (_root_.Set.range γ)ᶜ
    have hCclosed : IsClosed (_root_.Set.range γ) := isCompact_range hγ.contMDiff.continuous |>.isClosed
    have hU : IsOpen U :=
      ((isOpen_Ioo.prod isOpen_univ).preimage B.symm.continuous).inter hCclosed.isOpen_compl
    have hpU : p ∈ U := by
      refine ⟨?_, hpC⟩
      change B.symm p ∈ _root_.Set.Ioo a b ×ˢ _root_.Set.univ
      rw [← hpz, B.symm_apply_apply]
      exact ⟨hz.1, _root_.Set.mem_univ _⟩
    have hf : ContDiff ℝ ∞ f := contDiff_snd.comp B.symm.contMDiff.contDiff
    refine ⟨U, f, hU, hpU, hf.contDiffOn, ?_, ?_⟩
    · intro x hx
      constructor
      · rintro (hxA | ⟨w, hw, rfl⟩)
        · exact (hx.2 (hcut.fst_subset hxA)).elim
        · change (B.symm (B w)).2 = 0
          rw [B.symm_apply_apply]
          exact hw.2
      · intro hfx
        refine Or.inr ⟨B.symm x, ⟨⟨hx.1.1.1.le, hx.1.1.2.le⟩, hfx⟩, B.apply_symm_apply x⟩
    · intro hdf
      have hfun : f ∘ B = Prod.snd := by
        funext w
        exact congrArg Prod.snd (B.symm_apply_apply w)
      have hd := fderiv_comp z (hf.differentiable (by simp) (B z))
        (B.contMDiff.contDiff.differentiable (by simp) z)
      rw [hfun, hpz, hdf, ContinuousLinearMap.zero_comp] at hd
      have hdv := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1)) hd
      rw [hasFDerivAt_snd.fderiv] at hdv
      norm_num at hdv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_local_defining_function_cut_loop_away_endpoints then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_local_defining_function_cut_loop_away_endpoints"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_local_defining_function_cut_loop_away_endpoints ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_local_defining_function_cut_loop_away_endpoints

end DifferentialGeometry.Topology.PlanarJordan

end

namespace DifferentialGeometry.Topology.PlanarJordan

attribute [local instance] instChartedSpaceFinTwo

private theorem exists_smooth_rounding_of_band_cut
    {γ : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hγ : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane) {b r k : ℝ}
    (hb : b ^ 2 = 1) (hr : 0 < r) (hrlt : r < 1) (hk : 0 < k)
    {A₀ A₁ : Set Schoenflies.Plane}
    (hcut : Schoenflies.IsCutPair (_root_.Set.range γ) (B (-1, 0)) (B (1, 0)) A₀ A₁)
    (havoid : B '' (_root_.Set.Ioo (-1 : ℝ) 1 ×ˢ {(0 : ℝ)}) ⊆ (_root_.Set.range γ)ᶜ)
    (hJ : Schoenflies.IsJordanCurve (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {(0 : ℝ)})))
    (hprofile :
      (∀ a ∈ ({-1, 1} : Set ℝ), ∀ z ∈ _root_.Set.Ioo (a - r) (a + r) ×ˢ _root_.Set.Ioo (-k) k,
        B z ∈ closure (Schoenflies.inside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {(0 : ℝ)}))) ↔
          a * z.1 ≤ 1 ∧ 0 ≤ b * z.2) ∨
      (∀ a ∈ ({-1, 1} : Set ℝ), ∀ z ∈ _root_.Set.Ioo (a - r) (a + r) ×ˢ _root_.Set.Ioo (-k) k,
        B z ∈ closure (Schoenflies.inside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {(0 : ℝ)}))) ↔
          1 ≤ a * z.1 ∨ b * z.2 ≤ 0)) :
    ∃ H : Schoenflies.Plane ≃ₜ Schoenflies.Plane, ∃ K : Set Schoenflies.Plane,
      IsCompact K ∧
      K ⊆ B '' ((_root_.Set.Ioo (-1 - r) (-1 + r) ∪ _root_.Set.Ioo (1 - r) (1 + r)) ×ˢ _root_.Set.Ioo (-k) k) ∧
      _root_.Set.EqOn H id Kᶜ ∧ _root_.Set.EqOn H.symm id Kᶜ ∧
      ∃ e : PartialDiffeomorph 𝓘(ℝ, Schoenflies.Plane) (𝓘(ℝ, PUnit.{1}).prod 𝓘(ℝ, ℝ × ℝ))
          Schoenflies.Plane (Fin 2 × (ℝ × ℝ)) ∞,
        e.source = B '' ((_root_.Set.Ioo (-1 - r) (-1 + r) ∪ _root_.Set.Ioo (1 - r) (1 + r)) ×ˢ _root_.Set.Ioo (-k) k) ∧
        e.target = _root_.Set.univ ×ˢ (_root_.Set.Ioo (-r) r ×ˢ _root_.Set.Ioo (-k) k) ∧
        (∀ z ∈ _root_.Set.Ioo (-r) r ×ˢ _root_.Set.Ioo (-k) k, e.symm (0, z) = B (-1 * (1 - z.1), b * z.2)) ∧
        (∀ z ∈ _root_.Set.Ioo (-r) r ×ˢ _root_.Set.Ioo (-k) k, e.symm (1, z) = B (1 - z.1, b * z.2)) ∧
        e.symm '' (_root_.Set.univ ×ˢ {(0 : ℝ × ℝ)}) = {B (-1, 0), B (1, 0)} ∧
        ∃ δ : ℝ, ∃ hδ : 0 < δ, δ < _root_.Min.min r k ∧
          K = e.symm '' (_root_.Set.univ ×ˢ _root_.Metric.closedBall (0 : ℝ × ℝ) δ) ∧
          (∀ x ∈ e.source, H x = e.symm ((e x).1, Homeomorph.smoothAbsCorner hδ (e x).2)) ∧
          (∀ x ∈ e.source, H.symm x =
            e.symm ((e x).1, (Homeomorph.smoothAbsCorner hδ).symm (e x).2)) ∧
          (∀ x ∉ ({B (-1, 0), B (1, 0)} : Set Schoenflies.Plane),
            IsLocalDiffeomorphAt 𝓘(ℝ, Schoenflies.Plane) 𝓘(ℝ, Schoenflies.Plane) ∞ H x ∧
            IsLocalDiffeomorphAt 𝓘(ℝ, Schoenflies.Plane) 𝓘(ℝ, Schoenflies.Plane) ∞ H.symm (H x)) ∧
      ∃ η : AddCircle (1 : ℝ) → Schoenflies.Plane,
        _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ η ∧
          range η = H '' (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {(0 : ℝ)})) := by
  exact exists_smooth_rounding_of_band_corner_curve B hb hr hrlt hk hJ
    (fun _ hp hends => exists_local_defining_function_cut_loop_away_endpoints hγ B hcut havoid hp hends)
    hprofile

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_smooth_rounding_of_band_cut
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PlanarJordan.exists_smooth_rounding_of_band_cut target :: scope.openDecls } }

theorem exists_smooth_roundings_of_attached_band_cuts
    {γ : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hγ : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane) {h : ℝ} (hh : 0 < h)
    (hedges : ∀ a ∈ ({-1, 1} : Set ℝ), (fun u => B (a, u)) '' _root_.Set.Ioo (-h) h ⊆ _root_.Set.range γ)
    (havoid : B '' (_root_.Set.Ioo (-1 : ℝ) 1 ×ˢ _root_.Set.Ioo (-h) h) ⊆ (_root_.Set.range γ)ᶜ) :
    ∃ A₀ A₁ : Set Schoenflies.Plane,
      Schoenflies.IsCutPair (_root_.Set.range γ) (B (-1, 0)) (B (1, 0)) A₀ A₁ ∧
      Schoenflies.IsJordanCurve (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
      Schoenflies.IsJordanCurve (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
      ∃ Ω V₀ V₁ : Set Schoenflies.Plane,
        B '' (_root_.Set.Ioo (-1 : ℝ) 1 ×ˢ _root_.Set.Ioo (-h) h) ⊆ Ω ∧
        Ω \ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0}) = V₀ ∪ V₁ ∧ Disjoint V₀ V₁ ∧
        V₀.Nonempty ∧ V₁.Nonempty ∧
        (∀ z ∈ V₀, connectedComponentIn (Ω \ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) z = V₀) ∧
        (∀ z ∈ V₁, connectedComponentIn (Ω \ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) z = V₁) ∧
        closure V₀ ∩ _root_.Set.range γ = A₀ ∧ closure V₁ ∩ _root_.Set.range γ = A₁ ∧
        B '' (_root_.Set.Ioo (-1 : ℝ) 1 ×ˢ _root_.Set.Ioo 0 h) ⊆ V₀ ∧
        B '' (_root_.Set.Ioo (-1 : ℝ) 1 ×ˢ _root_.Set.Ioo (-h) 0) ⊆ V₁ ∧
        (∀ a ∈ ({-1, 1} : Set ℝ),
          (fun u => B (a, u)) '' _root_.Set.Ioo 0 h ⊆ A₀ ∧
          (fun u => B (a, u)) '' _root_.Set.Ioo (-h) 0 ⊆ A₁) ∧
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∃ k : ℝ, 0 < k ∧ k < h ∧
          ((((Ω = Schoenflies.inside (_root_.Set.range γ) ∧
              V₀ = Schoenflies.inside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
              V₁ = Schoenflies.inside (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0}))) ∧
            ∀ a ∈ ({-1, 1} : Set ℝ), ∀ z ∈ _root_.Set.Ioo (a - r) (a + r) ×ˢ _root_.Set.Ioo (-k) k,
              (B z ∈ Schoenflies.inside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ↔
                a * z.1 < 1 ∧ 0 < z.2) ∧
              (B z ∈ closure (Schoenflies.inside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0}))) ↔
                a * z.1 ≤ 1 ∧ 0 ≤ z.2) ∧
              (B z ∈ Schoenflies.inside (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ↔
                a * z.1 < 1 ∧ z.2 < 0) ∧
              (B z ∈ closure (Schoenflies.inside (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0}))) ↔
                a * z.1 ≤ 1 ∧ z.2 ≤ 0)) ∨
          (((Ω = Schoenflies.outside (_root_.Set.range γ) ∧
              V₀ = Schoenflies.outside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
              V₁ = Schoenflies.inside (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
              Schoenflies.inside (_root_.Set.range γ) ⊆
                Schoenflies.inside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})))) ∧
            ∀ a ∈ ({-1, 1} : Set ℝ), ∀ z ∈ _root_.Set.Ioo (a - r) (a + r) ×ˢ _root_.Set.Ioo (-k) k,
              (B z ∈ Schoenflies.inside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ↔
                1 < a * z.1 ∨ z.2 < 0) ∧
              (B z ∈ closure (Schoenflies.inside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0}))) ↔
                1 ≤ a * z.1 ∨ z.2 ≤ 0) ∧
              (B z ∈ Schoenflies.inside (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ↔
                a * z.1 < 1 ∧ z.2 < 0) ∧
              (B z ∈ closure (Schoenflies.inside (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0}))) ↔
                a * z.1 ≤ 1 ∧ z.2 ≤ 0)) ∨
          (((Ω = Schoenflies.outside (_root_.Set.range γ) ∧
              V₀ = Schoenflies.inside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
              V₁ = Schoenflies.outside (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
              Schoenflies.inside (_root_.Set.range γ) ⊆
                Schoenflies.inside (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})))) ∧
            ∀ a ∈ ({-1, 1} : Set ℝ), ∀ z ∈ _root_.Set.Ioo (a - r) (a + r) ×ˢ _root_.Set.Ioo (-k) k,
              (B z ∈ Schoenflies.inside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ↔
                a * z.1 < 1 ∧ 0 < z.2) ∧
              (B z ∈ closure (Schoenflies.inside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0}))) ↔
                a * z.1 ≤ 1 ∧ 0 ≤ z.2) ∧
              (B z ∈ Schoenflies.inside (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ↔
                1 < a * z.1 ∨ 0 < z.2) ∧
              (B z ∈ closure (Schoenflies.inside (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0}))) ↔
                1 ≤ a * z.1 ∨ 0 ≤ z.2)))) ∧
          ∃ H₀ H₁ : Schoenflies.Plane ≃ₜ Schoenflies.Plane,
            ∃ K₀ K₁ : Set Schoenflies.Plane,
              IsCompact K₀ ∧ IsCompact K₁ ∧
              K₀ ⊆ B '' ((_root_.Set.Ioo (-1 - r) (-1 + r) ∪ _root_.Set.Ioo (1 - r) (1 + r)) ×ˢ _root_.Set.Ioo (-k) k) ∧
              K₁ ⊆ B '' ((_root_.Set.Ioo (-1 - r) (-1 + r) ∪ _root_.Set.Ioo (1 - r) (1 + r)) ×ˢ _root_.Set.Ioo (-k) k) ∧
              _root_.Set.EqOn H₀ id K₀ᶜ ∧ _root_.Set.EqOn H₀.symm id K₀ᶜ ∧
              _root_.Set.EqOn H₁ id K₁ᶜ ∧ _root_.Set.EqOn H₁.symm id K₁ᶜ ∧
              ∃ e₀ e₁ : PartialDiffeomorph 𝓘(ℝ, Schoenflies.Plane)
                  (𝓘(ℝ, PUnit.{1}).prod 𝓘(ℝ, ℝ × ℝ)) Schoenflies.Plane (Fin 2 × (ℝ × ℝ)) ∞,
                e₀.source = B '' ((_root_.Set.Ioo (-1 - r) (-1 + r) ∪ _root_.Set.Ioo (1 - r) (1 + r)) ×ˢ _root_.Set.Ioo (-k) k) ∧
                e₁.source = B '' ((_root_.Set.Ioo (-1 - r) (-1 + r) ∪ _root_.Set.Ioo (1 - r) (1 + r)) ×ˢ _root_.Set.Ioo (-k) k) ∧
                e₀.target = _root_.Set.univ ×ˢ (_root_.Set.Ioo (-r) r ×ˢ _root_.Set.Ioo (-k) k) ∧
                e₁.target = _root_.Set.univ ×ˢ (_root_.Set.Ioo (-r) r ×ˢ _root_.Set.Ioo (-k) k) ∧
                (∀ z ∈ _root_.Set.Ioo (-r) r ×ˢ _root_.Set.Ioo (-k) k, e₀.symm (0, z) = B (-1 * (1 - z.1), z.2)) ∧
                (∀ z ∈ _root_.Set.Ioo (-r) r ×ˢ _root_.Set.Ioo (-k) k, e₀.symm (1, z) = B (1 - z.1, z.2)) ∧
                (∀ z ∈ _root_.Set.Ioo (-r) r ×ˢ _root_.Set.Ioo (-k) k, e₁.symm (0, z) = B (-1 * (1 - z.1), -z.2)) ∧
                (∀ z ∈ _root_.Set.Ioo (-r) r ×ˢ _root_.Set.Ioo (-k) k, e₁.symm (1, z) = B (1 - z.1, -z.2)) ∧
                e₀.symm '' (_root_.Set.univ ×ˢ {(0 : ℝ × ℝ)}) = {B (-1, 0), B (1, 0)} ∧
                e₁.symm '' (_root_.Set.univ ×ˢ {(0 : ℝ × ℝ)}) = {B (-1, 0), B (1, 0)} ∧
                ∃ δ₀ : ℝ, ∃ hδ₀ : 0 < δ₀, δ₀ < _root_.Min.min r k ∧
                ∃ δ₁ : ℝ, ∃ hδ₁ : 0 < δ₁, δ₁ < _root_.Min.min r k ∧
                  K₀ = e₀.symm '' (_root_.Set.univ ×ˢ _root_.Metric.closedBall (0 : ℝ × ℝ) δ₀) ∧
                  K₁ = e₁.symm '' (_root_.Set.univ ×ˢ _root_.Metric.closedBall (0 : ℝ × ℝ) δ₁) ∧
                  (∀ x ∈ e₀.source, H₀ x = e₀.symm ((e₀ x).1, Homeomorph.smoothAbsCorner hδ₀ (e₀ x).2)) ∧
                  (∀ x ∈ e₀.source, H₀.symm x =
                    e₀.symm ((e₀ x).1, (Homeomorph.smoothAbsCorner hδ₀).symm (e₀ x).2)) ∧
                  (∀ x ∈ e₁.source, H₁ x = e₁.symm ((e₁ x).1, Homeomorph.smoothAbsCorner hδ₁ (e₁ x).2)) ∧
                  (∀ x ∈ e₁.source, H₁.symm x =
                    e₁.symm ((e₁ x).1, (Homeomorph.smoothAbsCorner hδ₁).symm (e₁ x).2)) ∧
                  (∀ x ∉ ({B (-1, 0), B (1, 0)} : Set Schoenflies.Plane),
                    IsLocalDiffeomorphAt 𝓘(ℝ, Schoenflies.Plane) 𝓘(ℝ, Schoenflies.Plane) ∞ H₀ x ∧
                    IsLocalDiffeomorphAt 𝓘(ℝ, Schoenflies.Plane) 𝓘(ℝ, Schoenflies.Plane) ∞ H₀.symm (H₀ x)) ∧
                  (∀ x ∉ ({B (-1, 0), B (1, 0)} : Set Schoenflies.Plane),
                    IsLocalDiffeomorphAt 𝓘(ℝ, Schoenflies.Plane) 𝓘(ℝ, Schoenflies.Plane) ∞ H₁ x ∧
                    IsLocalDiffeomorphAt 𝓘(ℝ, Schoenflies.Plane) 𝓘(ℝ, Schoenflies.Plane) ∞ H₁.symm (H₁ x)) ∧
              ∃ η₀ η₁ : AddCircle (1 : ℝ) → Schoenflies.Plane,
                _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ η₀ ∧
                _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ η₁ ∧
                _root_.Set.range η₀ = H₀ '' (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
                range η₁ = H₁ '' (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) := by
  obtain ⟨A₀, A₁, hcut, hJ₀, hJ₁, Ω, V₀, V₁, hband, hcover, hdisj,
    hn₀, hn₁, hcomp₀, hcomp₁, hcl₀, hcl₁, hupper, hlower, hedgearcs,
    r, hr, hrlt, k, hk, hkh, hcases⟩ :=
      exists_cut_regions_with_corner_charts_of_attached_band hγ B hh hedges havoid
  have hcore : B '' (_root_.Set.Ioo (-1 : ℝ) 1 ×ˢ {(0 : ℝ)}) ⊆ (_root_.Set.range γ)ᶜ := by
    apply Subset.trans (_root_.Set.image_mono (_root_.Set.prod_mono Subset.rfl ?_)) havoid
    intro y hy
    have hy0 : y = 0 := hy
    rw [hy0]
    exact ⟨neg_neg_of_pos hh, hh⟩
  have hprofile₀ :
      (∀ a ∈ ({-1, 1} : Set ℝ), ∀ z ∈ _root_.Set.Ioo (a - r) (a + r) ×ˢ _root_.Set.Ioo (-k) k,
        B z ∈ closure (Schoenflies.inside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {(0 : ℝ)}))) ↔
          a * z.1 ≤ 1 ∧ 0 ≤ (1 : ℝ) * z.2) ∨
      (∀ a ∈ ({-1, 1} : Set ℝ), ∀ z ∈ _root_.Set.Ioo (a - r) (a + r) ×ˢ _root_.Set.Ioo (-k) k,
        B z ∈ closure (Schoenflies.inside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {(0 : ℝ)}))) ↔
          1 ≤ a * z.1 ∨ (1 : ℝ) * z.2 ≤ 0) := by
    rcases hcases with hc | hc | hc
    · exact Or.inl (fun a ha z hz => by simpa only [one_mul] using (hc.2 a ha z hz).2.1)
    · exact Or.inr (fun a ha z hz => by simpa only [one_mul] using (hc.2 a ha z hz).2.1)
    · exact Or.inl (fun a ha z hz => by simpa only [one_mul] using (hc.2 a ha z hz).2.1)
  have hprofile₁ :
      (∀ a ∈ ({-1, 1} : Set ℝ), ∀ z ∈ _root_.Set.Ioo (a - r) (a + r) ×ˢ _root_.Set.Ioo (-k) k,
        B z ∈ closure (Schoenflies.inside (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {(0 : ℝ)}))) ↔
          a * z.1 ≤ 1 ∧ 0 ≤ (-1 : ℝ) * z.2) ∨
      (∀ a ∈ ({-1, 1} : Set ℝ), ∀ z ∈ _root_.Set.Ioo (a - r) (a + r) ×ˢ _root_.Set.Ioo (-k) k,
        B z ∈ closure (Schoenflies.inside (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {(0 : ℝ)}))) ↔
          1 ≤ a * z.1 ∨ (-1 : ℝ) * z.2 ≤ 0) := by
    rcases hcases with hc | hc | hc
    · exact Or.inl (fun a ha z hz => by
        simpa only [neg_one_mul, neg_nonneg] using (hc.2 a ha z hz).2.2.2)
    · exact Or.inl (fun a ha z hz => by
        simpa only [neg_one_mul, neg_nonneg] using (hc.2 a ha z hz).2.2.2)
    · exact Or.inr (fun a ha z hz => by
        simpa only [neg_one_mul, neg_nonpos] using (hc.2 a ha z hz).2.2.2)
  obtain ⟨H₀, K₀, hK₀, hK₀s, hfix₀, hfixi₀, e₀, hs₀, ht₀, hl₀, hr₀, hz₀,
    δ₀, hδ₀, hδ₀lt, hK₀eq, hH₀, hHi₀, hloc₀, η₀, hη₀, hη₀range⟩ :=
    exists_smooth_rounding_of_band_cut hγ B (by norm_num : (1 : ℝ) ^ 2 = 1)
      hr hrlt hk hcut hcore hJ₀ hprofile₀
  obtain ⟨H₁, K₁, hK₁, hK₁s, hfix₁, hfixi₁, e₁, hs₁, ht₁, hl₁, hr₁, hz₁,
    δ₁, hδ₁, hδ₁lt, hK₁eq, hH₁, hHi₁, hloc₁, η₁, hη₁, hη₁range⟩ :=
    exists_smooth_rounding_of_band_cut hγ B (by norm_num : (-1 : ℝ) ^ 2 = 1)
      hr hrlt hk hcut.symm hcore hJ₁ hprofile₁
  refine ⟨A₀, A₁, hcut, hJ₀, hJ₁, Ω, V₀, V₁, hband, hcover, hdisj,
    hn₀, hn₁, hcomp₀, hcomp₁, hcl₀, hcl₁, hupper, hlower, hedgearcs,
    r, hr, hrlt, k, hk, hkh, hcases, H₀, H₁, K₀, K₁, hK₀, hK₁, hK₀s, hK₁s,
    hfix₀, hfixi₀, hfix₁, hfixi₁, e₀, e₁, hs₀, hs₁, ht₀, ht₁,
    by simpa only [one_mul] using hl₀, by simpa only [one_mul] using hr₀,
    by simpa only [neg_one_mul] using hl₁, by simpa only [neg_one_mul] using hr₁, hz₀, hz₁,
    δ₀, hδ₀, hδ₀lt, δ₁, hδ₁, hδ₁lt, hK₀eq, hK₁eq, hH₀, hHi₀, hH₁, hHi₁, hloc₀, hloc₁,
    η₀, η₁, hη₀, hη₁, hη₀range, hη₁range⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_smooth_roundings_of_attached_band_cuts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_smooth_roundings_of_attached_band_cuts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_smooth_roundings_of_attached_band_cuts ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_smooth_roundings_of_attached_band_cuts

end DifferentialGeometry.Topology.PlanarJordan
