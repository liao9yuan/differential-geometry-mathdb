import Submission.DifferentialGeometry.Analysis.InnerProductSpace.EuclideanSplit
import Submission.DifferentialGeometry.Topology.Morse.OneSaddleIncidence
import Submission.DifferentialGeometry.Topology.Morse.RegularLevel.QuadraticCap
import Submission.DifferentialGeometry.Topology.SphereSeparation.StandardSphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.SphereSeparation

private theorem image_subset_and_disjoint_of_component_level
    {M X Z : Type*} [TopologicalSpace M] (e : M → X × ℝ) (he : Function.Injective e)
    (β : Z → M) (B : Z → X) {a : ℝ} {p q : M} {Kp Kq : Set Z} {D C : Set X}
    (hB : ∀ z ∈ Kp ∪ Kq, (e (β z)).1 = B z)
    (hKp : β '' Kp ⊆ connectedComponentIn {x | a ≤ (e x).2} p ∩ {x | (e x).2 = a})
    (hKq : β '' Kq ⊆ connectedComponentIn {x | a ≤ (e x).2} q ∩ {x | (e x).2 = a})
    (hdisj : Disjoint (connectedComponentIn {x | a ≤ (e x).2} p)
      (connectedComponentIn {x | a ≤ (e x).2} q))
    (hcircle : (fun x => (e x).1) ''
      (connectedComponentIn {x | a ≤ (e x).2} p ∩ {x | (e x).2 = a}) = C)
    (hdisk : D ∩ ((fun x => (e x).1) '' {x | (e x).2 = a}) = C) :
    B '' Kp ⊆ C ∧ Disjoint (B '' Kq) D := by
  constructor
  · rintro y ⟨z, hz, rfl⟩
    exact hcircle.subset ⟨β z, hKp (_root_.Set.mem_image_of_mem β hz), hB z (Or.inl hz)⟩
  · apply disjoint_left.mpr
    rintro y ⟨z, hz, rfl⟩ hzD
    have hzq := hKq (_root_.Set.mem_image_of_mem β hz)
    have hzC := hdisk.subset ⟨hzD, ⟨β z, hzq.2, hB z (Or.inr hz)⟩⟩
    obtain ⟨x, ⟨hxp, hxa⟩, hxB⟩ := hcircle.symm.subset hzC
    have heq : x = β z := he (Prod.ext (hxB.trans (hB z (Or.inr hz)).symm)
      (hxa.trans hzq.2.symm))
    exact disjoint_left.mp hdisj (heq ▸ hxp) hzq.1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.image_subset_and_disjoint_of_component_level
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.image_subset_and_disjoint_of_component_level target :: scope.openDecls } }

theorem exists_saddleBandLevelCurve_incidence_of_one_saddle
    {e : SphereTwo → EuclideanThree} (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) (fun x => e x 2) x →
      IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) x)
    (hinj : _root_.Set.InjOn (fun x => e x 2) {x | IsCriticalPointAt (𝓡 2) (fun x => e x 2) x})
    (hone : {p | IsCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧ sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}.ncard = 1)
    (hconn : ∀ a : ℝ, IsPreconnected {x | e x 2 < a})
    (B : (ℝ × ℝ) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 2))
    {β : (ℝ × ℝ) → SphereTwo} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hzero : (0, 0) ∈ U)
    (hβ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ β U)
    {c s : ℝ} (hs : 0 < s)
    (hgraph : ∀ z ∈ U, EuclideanSpace.equivProdLast 2 (e (β z)) =
      (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    (hβcrit : IsCriticalPointAt (𝓡 2) (fun x => e x 2) (β (0, 0)))
    (hβindex : sigNeg (chartHessianAt
      (fun y => e ((extChartAt (𝓡 2) (β (0, 0))).symm y) 2)
      (extChartAt (𝓡 2) (β (0, 0)) (β (0, 0)))) = 1) :
    ∃ p : SphereTwo,
      IsLocalMax (fun x => e x 2) p ∧
      IsNondegenerateCriticalPointAt (𝓡 2) (fun x => e x 2) p ∧
      ¬ IsMaxOn (fun x => e x 2) _root_.Set.univ p ∧
      ∃ δ k : ℝ, 0 < δ ∧ c + s + δ ≤ e p 2 ∧ 0 < k ∧ k < 1 ∧
        ∃ σ ∈ ({-1, 1} : Set ℝ), ∀ τ ∈ _root_.Set.Ioo (0 : ℝ) δ,
          let a := c + s + τ
          let Kp := saddleBandLevelCurve s τ σ '' _root_.Set.Icc (-k) k
          let Kq := saddleBandLevelCurve s τ (-σ) '' _root_.Set.Icc (-k) k
          IsCompact Kp ∧ IsCompact Kq ∧ IsCompact (Kp ∪ Kq) ∧ Kp ∪ Kq ⊆ U ∧
          (∀ z ∈ Kp ∪ Kq, (1 - z.1 ^ 2) * z.2 ≠ 0) ∧
          (∀ z ∈ Kp ∪ Kq, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = a) ∧
          a < e p 2 ∧
          (∀ x, e x 2 ∈ _root_.Set.Ico a (e p 2) → ¬ IsCriticalPointAt (𝓡 2) (fun y => e y 2) x) ∧
          ∀ r : ℝ, 0 < r → a < e p 2 - r ^ 2 / 2 →
          ∀ A : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ),
            (∀ z, (A z).2 = z.2) →
            (EuclideanSpace.equivProdLast 2 ∘ e) ''
                connectedComponentIn {x | e p 2 - r ^ 2 / 2 ≤ e x 2} p =
              (fun y => A (y, e p 2 + (-1) / 2 * ‖y‖ ^ 2)) '' _root_.Metric.closedBall 0 r →
          ∀ Φ : ℝ → (EuclideanSpace ℝ (Fin 2)) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2)),
            ContDiff ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin 2) => Φ z.1 z.2) →
            Φ a = Diffeomorph.refl (𝓡 2) (EuclideanSpace ℝ (Fin 2)) ∞ →
            (∀ t ∈ _root_.Set.Icc a (e p 2 - r ^ 2 / 2),
              Φ t '' ((fun x => (EuclideanSpace.equivProdLast 2 (e x)).1) '' {x | e x 2 = a}) =
                (fun x => (EuclideanSpace.equivProdLast 2 (e x)).1) '' {x | e x 2 = t}) →
            let T := fun y => Φ a ((Φ (e p 2 - r ^ 2 / 2)).symm
              (A (y, e p 2 - r ^ 2 / 2)).1)
            T '' _root_.Metric.closedBall 0 r ∩
                ((fun x => (EuclideanSpace.equivProdLast 2 (e x)).1) '' {x | e x 2 = a}) =
              T '' _root_.Metric.sphere 0 r →
            B '' Kp ⊆ T '' _root_.Metric.sphere 0 r ∧ Disjoint (B '' Kq) (T '' _root_.Metric.closedBall 0 r) := by
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => e x 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp he.contMDiff
  have hg : ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ (fun x => (L (e x)).1) :=
    contDiff_fst.contMDiff.comp (L.contDiff.contMDiff.comp he.contMDiff)
  have hheight (z : ℝ × ℝ) (hz : z ∈ U) :
      e (β z) 2 = c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 :=
    congrArg Prod.snd (hgraph z hz)
  have hβheight : e (β (0, 0)) 2 = c + s := by simpa using hheight (0, 0) hzero
  obtain ⟨m, p, q, _, hsp, hpq, _, _, hpmax, hpnd, _, hregular,
    δ, k, hδ, hδbound, hk, hkone, σ, hσ, hcurves⟩ :=
    exists_saddleBandLevelCurve_subset_superlevel_components_of_one_saddle hf hnd hinj hone hconn
      B hU hzero hβ (fun z _ => hg.contMDiffAt) hs
      (fun z hz => congrArg Prod.fst (hgraph z hz)) hheight hβcrit hβindex
  refine ⟨p, hpmax, hpnd, (fun hpglob => hpq.not_ge (hpglob (_root_.Set.mem_univ q))),
    δ, k, hδ, hδbound, hk, hkone, σ, hσ, ?_⟩
  intro τ hτ
  dsimp only
  let a := c + s + τ
  let Kp := saddleBandLevelCurve s τ σ '' _root_.Set.Icc (-k) k
  let Kq := saddleBandLevelCurve s τ (-σ) '' _root_.Set.Icc (-k) k
  have hI : _root_.Set.Icc (-k) k ⊆ _root_.Set.Ioo (-1 : ℝ) 1 := by
    intro u hu
    exact ⟨by linarith [hu.1], hu.2.trans_lt hkone⟩
  have hcompact (ε : ℝ) : IsCompact (saddleBandLevelCurve s τ ε '' _root_.Set.Icc (-k) k) :=
    isCompact_Icc.image_of_continuousOn ((contDiffOn_saddleBandLevelCurve hs.le hτ.1 ε).continuousOn.mono hI)
  have hσsq : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσne : σ ≠ 0 := by intro h; rw [h] at hσsq; norm_num at hσsq
  have hregcurve (ε : ℝ) (hε : ε ≠ 0) : ∀ z ∈ saddleBandLevelCurve s τ ε '' _root_.Set.Icc (-k) k,
      (1 - z.1 ^ 2) * z.2 ≠ 0 := by
    rintro _ ⟨u, hu, rfl⟩
    exact saddleBandLevelCurve_regular hs.le hτ.1 hε (hI hu)
  have hlevelcurve (ε : ℝ) (hε : ε ^ 2 = 1) : ∀ z ∈ saddleBandLevelCurve s τ ε '' _root_.Set.Icc (-k) k,
      c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2 = a := by
    rintro _ ⟨u, hu, rfl⟩
    exact saddleBandLevelCurve_height hs.le hτ.1 hε (hI hu) c
  have ha : a ∈ _root_.Set.Ioo (e (β (0, 0)) 2) (e p 2) := by
    rw [hβheight]
    exact ⟨by dsimp [a]; linarith [hτ.1], by dsimp [a]; linarith [hτ.2]⟩
  have hcurvest := hcurves τ hτ
  have hKU : Kp ∪ Kq ⊆ U := _root_.Set.union_subset hcurvest.1 hcurvest.2.1
  refine ⟨hcompact σ, hcompact (-σ), (hcompact σ).union (hcompact (-σ)), hKU,
    ?_, ?_, ha.2, hregular a ha, ?_⟩
  · intro z hz
    rcases hz with hz | hz
    · exact hregcurve σ hσne z hz
    · exact hregcurve (-σ) (neg_ne_zero.mpr hσne) z hz
  · intro z hz
    rcases hz with hz | hz
    · exact hlevelcurve σ hσsq z hz
    · exact hlevelcurve (-σ) (by simpa only [neg_sq] using hσsq) z hz
  intro r hr hab A hA hcap Φ hΦ hΦa hlevels hdisk
  have hbp : e p 2 - r ^ 2 / 2 < e p 2 := by nlinarith [sq_pos_of_pos hr]
  have hboundary := image_superlevel_component_level_eq_sphere_of_quadratic_cap
    (e := L ∘ e) (I := 𝓡 2) (c := e p 2) (α := -1)
    (L.toHomeomorph.isEmbedding.comp he.isEmbedding) hf hab.le
    (by ring) (by norm_num) hr.le
    (isClosed_Icc.preimage hf.continuous).isCompact
    (fun x hx => hregular a ha x ⟨hx.1, hx.2.trans_lt hbp⟩) hbp.le A hA hcap
    (fun t => (Φ t).toEquiv)
    (fun x _ => (hΦ.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn)
    (by intro y _; change Φ a y = y; rw [hΦa]; rfl) hlevels
  exact image_subset_and_disjoint_of_component_level (L ∘ e)
    (L.injective.comp he.isEmbedding.injective) β B
    (fun z hz => congrArg Prod.fst (hgraph z (hKU hz)))
    hcurvest.2.2.1 hcurvest.2.2.2.1 hcurvest.2.2.2.2
    (hboundary a ⟨le_rfl, hab.le⟩) hdisk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_saddleBandLevelCurve_incidence_of_one_saddle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_saddleBandLevelCurve_incidence_of_one_saddle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_saddleBandLevelCurve_incidence_of_one_saddle ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_saddleBandLevelCurve_incidence_of_one_saddle

end DifferentialGeometry.Topology.SphereSeparation
