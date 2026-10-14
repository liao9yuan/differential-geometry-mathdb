import Submission.DifferentialGeometry.Analysis.ODE.Flow.Planar.SquareOrbitStrip
import Submission.DifferentialGeometry.Analysis.ODE.Flow.Planar.SmoothLeftEdgeCoordinates
import Submission.DifferentialGeometry.Analysis.Calculus.Interpolation.IntervalReparametrization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set
open scoped _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Analysis

def leftEdgeSquareMap {P : Type*} (φ : P → _root_.Flow ℝ ℂ) (τ : P × ℝ → ℝ)
    (D : ℝ → Diffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ∞) (q : P × ℂ) : ℂ :=
  φ q.1 (D (τ (q.1, q.2.im)) q.2.re) (q.2.im • Complex.I)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.leftEdgeSquareMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.leftEdgeSquareMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.leftEdgeSquareMap ``Submission.DifferentialGeometry.Analysis.leftEdgeSquareMap

theorem exists_smooth_inverse_leftEdgeSquareMap
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {v : P × ℂ → ℂ} (hv : ContDiff ℝ ∞ v) (φ : P → _root_.Flow ℝ ℂ)
    (hφ : ContDiff ℝ ∞ (fun q : P × ℝ × ℂ ↦ φ q.1 q.2.1 q.2.2)) {S : Set P}
    (hnz : ∀ p ∈ S, ∀ z, v (p, z) ≠ 0)
    (hderiv : ∀ p ∈ S, ∀ z t, HasDerivAt (fun s ↦ φ p s z) (v (p, φ p t z)) t)
    (hfixed : ∀ p ∈ S, ∀ z : ℂ,
      z.re ≤ 0 ∨ 1 ≤ z.re ∨ z.im ≤ 0 ∨ 1 ≤ z.im → v (p, z) = 1)
    {τ : P × ℝ → ℝ} (hτ : ContDiffOn ℝ ∞ τ (S ×ˢ _root_.Set.Icc 0 1))
    (hτpos : ∀ p ∈ S, ∀ y ∈ _root_.Set.Icc (0 : ℝ) 1, 0 < τ (p, y))
    (hexit : ∀ p ∈ S, ∀ y ∈ _root_.Set.Icc (0 : ℝ) 1, (φ p (τ (p, y)) (y • Complex.I)).re = 1)
    (D : ℝ → Diffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ∞)
    (hD : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ ↦ D q.1 q.2) (_root_.Set.Ioi 0 ×ˢ _root_.Set.univ))
    (hDi : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ ↦ (D q.1).symm q.2) (_root_.Set.Ioi 0 ×ˢ _root_.Set.univ))
    (hDmap : ∀ r : ℝ, 0 < r → _root_.Set.BijOn (D r) (_root_.Set.Icc 0 1) (_root_.Set.Icc 0 r)) :
    ∃ G : P × ℂ → ℂ,
      ContDiffOn ℝ ∞ (leftEdgeSquareMap φ τ D)
        (S ×ˢ Complex.reProdIm (_root_.Set.Icc 0 1) (_root_.Set.Icc 0 1)) ∧
      ContDiffOn ℝ ∞ G (S ×ˢ Complex.reProdIm (_root_.Set.Icc 0 1) (_root_.Set.Icc 0 1)) ∧
      ∀ p ∈ S,
        _root_.Set.MapsTo (fun z ↦ leftEdgeSquareMap φ τ D (p, z))
          (Complex.reProdIm (_root_.Set.Icc 0 1) (_root_.Set.Icc 0 1)) (Complex.reProdIm (_root_.Set.Icc 0 1) (_root_.Set.Icc 0 1)) ∧
        _root_.Set.MapsTo (fun z ↦ G (p, z))
          (Complex.reProdIm (_root_.Set.Icc 0 1) (_root_.Set.Icc 0 1)) (Complex.reProdIm (_root_.Set.Icc 0 1) (_root_.Set.Icc 0 1)) ∧
        (∀ z ∈ Complex.reProdIm (_root_.Set.Icc (0 : ℝ) 1) (_root_.Set.Icc 0 1), G (p, leftEdgeSquareMap φ τ D (p, z)) = z) ∧
        ∀ z ∈ Complex.reProdIm (_root_.Set.Icc (0 : ℝ) 1) (_root_.Set.Icc 0 1), leftEdgeSquareMap φ τ D (p, G (p, z)) = z := by
  let K : Set ℂ := Complex.reProdIm (_root_.Set.Icc 0 1) (_root_.Set.Icc 0 1)
  let Q : Set (P × ℂ) := S ×ˢ K
  let F := leftEdgeSquareMap φ τ D
  have hvs (p : P) : ContDiff ℝ ∞ (fun z ↦ v (p, z)) :=
    hv.comp (contDiff_const.prodMk contDiff_id)
  have htime : ContDiffOn ℝ ∞ (fun q : P × ℂ ↦ τ (q.1, q.2.im)) Q :=
    hτ.comp (contDiffOn_fst.prodMk (Complex.imCLM.contDiff.comp_contDiffOn contDiffOn_snd))
      (fun q hq ↦ ⟨hq.1, hq.2.2⟩)
  have hchange : ContDiffOn ℝ ∞ (fun q : P × ℂ ↦ D (τ (q.1, q.2.im)) q.2.re) Q :=
    hD.comp (htime.prodMk (Complex.reCLM.contDiff.comp_contDiffOn contDiffOn_snd))
      (fun q hq ↦ ⟨hτpos q.1 hq.1 q.2.im hq.2.2, _root_.Set.mem_univ _⟩)
  have hF : ContDiffOn ℝ ∞ F Q :=
    hφ.comp_contDiffOn (contDiffOn_fst.prodMk (hchange.prodMk
      ((Complex.imCLM.contDiff.comp_contDiffOn contDiffOn_snd).smul contDiffOn_const)))
  have hFmap (p : P) (hp : p ∈ S) : _root_.Set.MapsTo (fun z ↦ F (p, z)) K K := by
    intro z hz
    exact (mem_square_iff_time_mem_Icc (φ p) (hvs p) (hnz p hp) (hderiv p hp)
      (hfixed p hp) hz.2 (hexit p hp z.im hz.2) _).mpr
      ((hDmap _ (hτpos p hp z.im hz.2)).mapsTo hz.1)
  obtain ⟨R, hR, hcoords⟩ := exists_smooth_leftEdge_coordinates hv φ hφ hnz hderiv hfixed
  have hlength : ContDiffOn ℝ ∞ (fun q : P × ℂ ↦ τ (q.1, (R q).1)) Q :=
    hτ.comp (contDiffOn_fst.prodMk hR.fst)
      (fun q hq ↦ ⟨hq.1, (hcoords q.1 hq.1 q.2 hq.2.1 hq.2.2).1⟩)
  have hX : ContDiffOn ℝ ∞ (fun q : P × ℂ ↦ (D (τ (q.1, (R q).1))).symm (R q).2) Q :=
    hDi.comp (hlength.prodMk hR.snd) (fun q hq ↦
      ⟨hτpos q.1 hq.1 _ (hcoords q.1 hq.1 q.2 hq.2.1 hq.2.2).1, _root_.Set.mem_univ _⟩)
  let G : P × ℂ → ℂ := fun q ↦
    ((D (τ (q.1, (R q).1))).symm (R q).2 : ℂ) + (R q).1 • Complex.I
  have hG : ContDiffOn ℝ ∞ G Q :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hX).add (hR.fst.smul contDiffOn_const)
  have hGre (q : P × ℂ) : (G q).re = (D (τ (q.1, (R q).1))).symm (R q).2 := by
    simp [G, Complex.real_smul]
  have hGim (q : P × ℂ) : (G q).im = (R q).1 := by simp [G, Complex.real_smul]
  have hDimap (r : ℝ) (hr : 0 < r) {t : ℝ} (ht : t ∈ _root_.Set.Icc 0 r) :
      (D r).symm t ∈ _root_.Set.Icc (0 : ℝ) 1 := by
    obtain ⟨s, hs, he⟩ := (hDmap r hr).surjOn ht
    rw [← he, (D r).symm_apply_apply]
    exact hs
  refine ⟨G, hF, hG, fun p hp ↦ ⟨hFmap p hp, ?_, ?_, ?_⟩⟩
  · intro z hz
    have hc := hcoords p hp z hz.1 hz.2
    have ht : (R (p, z)).2 ∈ _root_.Set.Icc 0 (τ (p, (R (p, z)).1)) :=
      (mem_square_iff_time_mem_Icc (φ p) (hvs p) (hnz p hp) (hderiv p hp)
        (hfixed p hp) hc.1 (hexit p hp _ hc.1) _).mp (hc.2.2.1.symm ▸ hz)
    change (G (p, z)).re ∈ _root_.Set.Icc 0 1 ∧ (G (p, z)).im ∈ _root_.Set.Icc 0 1
    exact ⟨by rw [hGre]; exact hDimap _ (hτpos p hp _ hc.1) ht, by rw [hGim]; exact hc.1⟩
  · intro z hz
    have hFz := hFmap p hp hz
    have hRF : R (p, F (p, z)) = (z.im, D (τ (p, z.im)) z.re) :=
      ((hcoords p hp (F (p, z)) hFz.1 hFz.2).2.2.2 _ _ rfl).symm
    change G (p, F (p, z)) = z
    dsimp only [G]
    rw [hRF]
    simp only [Diffeomorph.symm_apply_apply]
    apply Complex.ext <;> simp [Complex.real_smul]
  · intro z hz
    change φ p (D (τ (p, (G (p, z)).im)) (G (p, z)).re) ((G (p, z)).im • Complex.I) = z
    rw [hGre, hGim, Diffeomorph.apply_symm_apply]
    exact (hcoords p hp z hz.1 hz.2).2.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_smooth_inverse_leftEdgeSquareMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_smooth_inverse_leftEdgeSquareMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_smooth_inverse_leftEdgeSquareMap ``Submission.DifferentialGeometry.Analysis.exists_smooth_inverse_leftEdgeSquareMap

end DifferentialGeometry.Analysis
