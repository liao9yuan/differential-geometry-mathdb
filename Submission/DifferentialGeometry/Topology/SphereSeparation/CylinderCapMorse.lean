import Submission.DifferentialGeometry.Topology.SphereSeparation.CylinderCap
import Submission.DifferentialGeometry.Topology.Morse.CylinderCapReplacement
import Submission.DifferentialGeometry.Topology.Morse.SurfaceEulerCharacteristic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.SphereSeparation

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

theorem exists_two_morse_cylinderCap_replacements_of_regular_height
    {e : SphereTwo → EuclideanThree} (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) (fun y => e y 2) x →
      IsNondegenerateCriticalPointAt (𝓡 2) (fun y => e y 2) x)
    (hinj : _root_.Set.InjOn (fun y => e y 2) (criticalPoints (𝓡 2) (fun y => e y 2)))
    {c : ℝ} (hne : ∃ x, e x 2 = c)
    (hr : ∀ x, e x 2 = c → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ x, e x 2 ∈ _root_.Set.Icc (c - ε) (c + ε) → ¬ IsCriticalPointAt (𝓡 2) (fun y => e y 2) x) ∧
      ∃ R : ℝ, 1 < R ∧ ∃ (η : AddCircle (1 : ℝ) → SphereTwo)
        (Ψ : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] EuclideanThree)
        (b : Fin 2 → ClosedCell 2 → SphereTwo) (σ : ℝ),
        (σ = 1 ∨ σ = -1) ∧ _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η ∧
        (∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ (b i)) ∧
        (∀ i, _root_.Set.range (b i ∘ cellBoundaryInclusion 2) = _root_.Set.range η) ∧
        _root_.Set.range (b 0) ∪ _root_.Set.range (b 1) = _root_.Set.univ ∧ _root_.Set.range (b 0) ∩ _root_.Set.range (b 1) = _root_.Set.range η ∧
        e '' _root_.Set.range η = Ψ '' (_root_.Metric.sphere (0 : Schoenflies.Plane) 1 ×ˢ {0}) ∧
        (∀ p, Ψ p 2 = c + p.2) ∧
        Ψ ⁻¹' _root_.Set.range e ∩ (_root_.Metric.closedBall (0 : Schoenflies.Plane) R ×ˢ _root_.Set.Icc (-ε) ε) =
          _root_.Metric.sphere (0 : Schoenflies.Plane) 1 ×ˢ _root_.Set.Icc (-ε) ε ∧
        let a : Fin 2 → ℝ := fun i => if i = 0 then σ * ε / 2 else -(σ * ε / 2)
        ∃ (χ : Fin 2 → PartialDiffeomorph (𝓡 2) (𝓡 2) Schoenflies.Plane SphereTwo ∞)
          (f : Fin 2 → SphereTwo → EuclideanThree),
          (∀ i, _root_.Metric.closedBall (0 : Schoenflies.Plane) 1 ⊆ (χ i).source ∧
            χ i '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1 = _root_.Set.range (b i) ∧
            _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (f i) ∧
            (∀ x ∈ _root_.Metric.closedBall (0 : Schoenflies.Plane) 1,
              f i (χ i x) = Ψ (EuclideanGeometry.cylinderCap (a i) x)) ∧
            _root_.Set.EqOn (f i) e (_root_.Set.range (b i))ᶜ ∧
            (∀ y ∈ _root_.Set.range (b i), f i =ᶠ[nhds y]
              (Ψ ∘ EuclideanGeometry.cylinderCap (a i)) ∘ (χ i).symm) ∧
            (∀ x, IsCriticalPointAt (𝓡 2) (fun y => f i y 2) x →
              IsNondegenerateCriticalPointAt (𝓡 2) (fun y => f i y 2) x) ∧
            _root_.Set.InjOn (fun y => f i y 2) (criticalPoints (𝓡 2) (fun y => f i y 2)) ∧
            criticalPoints (𝓡 2) (fun y => f i y 2) =
              (criticalPoints (𝓡 2) (fun y => e y 2) \ _root_.Set.range (b i)) ∪ {χ i 0} ∧
            (criticalPoints (𝓡 2) (fun y => f i y 2)).ncard +
              (criticalPoints (𝓡 2) (fun y => e y 2) ∩ _root_.Set.range (b i)).ncard =
                (criticalPoints (𝓡 2) (fun y => e y 2)).ncard + 1 ∧
            ∀ p ∈ _root_.Metric.ball (0 : Schoenflies.Plane) R ×ˢ _root_.Set.Ioo (-ε) ε,
              Ψ p ∈ e '' (_root_.Set.range (b i))ᶜ ↔
                ‖p.1‖ = 1 ∧ 0 < (if i = 0 then σ else -σ) * p.2) ∧
          (criticalPoints (𝓡 2) (fun y => f 0 y 2)).ncard +
            (criticalPoints (𝓡 2) (fun y => f 1 y 2)).ncard =
              (criticalPoints (𝓡 2) (fun y => e y 2)).ncard + 2 ∧
          {p | IsCriticalPointAt (𝓡 2) (fun y => f 0 y 2) p ∧ sigNeg (chartHessianAt
            (fun y => f 0 ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}.ncard +
            {p | IsCriticalPointAt (𝓡 2) (fun y => f 1 y 2) p ∧ sigNeg (chartHessianAt
              (fun y => f 1 ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}.ncard =
              {p | IsCriticalPointAt (𝓡 2) (fun y => e y 2) p ∧ sigNeg (chartHessianAt
                (fun y => e ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}.ncard := by
  classical
  have heh : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun y => e y 2) :=
    (EuclideanSpace.proj 2).contMDiff.comp he.contMDiff
  have hfinite := DifferentialGeometry.Morse.finite_criticalPoints_of_isCompact heh isCompact_univ
    (fun _ _ => BoundarylessManifold.isInteriorPoint) (fun _ _ => _root_.Set.mem_univ _) hnd
  let K := criticalPoints (𝓡 2) (fun y => e y 2)
  let W := ((fun y => e y 2) '' K)ᶜ
  have hW : IsOpen W := (hfinite.image (fun y => e y 2)).isClosed.isOpen_compl
  have hcW : c ∈ W := by
    rintro ⟨x, hx, hxc⟩
    exact hr x hxc hx
  obtain ⟨ε, hε, hεW, R, hR, η, Ψ, b, σ, hσ, hη, hb, hbd, hcover, hinter,
    hboundary, hheight, hsphere, χ, f, hf⟩ :=
    exists_two_cylinderCap_replacements_of_regular_height he hne hr hW hcW
  let a : Fin 2 → ℝ := fun i => if i = 0 then σ * ε / 2 else -(σ * ε / 2)
  have hazero (i : Fin 2) : a i ≠ 0 := by
    dsimp [a]
    rcases hσ with hσ | hσ <;> rw [hσ] <;> split_ifs <;> nlinarith
  have haε (i : Fin 2) : |a i| < ε := by
    dsimp [a]
    rcases hσ with hσ | hσ <;> rw [hσ] <;> split_ifs <;>
      simp only [one_mul, neg_one_mul, neg_div, neg_neg, abs_neg] <;>
      rw [abs_of_pos (by linarith : 0 < ε / 2)] <;> linarith
  have hDc (i : Fin 2) : IsClosed (_root_.Set.range (b i)) := (isCompact_range (hb i).contMDiff.continuous).isClosed
  have hregular (x : SphereTwo) (hx : e x 2 ∈ _root_.Set.Icc (c - ε) (c + ε)) :
      ¬ IsCriticalPointAt (𝓡 2) (fun y => e y 2) x := by
    intro hc
    exact hεW hx ⟨x, hc, rfl⟩
  have hvalue (i : Fin 2) : c - a i ∉ (fun y => e y 2) '' (K \ _root_.Set.range (b i)) := by
    rintro ⟨x, hx, heq⟩
    apply hregular x ?_ hx.1
    change e x 2 = c - a i at heq
    rw [heq]
    have ha := abs_lt.mp (haε i)
    constructor <;> linarith
  have hndf (i : Fin 2) : ∀ x, IsCriticalPointAt (𝓡 2) (fun y => f i y 2) x →
      IsNondegenerateCriticalPointAt (𝓡 2) (fun y => f i y 2) x := by
    intro x hx
    exact isNondegenerateCriticalPointAt_cylinderCap_replacement_of_critical (h := fun z : EuclideanThree => z 2)
      (χ i)
      (hf i).1 (hDc i) (hf i).2.1 (hf i).2.2.2.2.1 (hazero i) hheight
      (hf i).2.2.2.2.2.1 (fun y _ hy => hnd y hy) hx
  have hinjf (i : Fin 2) : _root_.Set.InjOn (fun y => f i y 2)
      (criticalPoints (𝓡 2) (fun y => f i y 2)) :=
    injOn_criticalPoints_cylinderCap_replacement (h := fun z : EuclideanThree => z 2)
      (χ i) (hf i).1 (hDc i) (hf i).2.1
      (hf i).2.2.2.2.1 (hazero i) hheight (hf i).2.2.2.2.2.1 (hinj.mono _root_.Set.sdiff_subset) (hvalue i)
  have hcrit (i : Fin 2) : criticalPoints (𝓡 2) (fun y => f i y 2) =
      (K \ _root_.Set.range (b i)) ∪ {χ i 0} :=
    criticalPoints_cylinderCap_replacement (h := fun z : EuclideanThree => z 2)
      (χ i) (hf i).1 (hDc i) (hf i).2.1
      (hf i).2.2.2.2.1 (hazero i) hheight (hf i).2.2.2.2.2.1
  have hcount (i : Fin 2) : (criticalPoints (𝓡 2) (fun y => f i y 2)).ncard +
      (K ∩ _root_.Set.range (b i)).ncard = K.ncard + 1 :=
    ncard_criticalPoints_cylinderCap_replacement (h := fun z : EuclideanThree => z 2)
      (χ i) (hf i).1 (hDc i) (hf i).2.1
      (hf i).2.2.2.2.1 (hazero i) hheight (hf i).2.2.2.2.2.1 hfinite
  have hlevel (y : SphereTwo) (hy : y ∈ _root_.Set.range η) : e y 2 = c := by
    obtain ⟨p, hp, heq⟩ := hboundary.subset (_root_.Set.mem_image_of_mem e hy)
    have hpzero : p.2 = 0 := hp.2
    rw [← heq, hheight, hpzero, add_zero]
  have hdisj : Disjoint (K ∩ _root_.Set.range (b 0)) (K ∩ _root_.Set.range (b 1)) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hr x (hlevel x (hinter.subset ⟨hx.2, hy.2⟩)) hx.1
  have hunion : (K ∩ _root_.Set.range (b 0)) ∪ (K ∩ _root_.Set.range (b 1)) = K := by
    rw [← _root_.Set.inter_union_distrib_left, hcover, _root_.Set.inter_univ]
  have hpartition : (K ∩ _root_.Set.range (b 0)).ncard + (K ∩ _root_.Set.range (b 1)).ncard = K.ncard := by
    rw [← _root_.Set.ncard_union_eq hdisj (hfinite.inter_of_left _) (hfinite.inter_of_left _), hunion]
  refine ⟨ε, hε, hregular, R, hR, η, Ψ, b, σ, hσ, hη, hb, hbd, hcover, hinter,
    hboundary, hheight, hsphere, χ, f, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hf i).1, (hf i).2.1, (hf i).2.2.1, (hf i).2.2.2.1,
      (hf i).2.2.2.2.1, (hf i).2.2.2.2.2.1, hndf i, hinjf i, hcrit i, hcount i, (hf i).2.2.2.2.2.2⟩
  · have h₀ := hcount 0
    have h₁ := hcount 1
    dsimp only [K, criticalPoints] at h₀ h₁ hpartition ⊢
    omega
  · let S (g : SphereTwo → EuclideanThree) : Set SphereTwo :=
      {p | IsCriticalPointAt (𝓡 2) (fun y => g y 2) p ∧ sigNeg (chartHessianAt
        (fun y => g ((extChartAt (𝓡 2) p).symm y) 2) (extChartAt (𝓡 2) p p)) = 1}
    change (S (f 0)).ncard + (S (f 1)).ncard = (S e).ncard
    have heuler := ncard_criticalPoints_sphere_two heh hnd hinj
    change (criticalPoints (𝓡 2) (fun y => e y 2)).ncard = 2 + 2 * (S e).ncard at heuler
    have hfh (i : Fin 2) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun y => f i y 2) :=
      (EuclideanSpace.proj 2).contMDiff.comp (hf i).2.2.1.contMDiff
    have heulerf (i : Fin 2) := ncard_criticalPoints_sphere_two (hfh i) (hndf i) (hinjf i)
    have h₀ := hcount 0
    have h₁ := hcount 1
    have heuler₀ := heulerf 0
    have heuler₁ := heulerf 1
    change (criticalPoints (𝓡 2) (fun y => f 0 y 2)).ncard =
      2 + 2 * (S (f 0)).ncard at heuler₀
    change (criticalPoints (𝓡 2) (fun y => f 1 y 2)).ncard =
      2 + 2 * (S (f 1)).ncard at heuler₁
    dsimp only [K, criticalPoints] at h₀ h₁ hpartition heuler heuler₀ heuler₁
    omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_two_morse_cylinderCap_replacements_of_regular_height then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_two_morse_cylinderCap_replacements_of_regular_height"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_two_morse_cylinderCap_replacements_of_regular_height ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_two_morse_cylinderCap_replacements_of_regular_height

end DifferentialGeometry.Topology.SphereSeparation
