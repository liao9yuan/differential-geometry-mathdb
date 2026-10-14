/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Pasting
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Product
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPath

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem exists_capMap_of_centeredPrism {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {prism : (Fin 3 → ℝ) × ℝ → M}
    {b : EuclideanSpace ℝ (Fin 2) → (Fin 3 → ℝ)} {E A : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)} {s h₀ σ : ℝ}
    (hE : IsPLBall 2 E) (hs : 0 < s) (hρ : IsPLHomeomorphOn ρ (frontier E ×ˢ _root_.Set.Icc (-s) 0) A)
    (hρ0 : ∀ x ∈ frontier E, ρ (x, 0) = x) (hAE : A ∩ E = frontier E) (hh₀ : 0 < h₀)
    (hh₀1 : h₀ ≤ 1) (hσ : σ = 1 ∨ σ = -1)
    (hinj : _root_.Set.InjOn prism (stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (-1 : ℝ) 1))
    (hb : _root_.Set.MapsTo b (E ∪ A) (stdSimplex ℝ (Fin 3))) (hbpa : IsPiecewiseAffineOn b (E ∪ A))
    (hbinj : _root_.Set.InjOn b (E ∪ A))
    (hpl : ∀ (G : EuclideanSpace ℝ (Fin 2) → (Fin 3 → ℝ) × ℝ)
      (S : Set (EuclideanSpace ℝ (Fin 2))), IsPiecewiseAffineOn G S →
        _root_.Set.MapsTo G S (stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (-1 : ℝ) 1) → IsPLOn 2 3 (prism ∘ G) S) :
    ∃ F : EuclideanSpace ℝ (Fin 2) → M, IsPLOn 2 3 F (E ∪ A) ∧ _root_.Set.InjOn F (E ∪ A) ∧
      (∀ x ∈ ρ '' (frontier E ×ˢ {-s}), F x = prism (b x, 0)) ∧
        ∀ x ∈ E ∪ A, ∃ t ∈ _root_.Set.Icc (0 : ℝ) h₀, F x = prism (b x, σ * t) ∧
          (x ∉ ρ '' (frontier E ×ˢ {-s}) → 0 < t) := by
  classical
  set T := frontier E with hTdef
  have hTpoly : IsPolyhedron T := hE.isPLSphere_frontier.isPolyhedron
  have hEclosed : IsClosed E := hE.isPolyhedron.isCompact.isClosed
  have hρinj : ∀ t ∈ T, ∀ u ∈ _root_.Set.Icc (-s) 0, ∀ t' ∈ T, ∀ u' ∈ _root_.Set.Icc (-s) 0,
      ρ (t, u) = ρ (t', u') → t = t' ∧ u = u' := by
    intro t ht u hu t' ht' u' hu' h
    have h' := hρ.bijOn.injOn ⟨ht, hu⟩ ⟨ht', hu'⟩ h
    exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  have hρinv : ∀ t ∈ T, ∀ u ∈ _root_.Set.Icc (-s) 0,
      Function.invFunOn ρ (T ×ˢ _root_.Set.Icc (-s) 0) (ρ (t, u)) = (t, u) :=
    fun t ht u hu => hρ.bijOn.injOn.leftInvOn_invFunOn ⟨ht, hu⟩
  have hpiece : ∀ a c : ℝ, -s ≤ a → c ≤ 0 → IsPolyhedron (ρ '' (T ×ˢ _root_.Set.Icc a c)) := by
    intro a c ha hc
    have hpoly : IsPolyhedron (T ×ˢ _root_.Set.Icc a c) := hTpoly.prod isHPolytope_Icc.isPolyhedron
    have hsub : T ×ˢ _root_.Set.Icc a c ⊆ T ×ˢ _root_.Set.Icc (-s) 0 := _root_.Set.prod_mono Subset.rfl (_root_.Set.Icc_subset_Icc ha hc)
    exact hpoly.image_of_isPiecewiseAffineOn
      (hρ.isPiecewiseAffineOn.mono_of_isPolyhedron hpoly hsub) (hρ.bijOn.injOn.mono hsub)
  have hs2 : -s ≤ -(s / 2) := by linarith
  have hs2' : -(s / 2) ≤ 0 := by linarith
  set A₁ := ρ '' (T ×ˢ _root_.Set.Icc (-(s / 2)) 0) with hA₁def
  set A₂ := ρ '' (T ×ˢ _root_.Set.Icc (-s) (-(s / 2))) with hA₂def
  have hA : A = A₁ ∪ A₂ := by
    rw [← hρ.image_eq, hA₁def, hA₂def, ← _root_.Set.image_union, ← _root_.Set.prod_union, _root_.Set.union_comm,
      _root_.Set.Icc_union_Icc_eq_Icc hs2 hs2']
  have hEA : E ∪ A = E ∪ A₁ ∪ A₂ := by rw [hA, _root_.Set.union_assoc]
  have hA₁poly : IsPolyhedron A₁ := hpiece _ _ hs2 le_rfl
  have hA₂poly : IsPolyhedron A₂ := hpiece _ _ le_rfl hs2'
  have hP₁poly : IsPolyhedron (E ∪ A₁) := hE.isPolyhedron.union hA₁poly
  have hA₂A : A₂ ⊆ A := by rw [hA]; exact _root_.Set.subset_union_right
  have hA₁A : A₁ ⊆ A := by rw [hA]; exact _root_.Set.subset_union_left
  have hAT : ∀ x ∈ A, ∃ t ∈ T, ∃ u ∈ _root_.Set.Icc (-s) 0, ρ (t, u) = x := by
    intro x hx
    obtain ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩ := hρ.bijOn.surjOn hx
    exact ⟨t, ht, u, hu, rfl⟩
  have hEρ : ∀ t ∈ T, ∀ u ∈ _root_.Set.Icc (-s) 0, ρ (t, u) ∈ E → u = 0 := by
    intro t ht u hu hmem
    have hT' : ρ (t, u) ∈ T := by
      rw [← hAE]
      exact ⟨hρ.bijOn.mapsTo ⟨ht, hu⟩, hmem⟩
    have h := hρinj (ρ (t, u)) hT' 0 ⟨by linarith, le_rfl⟩ t ht u hu (hρ0 _ hT')
    exact h.2.symm
  set g : EuclideanSpace ℝ (Fin 2) → ℝ := fun x =>
    h₀ * 2 / s * (Function.invFunOn ρ (T ×ˢ _root_.Set.Icc (-s) 0) x).2 + 2 * h₀ with hgdef
  have hgpa : IsPiecewiseAffineOn g A₂ := by
    have hinv := hρ.isPiecewiseAffineOn_invFunOn.mono_of_isPolyhedron hA₂poly hA₂A
    exact (hinv.affine_comp (LinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).toAffineMap).affine_comp
      ((h₀ * 2 / s) • AffineMap.id ℝ ℝ + AffineMap.const ℝ ℝ (2 * h₀))
  have hgval : ∀ t ∈ T, ∀ u ∈ _root_.Set.Icc (-s) 0, g (ρ (t, u)) = 2 * h₀ * (u + s) / s := by
    intro t ht u hu
    rw [hgdef]
    simp only
    rw [hρinv t ht u hu, eq_div_iff hs.ne']
    calc (h₀ * 2 / s * u + 2 * h₀) * s = h₀ * 2 / s * s * u + 2 * h₀ * s := by ring
      _ = h₀ * 2 * u + 2 * h₀ * s := by rw [div_mul_cancel₀ _ hs.ne']
      _ = 2 * h₀ * (u + s) := by ring
  have hconst : IsPiecewiseAffineOn (fun _ : EuclideanSpace ℝ (Fin 2) => h₀) (E ∪ A₁) :=
    ((isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (EuclideanSpace ℝ (Fin 2)) h₀)
      isOpen_univ).mono_of_isPolyhedron hP₁poly (_root_.Set.subset_univ _)).congr fun _ _ => rfl
  have hagree : _root_.Set.EqOn (fun _ : EuclideanSpace ℝ (Fin 2) => h₀) g ((E ∪ A₁) ∩ A₂) := by
    rintro x ⟨hx₁, ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩⟩
    have hu' : u ∈ _root_.Set.Icc (-s) 0 := ⟨hu.1, by linarith [hu.2]⟩
    rcases hx₁ with hxE | ⟨⟨t', u'⟩, ⟨ht', hu'₁⟩, hxt⟩
    · have := hEρ t ht u hu' hxE
      linarith [hu.2]
    · have h := hρinj t' ht' u' ⟨by linarith [hu'₁.1], hu'₁.2⟩ t ht u hu' hxt
      have hu2 : u = -(s / 2) := by linarith [hu'₁.1, hu.2, h.2]
      change h₀ = g (ρ (t, u))
      rw [hgval t ht u hu', hu2, eq_div_iff hs.ne']
      ring
  obtain ⟨ℓ, hℓpa, hℓ₁, hℓ₂⟩ : ∃ ℓ : EuclideanSpace ℝ (Fin 2) → ℝ,
      IsPiecewiseAffineOn ℓ (E ∪ A₁ ∪ A₂) ∧ _root_.Set.EqOn ℓ (fun _ => h₀) (E ∪ A₁) ∧ _root_.Set.EqOn ℓ g A₂ := by
    refine ⟨_, hconst.piecewise_of_isClosed hgpa hP₁poly.isClosed hA₂poly.isClosed hagree,
      fun x hx => if_pos hx, fun x hx => ?_⟩
    by_cases hx₁ : x ∈ E ∪ A₁
    · exact (if_pos hx₁).trans (hagree ⟨hx₁, hx⟩)
    · exact if_neg hx₁
  have hℓrange : ∀ x ∈ E ∪ A₁ ∪ A₂, 0 ≤ ℓ x ∧ ℓ x ≤ h₀ := by
    rintro x (hx | hx)
    · rw [hℓ₁ hx]
      exact ⟨hh₀.le, le_rfl⟩
    · obtain ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩ := hx
      rw [hℓ₂ ⟨(t, u), ⟨ht, hu⟩, rfl⟩, hgval t ht u ⟨hu.1, by linarith [hu.2]⟩]
      constructor
      · exact div_nonneg (mul_nonneg (by linarith) (by linarith [hu.1])) hs.le
      · rw [div_le_iff₀ hs]
        nlinarith [mul_nonneg hh₀.le (show 0 ≤ -(2 * u + s) by linarith [hu.2])]
  have hℓzero : ∀ x ∈ E ∪ A₁ ∪ A₂, ℓ x = 0 → x ∈ ρ '' (T ×ˢ {-s}) := by
    rintro x (hx | hx) h0
    · rw [hℓ₁ hx] at h0
      exact absurd h0 hh₀.ne'
    · obtain ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩ := hx
      rw [hℓ₂ ⟨(t, u), ⟨ht, hu⟩, rfl⟩, hgval t ht u ⟨hu.1, by linarith [hu.2]⟩] at h0
      have hus : u + s = 0 := by
        rcases mul_eq_zero.mp ((div_eq_zero_iff.mp h0).resolve_right hs.ne') with h | h
        · exact absurd h (mul_pos two_pos hh₀).ne'
        · exact h
      exact ⟨(t, u), ⟨ht, show u = -s by linarith⟩, rfl⟩
  have hℓbd : ∀ x ∈ ρ '' (T ×ˢ {-s}), ℓ x = 0 := by
    rintro _ ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
    have hu' : u = -s := hu
    have hmem : ρ (t, u) ∈ A₂ :=
      ⟨(t, u), ⟨ht, le_of_eq (by rw [hu']), by rw [hu']; exact hs2⟩, rfl⟩
    rw [hℓ₂ hmem, hgval t ht u ⟨le_of_eq (by rw [hu']), by linarith⟩, hu']
    simp
  set G : EuclideanSpace ℝ (Fin 2) → (Fin 3 → ℝ) × ℝ := fun x => (b x, σ * ℓ x) with hGdef
  have hGpa : IsPiecewiseAffineOn G (E ∪ A) := by
    rw [hEA] at hbpa ⊢
    exact (hbpa.prod_mk (hℓpa.affine_comp (σ • AffineMap.id ℝ ℝ))).congr fun x _ => by
      simp [hGdef]
  have hGmaps : _root_.Set.MapsTo G (E ∪ A) (stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (-1 : ℝ) 1) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hℓrange x (hEA ▸ hx)
    have hσℓ : σ * ℓ x ∈ _root_.Set.Icc (-1 : ℝ) 1 := by
      rcases hσ with h | h <;> rw [h] <;> constructor <;> linarith
    exact ⟨hb hx, hσℓ⟩
  refine ⟨prism ∘ G, hpl G (E ∪ A) hGpa hGmaps, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hbinj hx hy (congrArg Prod.fst (hinj (hGmaps hx) (hGmaps hy) hxy))
  · intro x hx
    change prism (b x, σ * ℓ x) = prism (b x, 0)
    rw [hℓbd x hx, _root_.MulZeroClass.mul_zero]
  · intro x hx
    obtain ⟨h1, h2⟩ := hℓrange x (hEA ▸ hx)
    exact ⟨ℓ x, ⟨h1, h2⟩, rfl, fun hxb =>
      lt_of_le_of_ne h1 fun h0 => hxb (hℓzero x (hEA ▸ hx) h0.symm)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_capMap_of_centeredPrism then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_capMap_of_centeredPrism"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_capMap_of_centeredPrism ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_capMap_of_centeredPrism

end DifferentialGeometry.Topology.PiecewiseLinear
