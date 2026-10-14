import Submission.DifferentialGeometry.Topology.SphereSeparation.HeightCapIsotopy
import Submission.DifferentialGeometry.Topology.PlanarJordan.QuadraticCaps
import Submission.DifferentialGeometry.Topology.Diffeomorph.IsotopyInterpolation
import Submission.DifferentialGeometry.Topology.Diffeomorph.Fiberwise

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.Topology.Morse
open _root_.Submission.DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Topology.SphereSeparation

private theorem exists_restrictFiber
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : (E × ℝ) ≃ₘ[ℝ] (E × ℝ)) (hA : ∀ z, (A z).2 = z.2) (a : ℝ) :
    ∃ L : E ≃ₘ[ℝ] E, (∀ x, L x = (A (x, a)).1) ∧
      (∀ x, L.symm x = (A.symm (x, a)).1) := by
  let A' : (E × ℝ) ≃ₘ⟮(𝓘(ℝ, E)).prod 𝓘(ℝ, ℝ), (𝓘(ℝ, E)).prod 𝓘(ℝ, ℝ)⟯ (E × ℝ) :=
    { toEquiv := A.toEquiv
      contMDiff_toFun := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact A.contMDiff
      contMDiff_invFun := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact A.symm.contMDiff }
  exact ⟨A'.restrictFiber hA a, fun _ => rfl, fun _ => rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_restrictFiber
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.exists_restrictFiber target :: scope.openDecls } }

private theorem exists_quadratic_cap_transition
    {M : Type*} (f : M → EuclideanSpace ℝ (Fin 2) × ℝ)
    (A₀ A₁ : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ))
    (hA₀ : ∀ z, (A₀ z).2 = z.2) (hA₁ : ∀ z, (A₁ z).2 = z.2)
    (D : (EuclideanSpace ℝ (Fin 2)) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2)))
    {c₀ c₁ r : ℝ} (hr : 0 < r) {K₀ K₁ : Set M}
    (hK₀ : {x | (f x).2 = c₀ + (1 : ℝ) / 2 * r ^ 2} ⊆ K₀)
    (hK₁ : {x | (f x).2 = c₁ + (-1 : ℝ) / 2 * r ^ 2} ⊆ K₁)
    (hcap₀ : f '' K₀ = (fun y => A₀ (y, c₀ + 1 / 2 * ‖y‖ ^ 2)) '' _root_.Metric.closedBall 0 r)
    (hcap₁ : f '' K₁ = (fun y => A₁ (y, c₁ + (-1) / 2 * ‖y‖ ^ 2)) '' _root_.Metric.closedBall 0 r)
    (hD : D '' ((fun x => (f x).1) '' {x | (f x).2 = c₀ + r ^ 2 / 2}) =
      (fun x => (f x).1) '' {x | (f x).2 = c₁ - r ^ 2 / 2}) :
    ∃ L U : (EuclideanSpace ℝ (Fin 2)) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2)),
      (∀ x, L x = (A₀ (x, c₀ + r ^ 2 / 2)).1) ∧
      (∀ x, U x = (A₁ (x, c₁ - r ^ 2 / 2)).1) ∧
      D '' (L '' _root_.Metric.closedBall 0 r) = U '' _root_.Metric.closedBall 0 r ∧
      (fun x => (f x).1) '' {x | (f x).2 = c₀ + r ^ 2 / 2} = L '' _root_.Metric.sphere 0 r := by
  have heqa : c₀ + (1 : ℝ) / 2 * r ^ 2 = c₀ + r ^ 2 / 2 := by ring
  have heqb : c₁ + (-1 : ℝ) / 2 * r ^ 2 = c₁ - r ^ 2 / 2 := by ring
  obtain ⟨L, hL, _⟩ := exists_restrictFiber A₀ hA₀ (c₀ + r ^ 2 / 2)
  obtain ⟨U, hU, _⟩ := exists_restrictFiber A₁ hA₁ (c₁ - r ^ 2 / 2)
  have hLfun : (L : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) =
      fun x => (A₀ (x, c₀ + r ^ 2 / 2)).1 := funext hL
  have hUfun : (U : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) =
      fun x => (A₁ (x, c₁ - r ^ 2 / 2)).1 := funext hU
  refine ⟨L, U, hL, hU, ?_, ?_⟩
  · have hball := PlanarJordan.image_closedBall_eq_of_image_quadratic_level_eq
      f A₀.toHomeomorph A₁.toHomeomorph hA₀ hA₁ D.toHomeomorph
        one_ne_zero (by norm_num : (-1 : ℝ) ≠ 0) hr hr hK₀ hK₁ hcap₀ hcap₁
        (by simpa only [heqa, heqb, Diffeomorph.coe_toHomeomorph] using hD)
    rw [hLfun, hUfun]
    simpa only [heqa, heqb, Diffeomorph.coe_toHomeomorph] using hball
  · have h := Function.image_level_eq_image_sphere_of_image_quadratic_graph_eq
      f A₀ hA₀ one_ne_zero hr.le hK₀ hcap₀
    rw [hLfun]
    simpa only [heqa] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_quadratic_cap_transition
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.exists_quadratic_cap_transition target :: scope.openDecls } }

theorem exists_height_disk_family_eqOn_extremum_neighborhoods
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
        ∃ C : (EuclideanSpace ℝ (Fin 2)) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2)),
          C '' _root_.Metric.closedBall 0 r = _root_.Metric.closedBall 0 r ∧
          ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
          (∀ x ∈ _root_.Metric.sphere 0 r, ∀ s ∈ _root_.Set.Icc (1 - δ) (1 + δ),
            C (s • x) = s • C x ∧ C.symm (s • x) = s • C.symm x) ∧
          ∃ G : ℝ → (EuclideanSpace ℝ (Fin 2)) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin 2)),
            ContDiff ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin 2) => G z.1 z.2) ∧
            ContDiff ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin 2) => (G z.1).symm z.2) ∧
            (∀ t ∈ _root_.Set.Icc (e p 2 + r ^ 2 / 2) (e q 2 - r ^ 2 / 2),
              G t '' _root_.Metric.sphere 0 r = (fun x => (EuclideanSpace.equivProdLast 2 (e x)).1) ''
                {x | e x 2 = t}) ∧
            ∃ η : ℝ, 0 < η ∧ η ≤ r ^ 2 / 8 ∧
              8 * η < (e q 2 - r ^ 2 / 2) - (e p 2 + r ^ 2 / 2) ∧
              ∃ V : Set (EuclideanSpace ℝ (Fin 2)), IsOpen V ∧ _root_.Metric.closedBall 0 r ⊆ V ∧
                (∀ t ∈ _root_.Set.Icc (e p 2 + r ^ 2 / 2 - η) (e p 2 + r ^ 2 / 2 + η), ∀ x ∈ V,
                  G t x = (A₀ (quadraticLevelScaling (e p 2 + r ^ 2 / 2) (e p 2) x t, t)).1) ∧
                (∀ t ∈ _root_.Set.Icc (e q 2 - r ^ 2 / 2 - η) (e q 2 - r ^ 2 / 2 + η), ∀ x ∈ V,
                  G t x =
                    (A₁ (quadraticLevelScaling (e q 2 - r ^ 2 / 2) (e q 2) (C x) t, t)).1) := by
  obtain ⟨r, hr, hab, A₀, A₁, hA₀, hA₁, hcap₀, hcap₁,
    Φ, hΦ, hΦinv, hΦa, hlevels, _, η, hη, hηr, hηab, R, hrR, h₀, h₁⟩ :=
      exists_height_level_isotopy_eqOn_extremum_neighborhoods he hp hq hmin hmax hpq hcrit
  let a := e p 2 + r ^ 2 / 2
  let b := e q 2 - r ^ 2 / 2
  let f := EuclideanSpace.equivProdLast (𝕜 := ℝ) 2 ∘ e
  have hfst (x : SphereTwo) : (f x).1 = (EuclideanSpace.equivProdLast 2 (e x)).1 := rfl
  have hsnd (x : SphereTwo) : (f x).2 = e x 2 := rfl
  have heqa : e p 2 + (1 : ℝ) / 2 * r ^ 2 = a := by dsimp [a]; ring
  have heqb : e q 2 + (-1 : ℝ) / 2 * r ^ 2 = b := by dsimp [b]; ring
  have hK₀ : {x | (f x).2 = e p 2 + (1 : ℝ) / 2 * r ^ 2} ⊆ {x | e x 2 ≤ a} := by
    intro x hx
    rw [_root_.Set.mem_ofPred_eq, hsnd, heqa] at hx
    exact hx.le
  have hK₁ : {x | (f x).2 = e q 2 + (-1 : ℝ) / 2 * r ^ 2} ⊆ {x | b ≤ e x 2} := by
    intro x hx
    rw [_root_.Set.mem_ofPred_eq, hsnd, heqb] at hx
    exact hx.ge
  obtain ⟨L, U, hL, hU, hball', hlevela'⟩ :=
    exists_quadratic_cap_transition f A₀ A₁ hA₀ hA₁ (Φ b) hr hK₀ hK₁ hcap₀ hcap₁
      (by simpa only [hfst, hsnd] using hlevels b ⟨hab.le, le_rfl⟩)
  have hlevela : (fun x => (f x).1) '' {x | e x 2 = a} = L '' _root_.Metric.sphere 0 r := by
    simpa only [hsnd] using hlevela'
  obtain ⟨C, hC, δ, hδ, hδhalf, hrad, G, hG, hGi, hGa, hGb, hGS, _⟩ :=
    Diffeomorph.exists_contDiff_family_eqOn_sphere_radial_collar Φ L U hΦ hΦinv
      (a := a + 2 * η) (b := b - 2 * η) (c := b)
      (by dsimp [a, b]; linarith) hr hball'
  have hradial : ∀ x ∈ _root_.Metric.sphere 0 r, ∀ s ∈ _root_.Set.Icc (1 - δ) (1 + δ),
      C (s • x) = s • C x ∧ C.symm (s • x) = s • C.symm x := by
    intro x hx s hs
    have heq := hrad x hx 1 ⟨by linarith, by linarith⟩
    simp only [one_smul] at heq
    exact ⟨(hrad x hx s hs).1.trans (congrArg (s • ·) heq.1.symm),
      (hrad x hx s hs).2.trans (congrArg (s • ·) heq.2.symm)⟩
  let V : Set (EuclideanSpace ℝ (Fin 2)) := _root_.Metric.ball 0 R ∩ C ⁻¹' _root_.Metric.ball 0 R
  have hV : IsOpen V := isOpen_ball.inter (isOpen_ball.preimage C.continuous)
  have hsub : _root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r ⊆ _root_.Metric.ball 0 R :=
    _root_.Metric.closedBall_subset_ball hrR
  have hmap : _root_.Set.MapsTo C (_root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r) (_root_.Metric.closedBall 0 r) :=
    fun x hx => hC.subset (_root_.Set.mem_image_of_mem C hx)
  have hCV : _root_.Set.MapsTo C (_root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r) (_root_.Metric.ball 0 R) :=
    fun x hx => hsub (hmap hx)
  have hVsub : _root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r ⊆ V := _root_.Set.subset_inter hsub hCV
  refine ⟨r, hr, hab, A₀, A₁, hA₀, hA₁, hcap₀, hcap₁,
    C, hC, δ, hδ, hδhalf, hradial, G, hG, hGi, ?_,
    η, hη, hηr, hηab, V, hV, hVsub, ?_, ?_⟩
  · intro t ht
    calc
      G t '' _root_.Metric.sphere 0 r = (fun x => Φ t (L x)) '' _root_.Metric.sphere 0 r := (hGS t).image_eq
      _ = Φ t '' (L '' _root_.Metric.sphere 0 r) := (_root_.Set.image_image ..).symm
      _ = (fun x => (EuclideanSpace.equivProdLast 2 (e x)).1) '' {x | e x 2 = t} := by
        rw [← hlevela]
        exact hlevels t ht
  · intro t ht x hx
    rw [hGa t (by dsimp [a]; linarith [ht.2]) x, hL]
    exact h₀ t ht x (_root_.Metric.ball_subset_closedBall hx.1)
  · intro t ht x hx
    rw [hGb t (by dsimp [b]; linarith [ht.1]) x, hU]
    exact h₁ t ht (C x) (_root_.Metric.ball_subset_closedBall hx.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_height_disk_family_eqOn_extremum_neighborhoods then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_height_disk_family_eqOn_extremum_neighborhoods"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_height_disk_family_eqOn_extremum_neighborhoods ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_height_disk_family_eqOn_extremum_neighborhoods

end DifferentialGeometry.Topology.SphereSeparation
