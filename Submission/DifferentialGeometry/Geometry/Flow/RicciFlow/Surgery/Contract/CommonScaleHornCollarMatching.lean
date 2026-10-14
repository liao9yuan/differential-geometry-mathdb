import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornNeckCollarMatching
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornScalarLevel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Submission.Function _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry.Topology.Manifold

universe u

theorem exists_common_scale_horn_collar_matching_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ {δ : ℝ}, 0 < δ → δ⁻¹+1 < ε⁻¹ →
        ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ Q : ℝ, Q₀ < Q → ∀ y : Sphere 2,
          ∃ (t δ₀ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
            (N : ∀ c e, NormalizedNeck D.terminal.metric (δ₀ c e) (k c e)),
            ∀ c e, 0 < t c e ∧ (N c e).center = P.horn c e (y,t c e) ∧
              (N c e).scale = Q ∧ δ₀ c e ≤ ε ∧ ⌊ε⁻¹⌋₊+1 ≤ k c e ∧
              ∃ (a : ℝ) (β : Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2) (σ : ℝ),
                (P.hornCollar c e).radius+δ⁻¹ < a ∧
                (β = Diffeomorph.refl (𝓡 2) (Sphere 2) ∞ ∨ β = sphereAntipodalDiffeomorph (n := 2)) ∧
                (σ = 1 ∨ σ = -1) ∧
                ∃ F : NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder,
                  (∀ (q : Sphere 2) (s : ℝ), |s| ≤ δ⁻¹ →
                    ∃ hq : (β q,σ*s) ∈ neckBuffer (δ₀ c e),
                      0 < (F (q,a+s)).2 ∧
                      P.horn c e (F (q,a+s)) = (N c e).chart ⟨(β q,σ*s),hq⟩) ∧
                  ∃ K : Set NeckCylinder, IsCompact K ∧
                    K ⊆ _root_.Set.univ ×ˢ _root_.Set.Ioi (P.hornCollar c e).radius ∧
                    EqOn F id Kᶜ ∧ _root_.Set.EqOn F.symm id Kᶜ := by
  obtain ⟨eta,heta,hmatch⟩ := exists_deep_horn_neck_collar_matching_tolerance
  refine ⟨eta,heta,?_⟩
  intro D ε Λ P hε δ hδpos hfit
  classical
  have hc (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c) : c ∈ P.component := by
    by_contra hn
    exact (P.hornIndex_empty c hn).false e
  choose a C ha _ hC using fun c e =>
    hmatch P hε c (hc c e) e (P.hornCollar c e).radius hδpos
  let J := Σ c : P.component,P.hornIndex c.val
  let : Finite P.component := P.component_finite.to_subtype
  let (c : P.component) : Finite (P.hornIndex c.val) := P.hornIndex_finite c.val
  have : Finite J := inferInstance
  obtain ⟨B,hB⟩ := (_root_.Set.finite_range (fun j : J => C j.1.val j.2)).bddAbove
  let Q₀ := _root_.Max.max (_root_.Max.max B (Λ*(P.coreRadius^2)⁻¹)) 0+1
  refine ⟨Q₀,by dsimp only [Q₀]; positivity,?_⟩
  intro Q hQ y
  have hQbase : Λ*(P.coreRadius^2)⁻¹ < Q := by
    have h₁ := le_max_right B (Λ*(P.coreRadius^2)⁻¹)
    have h₂ := le_max_left (_root_.Max.max B (Λ*(P.coreRadius^2)⁻¹)) 0
    dsimp only [Q₀] at hQ
    linarith
  obtain ⟨t,δ₀,k,N,hN⟩ := P.exists_neck_family_scale_eq y hQbase
  refine ⟨t,δ₀,k,N,?_⟩
  intro c e
  obtain ⟨ht,hcenter,hscale,hδε,hk⟩ := hN c e
  have hCQ : C c e < (N c e).scale := by
    have hCB := hB (_root_.Set.mem_range_self (⟨⟨c,hc c e⟩,e⟩ : J))
    have h₁ := le_max_left B (Λ*(P.coreRadius^2)⁻¹)
    have h₂ := le_max_left (_root_.Max.max B (Λ*(P.coreRadius^2)⁻¹)) 0
    rw [hscale]
    dsimp only [Q₀] at hQ
    change C c e ≤ B at hCB
    linarith
  have hcenter' : (N c e).center ∈ TerminalCorePresentation.hornHalfRange P c e := by
    rw [hcenter]
    exact ⟨⟨(y,t c e),ht.le⟩,rfl⟩
  have hfit₀ : δ⁻¹+1 < (δ₀ c e)⁻¹ := hfit.trans_le (inv_anti₀ (N c e).delta_pos hδε)
  obtain ⟨β,σ,hβ,hσ,F,hF,K,hK,hKρ,hfix,hfixi⟩ :=
    hC c e (N c e) hδε hk hcenter' hCQ hfit₀
  exact ⟨ht,hcenter,hscale,hδε,hk,a c e,β,σ,ha c e,hβ,hσ,F,hF,K,hK,hKρ,hfix,hfixi⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_common_scale_horn_collar_matching_tolerance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_common_scale_horn_collar_matching_tolerance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_common_scale_horn_collar_matching_tolerance ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_common_scale_horn_collar_matching_tolerance

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
