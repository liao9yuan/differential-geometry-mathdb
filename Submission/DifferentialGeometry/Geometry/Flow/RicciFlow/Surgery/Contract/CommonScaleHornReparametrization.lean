import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.CommonScaleHornCollarMatching
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornReparametrization

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

theorem exists_common_scale_reparametrized_horn_necks_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ {δ : ℝ}, 0 < δ → δ⁻¹+1 < ε⁻¹ →
        ∃ Q₀ : ℝ, 0 < Q₀ ∧ ∀ Q : ℝ, Q₀ < Q → ∀ y : Sphere 2,
          ∃ (t δ₀ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
            (N : ∀ c e, NormalizedNeck D.terminal.metric (δ₀ c e) (k c e))
            (a : ∀ c, P.hornIndex c → ℝ)
            (β : ∀ c, P.hornIndex c → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2)
            (γ : ∀ c, P.hornIndex c → ℝ)
            (F : ∀ c, P.hornIndex c → NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
            (K : ∀ c, P.hornIndex c → Set NeckCylinder)
            (hK : ∀ c e, IsCompact (K c e))
            (hfix : ∀ c e (q : NeckCylinder), q.2 ≤ (P.hornCollar c e).radius → F c e q = q)
            (hF : ∀ c e, _root_.Set.EqOn (F c e) id (K c e)ᶜ),
            let P' := P.reparametrizeHornsOfCompactSupport F hfix K hK hF
            P'.core = P.core ∧
            ∀ c e, 0 < t c e ∧ (N c e).center = P.horn c e (y,t c e) ∧
              (N c e).scale = Q ∧ δ₀ c e ≤ ε ∧ ⌊ε⁻¹⌋₊+1 ≤ k c e ∧
              (P.hornCollar c e).radius+δ⁻¹ < a c e ∧
              (β c e = Diffeomorph.refl (𝓡 2) (Sphere 2) ∞ ∨ β c e = sphereAntipodalDiffeomorph (n := 2)) ∧
              (γ c e = 1 ∨ γ c e = -1) ∧
              (_root_.Set.range (fun q : HalfNeckCylinder => P'.horn c e q.val) =
                _root_.Set.range (fun q : HalfNeckCylinder => P.horn c e q.val)) ∧
              ∀ (q : Sphere 2) (s : ℝ), |s| ≤ δ⁻¹ →
                ∃ hq : (β c e q,γ c e*s) ∈ neckBuffer (δ₀ c e),
                  P'.horn c e (q,a c e-s) = (N c e).chart ⟨(β c e q,γ c e*s),hq⟩ := by
  obtain ⟨eta,heta,hmatch⟩ := exists_common_scale_horn_collar_matching_tolerance
  refine ⟨eta,heta,?_⟩
  intro D ε Λ P hε δ hδpos hfit
  obtain ⟨Q₀,hQ₀,hQ⟩ := hmatch P hε hδpos hfit
  refine ⟨Q₀,hQ₀,?_⟩
  intro Q hQlt y
  obtain ⟨t,δ₀,k,N,hN⟩ := hQ Q hQlt y
  classical
  choose a β σ ha hβ hσ F hchart K hK hKρ hfix hfixi using fun c e => (hN c e).2.2.2.2.2
  let γ : ∀ c, P.hornIndex c → ℝ := fun c e => -(σ c e)
  have hfixed (c) (e : P.hornIndex c) (q : NeckCylinder)
      (hq : q.2 ≤ (P.hornCollar c e).radius) : F c e q = q :=
    hfix c e (fun hqK => (not_lt_of_ge hq) (hKρ c e hqK).2)
  refine ⟨t,δ₀,k,N,a,β,γ,F,K,hK,hfixed,hfix,rfl,?_⟩
  intro c e
  obtain ⟨ht,hcenter,hscale,hδε,hk,hrest⟩ := hN c e
  refine ⟨ht,hcenter,hscale,hδε,hk,ha c e,hβ c e,?_,
    P.reparametrizeHornsOfCompactSupport_range F hfixed K hK hfix c e,?_⟩
  · rcases hσ c e with h | h
    · exact Or.inr (congrArg Neg.neg h)
    · exact Or.inl (by dsimp only [γ]; rw [h]; norm_num)
  · intro q s hs
    obtain ⟨hq,hpos,heq⟩ := hchart c e q (-s) (by simpa only [abs_neg] using hs)
    have hsign : σ c e*(-s) = γ c e*s := by dsimp only [γ]; ring
    have hq' : (β c e q,γ c e*s) ∈ neckBuffer (δ₀ c e) := hsign ▸ hq
    refine ⟨hq',?_⟩
    change P.horn c e (F c e (q,a c e-s)) = _
    have hsub : (⟨(β c e q,σ c e*(-s)),hq⟩ : neckBuffer (δ₀ c e)) =
        ⟨(β c e q,γ c e*s),hq'⟩ := Subtype.ext (Prod.ext rfl hsign)
    simpa only [sub_eq_add_neg] using heq.trans (congrArg (N c e).chart hsub)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_common_scale_reparametrized_horn_necks_tolerance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_common_scale_reparametrized_horn_necks_tolerance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_common_scale_reparametrized_horn_necks_tolerance ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_common_scale_reparametrized_horn_necks_tolerance

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
