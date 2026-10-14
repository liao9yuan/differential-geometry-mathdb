import Mathlib.Topology.Sequences

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

open _root_.Set _root_.Filter _root_.Topology

namespace IsCompact
open _root_.IsCompact

variable {Q : Type*} [TopologicalSpace Q] [FirstCountableTopology Q]
  {M : ℕ → Type*} {K : Set Q}

open _root_.IsCompact in
theorem eventually_injOn_of_local_injOn_of_collision_limits
    (hK : IsCompact K) (F : ∀ n, Q → M n)
    (hlocal : ∀ x ∈ K, ∃ U ∈ nhds x, ∀ᶠ n in _root_.Filter.atTop, _root_.Set.InjOn (F n) U)
    (hcollision : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∀ (x y : ℕ → Q), (∀ n, x n ∈ K) → (∀ n, y n ∈ K) →
      ∀ a ∈ K, ∀ b ∈ K,
        _root_.Filter.Tendsto x _root_.Filter.atTop (nhds a) → _root_.Filter.Tendsto y _root_.Filter.atTop (nhds b) →
        (∀ n, F (φ n) (x n) = F (φ n) (y n)) → a = b) :
    ∀ᶠ n in _root_.Filter.atTop, _root_.Set.InjOn (F n) K := by
  classical
  by_contra h
  obtain ⟨φ, hφ, hbad⟩ := _root_.Filter.extraction_of_frequently_atTop (not_eventually.mp h)
  have hex : ∀ n, ∃ x ∈ K, ∃ y ∈ K, F (φ n) x = F (φ n) y ∧ x ≠ y := by
    intro n
    have hn := hbad n
    simp only [_root_.Set.InjOn, _root_.Classical.not_forall] at hn
    obtain ⟨x, hx, y, hy, heq, hne⟩ := hn
    exact ⟨x, hx, y, hy, heq, hne⟩
  choose x hx y hy heq hne using hex
  obtain ⟨p, hp, ψ, hψ, hpconv⟩ :=
    (hK.prod hK).tendsto_subseq (fun n => show (x n, y n) ∈ K ×ˢ K from ⟨hx n, hy n⟩)
  have hxconv : _root_.Filter.Tendsto (x ∘ ψ) _root_.Filter.atTop (nhds p.1) := by
    exact (continuous_fst.tendsto p).comp hpconv
  have hyconv : _root_.Filter.Tendsto (y ∘ ψ) _root_.Filter.atTop (nhds p.2) := by
    exact (continuous_snd.tendsto p).comp hpconv
  have hpEq := hcollision (φ ∘ ψ) (hφ.comp hψ) (x ∘ ψ) (y ∘ ψ)
    (fun n => hx (ψ n)) (fun n => hy (ψ n)) p.1 hp.1 p.2 hp.2 hxconv hyconv
    (fun n => heq (ψ n))
  rw [← hpEq] at hyconv
  obtain ⟨U, hU, hinj⟩ := hlocal p.1 hp.1
  have htail := ((hφ.comp hψ).tendsto_atTop.eventually hinj).and
    ((hxconv.eventually hU).and (hyconv.eventually hU))
  obtain ⟨n, hn⟩ := htail.exists
  exact hne (ψ n) (hn.1 hn.2.1 hn.2.2 (heq (ψ n)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCompact.eventually_injOn_of_local_injOn_of_collision_limits then
    throwError "Refusing to shadow existing declaration IsCompact.eventually_injOn_of_local_injOn_of_collision_limits"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCompact.eventually_injOn_of_local_injOn_of_collision_limits ``Submission.IsCompact.eventually_injOn_of_local_injOn_of_collision_limits

end IsCompact

end
