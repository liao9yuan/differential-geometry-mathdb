import Submission.DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import Submission.DifferentialGeometry.Topology.Manifold.Quotient
import Mathlib.Algebra.Ring.Periodic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace AddCircle
open _root_.AddCircle

open _root_.AddCircle in
theorem contMDiff_periodic_lift {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hper : Function.Periodic β 1) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ hper.lift := by
  apply AddCircle.isLocalDiffeomorph_coe.contMDiff_of_comp_of_surjective
    QuotientAddGroup.mk_surjective
  · change ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ β
    exact hβ.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.contMDiff_periodic_lift then
    throwError "Refusing to shadow existing declaration AddCircle.contMDiff_periodic_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.contMDiff_periodic_lift ``Submission.AddCircle.contMDiff_periodic_lift

end AddCircle

namespace AddCircle
open _root_.AddCircle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {K : Type*} [TopologicalSpace K] [ChartedSpace H K]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

open _root_.AddCircle in
theorem contMDiffOn_of_comp_coe {U : Set K} {f : K × AddCircle (1 : ℝ) → N}
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) J ∞
      (fun p : K × ℝ => f (p.1, (p.2 : AddCircle (1 : ℝ)))) (U ×ˢ _root_.Set.univ)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) J ∞ f (U ×ˢ _root_.Set.univ) := by
  rintro ⟨k, z⟩ hz
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  let hloc := isLocalDiffeomorph_coe x
  let ψ : K × AddCircle (1 : ℝ) → K × ℝ := fun p => (p.1, hloc.localInverse p.2)
  let g : K × ℝ → N := fun p => f (p.1, (p.2 : AddCircle (1 : ℝ)))
  have hleft : hloc.localInverse (x : AddCircle (1 : ℝ)) = x :=
    hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hmap : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞ ψ
      (k, (x : AddCircle (1 : ℝ))) :=
    contMDiffAt_fst.prodMk (hloc.localInverse_contMDiffAt.comp
      (k, (x : AddCircle (1 : ℝ))) contMDiffAt_snd)
  have hg : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) J ∞ g (U ×ˢ _root_.Set.univ)
      (ψ (k, (x : AddCircle (1 : ℝ)))) := hf _ ⟨hz.1, _root_.Set.mem_univ _⟩
  have hcomp : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) J ∞ (g ∘ ψ)
      (U ×ˢ _root_.Set.univ) (k, (x : AddCircle (1 : ℝ))) :=
    hg.comp (k, (x : AddCircle (1 : ℝ))) hmap.contMDiffWithinAt
      (show _root_.Set.MapsTo ψ (U ×ˢ _root_.Set.univ) (U ×ˢ _root_.Set.univ) from fun p hp => ⟨hp.1, _root_.Set.mem_univ _⟩)
  apply hcomp.congr_of_eventuallyEq
  · apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (hloc.localInverse_open_source.mem_nhds hloc.localInverse_mem_source)] with p hp
    change f p = f (p.1, (hloc.localInverse p.2 : AddCircle (1 : ℝ)))
    rw [hloc.localInverse_right_inv hp]
  · change f (k, (x : AddCircle (1 : ℝ))) =
      f (k, (hloc.localInverse (x : AddCircle (1 : ℝ)) : AddCircle (1 : ℝ)))
    rw [hleft]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.contMDiffOn_of_comp_coe then
    throwError "Refusing to shadow existing declaration AddCircle.contMDiffOn_of_comp_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.contMDiffOn_of_comp_coe ``Submission.AddCircle.contMDiffOn_of_comp_coe

end AddCircle
