import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Order.ProjIcc

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.Embedding

theorem exists_curve_of_product_chart_segment
    {N M W : Type*} [TopologicalSpace N] [TopologicalSpace M] [TopologicalSpace W]
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens M)
    (e : O ≃ₜ V) (ι : W → M) (hemb : _root_.Topology.IsEmbedding ι)
    (p : N) (t σ r : ℝ) (hr : 0 < r)
    (hsegment : ∀ s ∈ _root_.Set.Icc 0 r, (p, t + σ * s) ∈ O)
    (himage : ∀ s (hs : s ∈ _root_.Set.Icc 0 r), (e ⟨(p, t + σ * s), hsegment s hs⟩ : M) ∈ _root_.Set.range ι) :
    ∃ γ : ℝ → W, Continuous γ ∧
      ∀ s (hs : s ∈ _root_.Set.Icc 0 r), ι (γ s) = (e ⟨(p, t + σ * s), hsegment s hs⟩ : M) := by
  let clamp : ℝ → _root_.Set.Icc 0 r := _root_.Set.projIcc 0 r hr.le
  let q : ℝ → O := fun s ↦ ⟨(p, t + σ * (clamp s : ℝ)), hsegment _ (clamp s).property⟩
  have hclamp : Continuous (fun s ↦ (clamp s : ℝ)) :=
    continuous_subtype_val.comp continuous_projIcc
  have hq : Continuous q :=
    (continuous_const.prodMk (continuous_const.add (continuous_const.mul hclamp))).subtype_mk _
  have hpre : ∀ s, ∃ w : W, ι w = (e (q s) : M) :=
    fun s ↦ himage _ (clamp s).property
  choose γ hγeq using hpre
  have hγ : Continuous γ := by
    apply hemb.isInducing.continuous_iff.mpr
    have heq : ι ∘ γ = fun s ↦ (e (q s) : M) := funext hγeq
    rw [heq]
    exact continuous_subtype_val.comp (e.continuous.comp hq)
  refine ⟨γ, hγ, ?_⟩
  intro s hs
  rw [hγeq]
  congr 2
  apply Subtype.ext
  change (p, t + σ * (_root_.Set.projIcc 0 r hr.le s : ℝ)) = (p, t + σ * s)
  rw [_root_.Set.projIcc_of_mem hr.le hs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Embedding.exists_curve_of_product_chart_segment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Embedding.exists_curve_of_product_chart_segment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Embedding.exists_curve_of_product_chart_segment ``Submission.DifferentialGeometry.Topology.Embedding.exists_curve_of_product_chart_segment

end DifferentialGeometry.Topology.Embedding
