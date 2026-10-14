import Submission.DifferentialGeometry.Topology.Embedding.CylinderCapLift
import Submission.DifferentialGeometry.Topology.Embedding.CylinderCapReplacement
import Submission.DifferentialGeometry.Topology.Manifold.DiskChart

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric _root_.TopologicalSpace
open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

namespace Manifold
open _root_.Manifold

variable {E F B H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 1 + 1)] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace B] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem IsSmoothEmbedding.exists_cylinderCap_chart
    {e : M → F} (he : _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, F) ∞ e)
    (Ψ : (E × ℝ) ≃ₘ[ℝ] F) {ε a σ : ℝ}
    (ha : a ≠ 0) (haε : |a| < ε) (hσa : 0 ≤ σ * a)
    (V : _root_.TopologicalSpace.Opens M) (C : (B × (⟨Ioo (-ε) ε, isOpen_Ioo⟩ : _root_.TopologicalSpace.Opens ℝ)) ≃ₜ V)
    (q : B → E) {D : Set M}
    (hwall : ∀ x ∈ _root_.Metric.closedBall (0 : E) 1, ∀ t ∈ _root_.Set.Ioo (-ε) ε,
      Ψ (x, t) ∈ _root_.Set.range e ↔ ‖x‖ = 1)
    (hV : (V : Set M) = e ⁻¹' (Ψ '' (_root_.Metric.sphere (0 : E) 1 ×ˢ _root_.Set.Ioo (-ε) ε)))
    (hC : ∀ p, e (C p) = Ψ (q p.1, p.2.val))
    (hside : ∀ p, (C p : M) ∈ D ↔ σ * p.2.val ≤ 0)
    (φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    (hballφ : _root_.Metric.closedBall (0 : E) 1 ⊆ φ.source)
    (hφD : φ '' _root_.Metric.closedBall (0 : E) 1 = D)
    (hboundary : e '' (φ '' _root_.Metric.sphere (0 : E) 1) = Ψ '' (_root_.Metric.sphere (0 : E) 1 ×ˢ {0})) :
    ∃ χ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞,
      _root_.Metric.closedBall (0 : E) 1 ⊆ χ.source ∧ χ '' _root_.Metric.closedBall (0 : E) 1 = D ∧
      ∀ x ∈ _root_.Metric.sphere (0 : E) 1,
        Ψ ∘ EuclideanGeometry.cylinderCap a =ᶠ[nhds x] e ∘ χ := by
  have hε : 0 < ε := (abs_nonneg a).trans_lt haε
  let _ : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ 1
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos
    (by rw [show Module.finrank ℝ E = 1 + 1 from Fact.out]; norm_num : 0 < Module.finrank ℝ E)
  let _ : T2Space M := he.isEmbedding.t2Space
  obtain ⟨ψ, _, hψ, _, hψeq⟩ := he.exists_partialDiffeomorph_cylinderCap Ψ hε ha
    (fun x hx t ht => (hwall x (_root_.Metric.sphere_subset_closedBall hx) t ht).mpr
      (mem_sphere_zero_iff_norm.mp hx))
  have hψboundary : e '' (ψ '' _root_.Metric.sphere (0 : E) 1) = Ψ '' (_root_.Metric.sphere (0 : E) 1 ×ˢ {0}) := by
    rw [_root_.Set.image_image, ← EuclideanGeometry.cylinderCap_image_sphere a, ← _root_.Set.image_comp]
    exact _root_.Set.image_congr fun x hx => hψeq x (hψ hx)
  have hboundary' : φ '' _root_.Metric.sphere (0 : E) 1 = ψ '' _root_.Metric.sphere (0 : E) 1 :=
    (Set.image_injective.mpr he.isEmbedding.injective) (hboundary.trans hψboundary.symm)
  have hdisj := EuclideanGeometry.disjoint_cylinderCap_image_of_cylinder_sides e Ψ.toHomeomorph
    haε hσa V C q (fun x hx t ht hh => (hwall x hx t ht).mp hh) hV hC hside
  have hside' : _root_.Set.MapsTo ψ (_root_.Metric.closedBall (0 : E) 1 ∩ ψ.source) (φ '' _root_.Metric.closedBall (0 : E) 1) := by
    intro x hx
    rw [hφD]
    by_contra hh
    exact (Set.disjoint_left.mp hdisj) ⟨x, hx.1, (hψeq x hx.2).symm⟩ ⟨ψ x, hh, rfl⟩
  obtain ⟨χ, hχ, hχD, W, hW, hSW, hWψ, hχψ⟩ :=
    φ.exists_disk_chart_eqOn_circle_neighborhood ψ hballφ hψ hboundary' hside'
  refine ⟨χ, hχ, hχD.trans hφD, ?_⟩
  intro x hx
  filter_upwards [hW.mem_nhds (hSW hx)] with y hy
  change Ψ (EuclideanGeometry.cylinderCap a y) = e (χ y)
  rw [hχψ hy]
  exact (hψeq y (hWψ hy)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.exists_cylinderCap_chart then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.exists_cylinderCap_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.exists_cylinderCap_chart ``Submission.Manifold.IsSmoothEmbedding.exists_cylinderCap_chart

end Manifold
