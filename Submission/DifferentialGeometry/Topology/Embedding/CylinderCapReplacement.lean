import Submission.DifferentialGeometry.Topology.Embedding.CylinderCap
import Submission.DifferentialGeometry.Topology.Embedding.Replacement
import Submission.DifferentialGeometry.Topology.Embedding.LocalDiffeomorph
import Mathlib.Topology.Instances.Real.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric _root_.TopologicalSpace
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology

namespace EuclideanGeometry

variable {E B M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace B] [TopologicalSpace M] [TopologicalSpace F]

theorem disjoint_cylinderCap_image_of_cylinder_sides
    (e : M → F) (Ψ : (E × ℝ) ≃ₜ F) {ε a σ : ℝ}
    (ha : |a| < ε) (hσa : 0 ≤ σ * a)
    (V : _root_.TopologicalSpace.Opens M) (C : (B × (⟨Ioo (-ε) ε, isOpen_Ioo⟩ : _root_.TopologicalSpace.Opens ℝ)) ≃ₜ V)
    (q : B → E) {D : Set M}
    (hwall : ∀ x ∈ _root_.Metric.closedBall (0 : E) 1, ∀ t ∈ _root_.Set.Ioo (-ε) ε,
      Ψ (x, t) ∈ _root_.Set.range e → ‖x‖ = 1)
    (hV : (V : Set M) = e ⁻¹' (Ψ '' (_root_.Metric.sphere (0 : E) 1 ×ˢ _root_.Set.Ioo (-ε) ε)))
    (hC : ∀ p, e (C p) = Ψ (q p.1, p.2.val))
    (hside : ∀ p, (C p : M) ∈ D ↔ σ * p.2.val ≤ 0) :
    Disjoint ((Ψ ∘ cylinderCap a) '' _root_.Metric.closedBall (0 : E) 1) (e '' Dᶜ) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hye⟩
  have hxnorm : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  have hsquare : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  have htime : |(cylinderCap a x).2| < ε := by
    rw [cylinderCap_snd, abs_mul]
    have habs : |‖x‖ ^ 2 - 1| ≤ 1 := abs_le.mpr ⟨by nlinarith [sq_nonneg ‖x‖], by linarith⟩
    exact (mul_le_mul_of_nonneg_left habs (abs_nonneg a)).trans_lt (by simpa using ha)
  have hfiber : Ψ ((cylinderCap a x).1, (cylinderCap a x).2) ∈ _root_.Set.range e := ⟨y, hye⟩
  have hnorm := hwall (cylinderCap a x).1
    (mem_closedBall_zero_iff.mpr (norm_cylinderCap_fst_le_one a x))
    (cylinderCap a x).2 (abs_lt.mp htime) hfiber
  have hyV : y ∈ V := by
    change y ∈ (V : Set M)
    rw [hV]
    exact ⟨cylinderCap a x, ⟨mem_sphere_zero_iff_norm.mpr hnorm, abs_lt.mp htime⟩, hye.symm⟩
  let p := C.symm ⟨y, hyV⟩
  have hp : (C p : M) = y := congrArg Subtype.val (C.apply_symm_apply ⟨y, hyV⟩)
  have hpt : p.2.val = (cylinderCap a x).2 := by
    exact congrArg Prod.snd (Ψ.injective ((hC p).symm.trans ((congrArg e hp).trans hye)))
  apply hy
  rw [← hp, hside, hpt, cylinderCap_snd, ← mul_assoc]
  exact mul_nonpos_of_nonneg_of_nonpos hσa (sub_nonpos.mpr hsquare)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EuclideanGeometry.disjoint_cylinderCap_image_of_cylinder_sides then
    throwError "Refusing to shadow existing declaration EuclideanGeometry.disjoint_cylinderCap_image_of_cylinder_sides"
  Lean.modifyEnv fun env => Lean.addAlias env `EuclideanGeometry.disjoint_cylinderCap_image_of_cylinder_sides ``Submission.EuclideanGeometry.disjoint_cylinderCap_image_of_cylinder_sides

end EuclideanGeometry

namespace Manifold
open _root_.Manifold

variable {E F B M H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace B] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [CompactSpace M] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem IsSmoothEmbedding.exists_cylinderCap_replacement
    {e : M → F} (he : _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, F) ∞ e)
    (Ψ : (E × ℝ) ≃ₘ[ℝ] F) {ε a σ : ℝ}
    (ha : a ≠ 0) (haε : |a| < ε) (hσa : 0 ≤ σ * a)
    (V : _root_.TopologicalSpace.Opens M) (C : (B × (⟨Ioo (-ε) ε, isOpen_Ioo⟩ : _root_.TopologicalSpace.Opens ℝ)) ≃ₜ V)
    (q : B → E) {D : Set M}
    (hwall : ∀ x ∈ _root_.Metric.closedBall (0 : E) 1, ∀ t ∈ _root_.Set.Ioo (-ε) ε,
      Ψ (x, t) ∈ _root_.Set.range e → ‖x‖ = 1)
    (hV : (V : Set M) = e ⁻¹' (Ψ '' (_root_.Metric.sphere (0 : E) 1 ×ˢ _root_.Set.Ioo (-ε) ε)))
    (hC : ∀ p, e (C p) = Ψ (q p.1, p.2.val))
    (hside : ∀ p, (C p : M) ∈ D ↔ σ * p.2.val ≤ 0)
    (φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    (hballφ : _root_.Metric.closedBall (0 : E) 1 ⊆ φ.source)
    (hφD : φ '' _root_.Metric.closedBall (0 : E) 1 = D)
    (hcollar : ∀ x ∈ _root_.Metric.sphere (0 : E) 1,
      Ψ ∘ EuclideanGeometry.cylinderCap a =ᶠ[nhds x] e ∘ φ) :
    ∃ f : M → F, _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, F) ∞ f ∧
      (∀ x ∈ _root_.Metric.closedBall (0 : E) 1, f (φ x) = Ψ (EuclideanGeometry.cylinderCap a x)) ∧
      _root_.Set.EqOn f e Dᶜ ∧
      ∀ y ∈ D, f =ᶠ[nhds y] (Ψ ∘ EuclideanGeometry.cylinderCap a) ∘ φ.symm := by
  let L : (E × ℝ) ≃L[ℝ] F := Ψ.mfderivToContinuousLinearEquiv (by simp) 0
  let _ : FiniteDimensional ℝ F :=
    FiniteDimensional.of_injective L.symm.toLinearMap L.symm.injective
  have hcap := (IsSmoothEmbedding.id (I := 𝓘(ℝ, E)) (M := E) (n := ∞)).cylinderCap ha
  have hg : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (Ψ ∘ EuclideanGeometry.cylinderCap a) :=
    ⟨hcap.isImmersion.isLocalDiffeomorphOn_comp_of_ne_zero
      (fun y => Ψ.isLocalDiffeomorph y.val) (by simp),
      Ψ.toHomeomorph.isEmbedding.comp hcap.isEmbedding⟩
  have hdisj := EuclideanGeometry.disjoint_cylinderCap_image_of_cylinder_sides
    e Ψ.toHomeomorph haε hσa V C q hwall hV hC hside
  have hfront : frontier (_root_.Metric.closedBall (0 : E) 1) = _root_.Metric.sphere 0 1 :=
    frontier_closedBall (0 : E) (by norm_num)
  obtain ⟨f, hf, hmap, hfix, hnear⟩ := he.exists_replacement_of_partialDiffeomorph (by simp)
    φ (_root_.ProperSpace.isCompact_closedBall (0 : E) 1) hballφ hg
    (fun x hx => hcollar x (hfront.subset hx)) (hφD.symm ▸ hdisj)
  exact ⟨f, hf, hmap, hφD ▸ hfix, hφD ▸ hnear⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.exists_cylinderCap_replacement then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.exists_cylinderCap_replacement"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.exists_cylinderCap_replacement ``Submission.Manifold.IsSmoothEmbedding.exists_cylinderCap_replacement

end Manifold
