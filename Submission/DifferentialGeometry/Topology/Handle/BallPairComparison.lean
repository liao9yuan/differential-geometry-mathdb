import Submission.DifferentialGeometry.Topology.Handle.BallPairExtension
import Submission.DifferentialGeometry.Topology.Manifold.SectorRoundingComparison
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace PartialDiffeomorph
open _root_.PartialDiffeomorph

variable (m : ℕ)

open _root_.PartialDiffeomorph in
private local instance _root_.Submission.PartialDiffeomorph.instFactEqNatFinrankRealEuclideanSpaceFinHAddOfNat_differentialGeometry :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 1) + 1))) = (m + 1) + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.PartialDiffeomorph.instFactEqNatFinrankRealEuclideanSpaceFinHAddOfNat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `PartialDiffeomorph.instFactEqNatFinrankRealEuclideanSpaceFinHAddOfNat_differentialGeometry target :: scope.openDecls } }

open _root_.PartialDiffeomorph in
theorem exists_diffeomorph_eqOn_of_diffeomorphic_balls
    (c : PartialDiffeomorph (𝓡 ((m + 1) + 1)) (𝓡 ((m + 1) + 1))
      (EuclideanSpace ℝ (Fin ((m + 1) + 1)))
      (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ∞)
    (D₀ D₁ : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ]
      (EuclideanSpace ℝ (Fin ((m + 1) + 1))))
    {A B : Set (EuclideanSpace ℝ (Fin ((m + 1) + 1)))}
    (hD₀ : D₀ '' _root_.Metric.closedBall 0 1 = A) (hD₁ : D₁ '' _root_.Metric.closedBall 0 1 = B)
    (hc : c.toOpenPartialHomeomorph.IsImage A B)
    (φ : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1))
      (EuclideanSpace ℝ (Fin (m + 1)))
      (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1) ∞)
    {R : ℝ} (hR : 0 < R) (hφ : _root_.Metric.closedBall 0 R ⊆ φ.source)
    (hsource : ∀ x ∈ _root_.Metric.closedBall 0 R, D₀ (φ x).val ∈ c.source)
    {K : Set (EuclideanSpace ℝ (Fin ((m + 1) + 1)))} (hK : IsCompact K)
    (hKφ : K ⊆ D₀ '' (Subtype.val '' (φ '' _root_.Metric.ball 0 R))) :
    ∃ Q : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ]
        (EuclideanSpace ℝ (Fin ((m + 1) + 1))),
      Q '' A = B ∧ ∃ V, IsOpen V ∧ K ⊆ V ∧ V ⊆ c.source ∧ _root_.Set.EqOn Q c V := by
  let E := EuclideanSpace ℝ (Fin ((m + 1) + 1))
  let F := (D₀.toPartialDiffeomorph.trans c).trans D₁.symm.toPartialDiffeomorph
  have hFs : F.source = D₀ ⁻¹' c.source := by
    ext x
    change ((x ∈ (_root_.Set.univ : Set E) ∧ D₀ x ∈ c.source) ∧ c (D₀ x) ∈ (_root_.Set.univ : Set E)) ↔ _
    simp
  have hF (x : E) : F x = D₁.symm (c (D₀ x)) := rfl
  have h₀ (x : E) : D₀ x ∈ A ↔ x ∈ _root_.Metric.closedBall 0 1 := by
    rw [← hD₀]
    exact D₀.injective.mem_set_image
  have h₁ (x : E) : D₁.symm x ∈ _root_.Metric.closedBall 0 1 ↔ x ∈ B := by
    rw [← hD₁]
    exact (Set.mem_image_iff_of_inverse D₁.symm_apply_apply D₁.apply_symm_apply).symm
  have hFi : F.toOpenPartialHomeomorph.IsImage (_root_.Metric.closedBall 0 1) (_root_.Metric.closedBall 0 1) := by
    intro x hx
    change F x ∈ _root_.Metric.closedBall 0 1 ↔ x ∈ _root_.Metric.closedBall 0 1
    rw [hF, h₁]
    have hx' : D₀ x ∈ c.source := by
      have hs : x ∈ F.source := hx
      rwa [hFs] at hs
    exact (hc hx').trans (h₀ x)
  have hFb : _root_.Set.MapsTo F (_root_.Metric.closedBall 0 1 ∩ F.source) (_root_.Metric.closedBall 0 1) :=
    fun x hx => (hFi hx.2).mpr hx.1
  have hFsphere : _root_.Set.MapsTo F (_root_.Metric.sphere 0 1 ∩ F.source) (_root_.Metric.sphere 0 1) := by
    intro x hx
    have h := hFi.frontier hx.2
    rw [frontier_closedBall _ one_ne_zero] at h
    exact h.mpr hx.1
  have hFφ (x : EuclideanSpace ℝ (Fin (m + 1))) (hx : x ∈ _root_.Metric.closedBall 0 R) :
      (φ x).val ∈ F.source := by
    rw [hFs]
    exact hsource x hx
  have hK' : IsCompact (D₀.symm '' K) := hK.image D₀.symm.continuous
  have hKφ' : D₀.symm '' K ⊆ Subtype.val '' (φ '' _root_.Metric.ball 0 R) := by
    rintro z ⟨y, hy, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hKφ hy
    simpa only [D₀.symm_apply_apply] using hw
  obtain ⟨q, hq, U, hU, hKU, hUF, heq⟩ :=
    F.exists_diffeomorph_eqOn_of_boundary_disk_chart m φ hR hφ hFφ hFsphere hFb hK' hKφ'
  let Q := (D₀.symm.trans q).trans D₁
  let V := D₀ '' U
  refine ⟨Q, ?_, V, D₀.toHomeomorph.isOpenMap U hU, ?_, ?_, ?_⟩
  · rw [← hD₀, ← hD₁]
    change (D₁ ∘ q ∘ D₀.symm) '' (D₀ '' _root_.Metric.closedBall 0 1) = D₁ '' _root_.Metric.closedBall 0 1
    rw [_root_.Set.image_comp, _root_.Set.image_comp, _root_.Set.image_image D₀.symm D₀]
    simp only [D₀.symm_apply_apply, _root_.Set.image_id']
    rw [hq]
  · intro x hx
    exact ⟨D₀.symm x, hKU (_root_.Set.mem_image_of_mem D₀.symm hx), D₀.apply_symm_apply x⟩
  · rintro x ⟨y, hy, rfl⟩
    have h := hUF hy
    rwa [hFs] at h
  · rintro x ⟨y, hy, rfl⟩
    change D₁ (q (D₀.symm (D₀ y))) = c (D₀ y)
    rw [D₀.symm_apply_apply, heq hy, hF, D₁.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.exists_diffeomorph_eqOn_of_diffeomorphic_balls then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.exists_diffeomorph_eqOn_of_diffeomorphic_balls"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.exists_diffeomorph_eqOn_of_diffeomorphic_balls ``Submission.PartialDiffeomorph.exists_diffeomorph_eqOn_of_diffeomorphic_balls


open _root_.PartialDiffeomorph in
theorem exists_diffeomorph_eqOn_neighborhood_of_boundary_disk
    (c : PartialDiffeomorph (𝓡 ((m + 1) + 1)) (𝓡 ((m + 1) + 1))
      (EuclideanSpace ℝ (Fin ((m + 1) + 1)))
      (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ∞)
    (D₀ D₁ : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ]
      (EuclideanSpace ℝ (Fin ((m + 1) + 1))))
    {A B : Set (EuclideanSpace ℝ (Fin ((m + 1) + 1)))}
    (hD₀ : D₀ '' _root_.Metric.closedBall 0 1 = A) (hD₁ : D₁ '' _root_.Metric.closedBall 0 1 = B)
    (hc : c.toOpenPartialHomeomorph.IsImage A B)
    (φ : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1))
      (EuclideanSpace ℝ (Fin (m + 1)))
      (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1) ∞)
    (hφ : _root_.Metric.closedBall 0 1 ⊆ φ.source)
    (hsource : ∀ x ∈ _root_.Metric.closedBall 0 1, D₀ (φ x).val ∈ c.source) :
    ∃ Q : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ]
        (EuclideanSpace ℝ (Fin ((m + 1) + 1))),
      Q '' A = B ∧ ∃ V, IsOpen V ∧
        D₀ '' (Subtype.val '' (φ '' _root_.Metric.closedBall 0 1)) ⊆ V ∧ V ⊆ c.source ∧ _root_.Set.EqOn Q c V := by
  let E := EuclideanSpace ℝ (Fin (m + 1))
  let f : E → EuclideanSpace ℝ (Fin ((m + 1) + 1)) := fun x => D₀ (φ x).val
  have hf : ContinuousOn f φ.source := D₀.continuous.comp_continuousOn
    (continuous_subtype_val.comp_continuousOn φ.toOpenPartialHomeomorph.continuousOn)
  let U := φ.source ∩ f ⁻¹' c.source
  have hU : IsOpen U := hf.isOpen_inter_preimage φ.open_source c.open_source
  have hballU : _root_.Metric.closedBall 0 1 ⊆ U := fun x hx => ⟨hφ hx, hsource x hx⟩
  obtain ⟨δ, hδ, hδU⟩ := (_root_.ProperSpace.isCompact_closedBall (0 : E) 1).exists_thickening_subset_open hU hballU
  rw [thickening_closedBall hδ zero_le_one] at hδU
  let R : ℝ := 1 + δ / 2
  have hR : 1 < R := by dsimp [R]; linarith
  have hRU : _root_.Metric.closedBall (0 : E) R ⊆ U :=
    (_root_.Metric.closedBall_subset_ball (by dsimp [R]; linarith : R < δ + 1)).trans hδU
  let K := D₀ '' (Subtype.val '' (φ '' _root_.Metric.closedBall 0 1))
  have hK : IsCompact K := by
    exact (((_root_.ProperSpace.isCompact_closedBall (0 : E) 1).image_of_continuousOn
      (φ.toOpenPartialHomeomorph.continuousOn.mono hφ)).image continuous_subtype_val).image D₀.continuous
  have hKφ : K ⊆ D₀ '' (Subtype.val '' (φ '' _root_.Metric.ball 0 R)) :=
    _root_.Set.image_mono (_root_.Set.image_mono (_root_.Set.image_mono (_root_.Metric.closedBall_subset_ball hR)))
  exact c.exists_diffeomorph_eqOn_of_diffeomorphic_balls m D₀ D₁ hD₀ hD₁ hc φ
    (zero_lt_one.trans hR) (fun x hx => (hRU hx).1) (fun x hx => (hRU hx).2) hK hKφ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.exists_diffeomorph_eqOn_neighborhood_of_boundary_disk then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.exists_diffeomorph_eqOn_neighborhood_of_boundary_disk"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.exists_diffeomorph_eqOn_neighborhood_of_boundary_disk ``Submission.PartialDiffeomorph.exists_diffeomorph_eqOn_neighborhood_of_boundary_disk


open _root_.PartialDiffeomorph in
theorem exists_diffeomorph_eqOn_neighborhood_of_rounded_corner_disk
    {P : Type*} [TopologicalSpace P]
    (c : PartialDiffeomorph (𝓡 ((m + 1) + 1)) (𝓡 ((m + 1) + 1))
      (EuclideanSpace ℝ (Fin ((m + 1) + 1)))
      (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ∞)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin ((m + 1) + 1))) (P × (ℝ × ℝ)))
    {A B : Set (EuclideanSpace ℝ (Fin ((m + 1) + 1)))}
    (hc : c.toOpenPartialHomeomorph.IsImage A B) (ε : ℝ)
    (D₀ D₁ : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ]
      (EuclideanSpace ℝ (Fin ((m + 1) + 1))))
    (hD₀ : D₀ '' _root_.Metric.closedBall 0 1 = e.smoothAbsQuadrantSet A ε)
    (hD₁ : D₁ '' _root_.Metric.closedBall 0 1 =
      (c.symm.toOpenPartialHomeomorph.trans e).smoothAbsQuadrantSet B ε)
    (φ : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1))
      (EuclideanSpace ℝ (Fin (m + 1)))
      (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1) ∞)
    (hφ : _root_.Metric.closedBall 0 1 ⊆ φ.source)
    (hsource : ∀ x ∈ _root_.Metric.closedBall 0 1, D₀ (φ x).val ∈ c.source) :
    ∃ Q : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ]
        (EuclideanSpace ℝ (Fin ((m + 1) + 1))),
      Q '' e.smoothAbsQuadrantSet A ε =
        (c.symm.toOpenPartialHomeomorph.trans e).smoothAbsQuadrantSet B ε ∧
      ∃ V, IsOpen V ∧ D₀ '' (Subtype.val '' (φ '' _root_.Metric.closedBall 0 1)) ⊆ V ∧
        V ⊆ c.source ∧ _root_.Set.EqOn Q c V := by
  exact c.exists_diffeomorph_eqOn_neighborhood_of_boundary_disk m D₀ D₁ hD₀ hD₁
    (hc.smoothAbsQuadrantSet e ε) φ hφ hsource

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.exists_diffeomorph_eqOn_neighborhood_of_rounded_corner_disk then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.exists_diffeomorph_eqOn_neighborhood_of_rounded_corner_disk"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.exists_diffeomorph_eqOn_neighborhood_of_rounded_corner_disk ``Submission.PartialDiffeomorph.exists_diffeomorph_eqOn_neighborhood_of_rounded_corner_disk

end PartialDiffeomorph
