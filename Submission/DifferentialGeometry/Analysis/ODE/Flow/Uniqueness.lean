import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Bundle _root_.Filter _root_.Manifold _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [T2Space M]
  {γ γ' : ℝ → M} {v : (x : M) → TangentSpace I x} {K : Set ℝ} {t₀ : ℝ}

theorem isMIntegralCurveOn_eqOn_of_contMDiff
    (hK : IsOpen K) (hconn : IsPreconnected K) (ht₀ : t₀ ∈ K)
    (hinterior : ∀ t ∈ K, I.IsInteriorPoint (γ t))
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurveOn γ v K) (hγ' : IsMIntegralCurveOn γ' v K)
    (h : γ t₀ = γ' t₀) : _root_.Set.EqOn γ γ' K := by
  let s := {t | γ t = γ' t} ∩ K
  suffices hsub : K ⊆ s from fun t ht ↦ (hsub ht).1
  apply hconn.subset_of_closure_inter_subset (s := K) (u := s) _
    ⟨t₀, ht₀, h, ht₀⟩
  · rw [show s = {t | γ t = γ' t} ∩ K from rfl, _root_.Set.inter_comm,
      ← Subtype.image_preimage_val, _root_.Set.inter_comm, ← Subtype.image_preimage_val,
      _root_.Set.image_subset_image_iff Subtype.val_injective, _root_.Set.preimage_ofPred_eq]
    intro t ht
    rw [_root_.Set.mem_preimage, ← closure_subtype] at ht
    revert ht t
    apply IsClosed.closure_subset (isClosed_eq _ _)
    · rw [continuous_iff_continuousAt]
      rintro ⟨_, ht⟩
      apply ContinuousAt.comp _ continuousAt_subtype_val
      rw [Subtype.coe_mk]
      exact (hγ.continuousWithinAt ht).continuousAt (hK.mem_nhds ht)
    · rw [continuous_iff_continuousAt]
      rintro ⟨_, ht⟩
      apply ContinuousAt.comp _ continuousAt_subtype_val
      rw [Subtype.coe_mk]
      exact (hγ'.continuousWithinAt ht).continuousAt (hK.mem_nhds ht)
  · rw [isOpen_iff_mem_nhds]
    intro t ht
    have hmem := hK.mem_nhds ht.2
    have heq : γ =ᶠ[𝓝 t] γ' := isMIntegralCurveAt_eventuallyEq_of_contMDiffAt
      (hinterior t ht.2) hv.contMDiffAt (hγ.isMIntegralCurveAt hmem)
      (hγ'.isMIntegralCurveAt hmem) ht.1
    exact (heq.and hmem).mono fun _ hx ↦ hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `isMIntegralCurveOn_eqOn_of_contMDiff then
    throwError "Refusing to shadow existing declaration isMIntegralCurveOn_eqOn_of_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `isMIntegralCurveOn_eqOn_of_contMDiff ``Submission.isMIntegralCurveOn_eqOn_of_contMDiff

theorem isMIntegralCurveOn_eqOn_of_contMDiff_boundaryless [BoundarylessManifold I M]
    (hK : IsOpen K) (hconn : IsPreconnected K) (ht₀ : t₀ ∈ K)
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurveOn γ v K) (hγ' : IsMIntegralCurveOn γ' v K)
    (h : γ t₀ = γ' t₀) : _root_.Set.EqOn γ γ' K :=
  isMIntegralCurveOn_eqOn_of_contMDiff hK hconn ht₀
    (fun _ _ ↦ BoundarylessManifold.isInteriorPoint) hv hγ hγ' h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `isMIntegralCurveOn_eqOn_of_contMDiff_boundaryless then
    throwError "Refusing to shadow existing declaration isMIntegralCurveOn_eqOn_of_contMDiff_boundaryless"
  Lean.modifyEnv fun env => Lean.addAlias env `isMIntegralCurveOn_eqOn_of_contMDiff_boundaryless ``Submission.isMIntegralCurveOn_eqOn_of_contMDiff_boundaryless
