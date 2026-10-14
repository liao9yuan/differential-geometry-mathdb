import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.WindowGluing
import Mathlib.Topology.Order.IntermediateValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

theorem curveShorteningLocalUniqueness_of_short_time
    {D : RealTimeInterval} {a b : ℝ}
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    (hshort : ∀ (s T : ℝ), a ≤ s → s < T → T ≤ b →
      ∀ c₁ c₂ : CurveMap M,
        c₁.IsSolutionOn B.family.metric (_root_.Set.Icc s T) →
        c₂.IsSolutionOn B.family.metric (_root_.Set.Icc s T) →
        (∀ z, c₁ z s = c₂ z s) →
        ∃ δ > 0, ∀ z t, t ∈ _root_.Set.Icc s (_root_.Min.min T (s + δ)) → c₁ z t = c₂ z t) :
    curveShorteningLocalUniqueness (I := I) (M := M) B := by
  intro s t₁ t₂ has _ _ hb₁ _ c₁ c₂ hc₁ hc₂ h₀
  let L := _root_.Min.min t₁ t₂
  have hLt₁ : L ≤ t₁ := min_le_left t₁ t₂
  have hLt₂ : L ≤ t₂ := min_le_right t₁ t₂
  have hLb : L ≤ b := hLt₁.trans hb₁
  have hcont (c : CurveMap M) {T : ℝ}
      (hc : c.SmoothOn (I := I) (_root_.Set.Icc s T)) (hLT : L ≤ T) :
      ContinuousOn (fun t => fun z => c z t) (_root_.Set.Icc s L) := by
    apply continuousOn_pi.2
    intro z
    obtain ⟨x, -, hx⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z
    rw [← hx]
    exact (c.time_slice_contMDiffOn (_root_.Set.Icc s T) hc x).continuousOn.mono
      (_root_.Set.Icc_subset_Icc le_rfl hLT)
  let A : Set ℝ := {t | (fun z => c₁ z t) = (fun z => c₂ z t)}
  have hclosed : IsClosed (A ∩ _root_.Set.Icc s L) := by
    simpa only [A, _root_.Set.inter_comm, Set.inter_def, Set.mem_ofPred_eq] using
      (isClosed_Icc.isClosed_eq (hcont c₁ hc₁.smooth hLt₁) (hcont c₂ hc₂.smooth hLt₂))
  have hsubset : _root_.Set.Icc s L ⊆ A := by
    apply hclosed.Icc_subset_of_forall_mem_nhdsWithin (funext h₀)
    rintro u ⟨huA, hu⟩
    have hrestrict₁ : c₁.IsSolutionOn B.family.metric (_root_.Set.Icc u L) :=
      hc₁.mono_Icc hu.1 hLt₁ hu.2
    have hrestrict₂ : c₂.IsSolutionOn B.family.metric (_root_.Set.Icc u L) :=
      hc₂.mono_Icc hu.1 hLt₂ hu.2
    obtain ⟨δ, hδ, hagree⟩ :=
      hshort u L (has.trans hu.1) hu.2 hLb c₁ c₂ hrestrict₁ hrestrict₂
        (fun z => congrFun huA z)
    exact Filter.mem_of_superset
      (Ioo_mem_nhdsGT (lt_min hu.2 (lt_add_of_pos_right u hδ)))
      (fun t ht => funext (fun z => hagree z t ⟨ht.1.le, ht.2.le⟩))
  intro z t ht
  exact congrFun (hsubset ht) z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalUniqueness_of_short_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalUniqueness_of_short_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalUniqueness_of_short_time ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.curveShorteningLocalUniqueness_of_short_time

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
