import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.BoundaryIsotopy
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.VelocityExtensionEuclidean

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [hBoundary : I.Boundaryless] [hT2 : T2Space M] [hCompact : CompactSpace M]
    [hNonempty : Nonempty M] [SigmaCompactSpace M]
variable {a b : ℝ}

/-- The single analytic input that the boundary isotopy headline consumes: on an immersed
family of embedded loops, smooth on the closed time window, the temporal velocity field extends
to a global smooth time dependent vector field whose one sided time derivatives reproduce the
family on the window. -/
def LoopFamilyVelocityExtensionProducer (a b : ℝ) : Prop :=
  ∀ γ : ℝ → ContinuousFreeLoop M,
    (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b) →
    (curveOfLoopFamily γ).ImmersedOn (I := I) (_root_.Set.Icc a b) →
    (∀ t ∈ _root_.Set.Icc a b, Topology.IsEmbedding (γ t)) →
    LoopFamilyVelocityExtension (I := I) a b γ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyVelocityExtensionProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyVelocityExtensionProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyVelocityExtensionProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyVelocityExtensionProducer

omit [CompleteSpace E] hNonempty in
theorem rfs_csf_boundary_isotopy_of_velocityExtensionProducer
    (h : LoopFamilyVelocityExtensionProducer (I := I) (M := M) a b)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (_root_.Set.Icc a b))
    (hemb : ∀ t ∈ _root_.Set.Icc a b, Topology.IsEmbedding (γ t))
    (t₀ : ℝ) (ht₀ : t₀ ∈ _root_.Set.Icc a b) (hab : a < b) :
    ∃ ε > 0, ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : M × ℝ => Φ p.2 p.1)
        (_root_.Set.univ ×ˢ (_root_.Set.Icc a b ∩ _root_.Set.Ioo (t₀ - ε) (t₀ + ε))) ∧
      (∀ p, Φ t₀ p = p) ∧
      ∀ t ∈ _root_.Set.Icc a b ∩ _root_.Set.Ioo (t₀ - ε) (t₀ + ε), ∀ z, Φ t (γ t₀ z) = γ t z :=
  let _ := hab
  rfs_csf_boundary_isotopy_of_velocityExtension a b γ t₀ ht₀ (h γ hγ hi hemb)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_boundary_isotopy_of_velocityExtensionProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_boundary_isotopy_of_velocityExtensionProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_boundary_isotopy_of_velocityExtensionProducer ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.rfs_csf_boundary_isotopy_of_velocityExtensionProducer

omit [CompleteSpace E] [FiniteDimensional ℝ E] hBoundary hT2 hCompact hNonempty
  [SigmaCompactSpace M] in
theorem loopFamilyVelocityExtensionProducer_of_allWindows
    (h : ∀ (a' b' : ℝ) (γ : ℝ → ContinuousFreeLoop M),
      (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a' b') →
      (curveOfLoopFamily γ).ImmersedOn (I := I) (_root_.Set.Icc a' b') →
      (∀ t ∈ _root_.Set.Icc a' b', Topology.IsEmbedding (γ t)) →
      LoopFamilyVelocityExtension (I := I) a' b' γ) :
    LoopFamilyVelocityExtensionProducer (I := I) (M := M) a b :=
  fun γ hγ hi hemb => h a b γ hγ hi hemb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtensionProducer_of_allWindows then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtensionProducer_of_allWindows"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtensionProducer_of_allWindows ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtensionProducer_of_allWindows

end Manifold

section ModelSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {a b : ℝ}

/-- The remaining genuinely analytic gap of the model space producer: a family that is only
smooth on the closed time window has to be replaced by a globally smooth family with the same
values on the window and with injective graph lift derivative. -/
def LoopFamilyGlobalSmoothExtension (a b : ℝ) (γ : ℝ → ContinuousFreeLoop E) : Prop :=
  ∃ γ' : ℝ → ContinuousFreeLoop E,
    (∀ t ∈ _root_.Set.Icc a b, γ' t = γ t) ∧
    ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ' q.1 (q.2 : Surgery.Topology.Circle)) ∧
    (∀ t, Function.Injective (fun z : Surgery.Topology.Circle => γ' t z)) ∧
    ∀ q, Function.Injective (fderiv ℝ (graphLift γ') q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyGlobalSmoothExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyGlobalSmoothExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyGlobalSmoothExtension ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.LoopFamilyGlobalSmoothExtension

omit [FiniteDimensional ℝ E] in
theorem loopFamilyGlobalSmoothExtension_of_globalSmooth
    {γ : ℝ → ContinuousFreeLoop E}
    (hγ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : Surgery.Topology.Circle)))
    (hemb : ∀ t, Function.Injective (fun z : Surgery.Topology.Circle => γ t z))
    (hi : ∀ q, Function.Injective (fderiv ℝ (graphLift γ) q)) :
    LoopFamilyGlobalSmoothExtension a b γ :=
  ⟨γ, fun _ _ => rfl, hγ, hemb, hi⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyGlobalSmoothExtension_of_globalSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyGlobalSmoothExtension_of_globalSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyGlobalSmoothExtension_of_globalSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyGlobalSmoothExtension_of_globalSmooth

theorem loopFamilyVelocityExtension_modelSpace_of_globalSmoothExtension
    {γ : ℝ → ContinuousFreeLoop E} (h : LoopFamilyGlobalSmoothExtension a b γ) :
    LoopFamilyVelocityExtension (I := 𝓘(ℝ, E)) a b γ := by
  obtain ⟨γ', hagree, hγ', hemb', hi'⟩ := h
  obtain ⟨X, hX, hIco, hIoc⟩ := loopFamilyVelocityExtension_modelSpace a b γ' hemb' hγ' hi'
  refine ⟨X, hX, ?_, ?_⟩
  · intro t ht z
    have htIcc : t ∈ _root_.Set.Icc a b := _root_.Set.Ico_subset_Icc_self ht
    have hsub : _root_.Set.Iio (t + (b - t)) ∩ _root_.Set.Ici t ⊆ _root_.Set.Icc a b := by
      rintro s ⟨hs1, hs2⟩
      refine ⟨le_trans ht.1 hs2, ?_⟩
      have : s < b := by
        have h1 : t + (b - t) = b := by ring
        rwa [h1] at hs1
      exact this.le
    have hmem : _root_.Set.Icc a b ∈ 𝓝[_root_.Set.Ici t] t :=
      _root_.Filter.mem_of_superset
        (_root_.Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by
            have h1 : t + (b - t) = b := by ring
            rw [h1]; exact ht.2)))
          self_mem_nhdsWithin) hsub
    have heq : (fun s : ℝ => γ s z) =ᶠ[𝓝[_root_.Set.Ici t] t] (fun s : ℝ => γ' s z) :=
      _root_.Filter.eventually_of_mem hmem fun s hs =>
        (congrArg (fun f : ContinuousFreeLoop E => f z) (hagree s hs)).symm
    have hx : γ t z = γ' t z :=
      (congrArg (fun f : ContinuousFreeLoop E => f z) (hagree t htIcc)).symm
    have hbase := hIco t ht z
    rw [show X t (γ' t z) = X t (γ t z) from by rw [hx]] at hbase
    exact hbase.congr_of_eventuallyEq heq hx
  · intro t ht z
    have htIcc : t ∈ _root_.Set.Icc a b := _root_.Set.Ioc_subset_Icc_self ht
    have hsub : _root_.Set.Ioi (t - (t - a)) ∩ _root_.Set.Iic t ⊆ _root_.Set.Icc a b := by
      rintro s ⟨hs1, hs2⟩
      refine ⟨?_, le_trans hs2 ht.2⟩
      have : a < s := by
        have h1 : t - (t - a) = a := by ring
        rwa [h1] at hs1
      exact this.le
    have hmem : _root_.Set.Icc a b ∈ 𝓝[_root_.Set.Iic t] t :=
      _root_.Filter.mem_of_superset
        (_root_.Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by
            have h1 : t - (t - a) = a := by ring
            rw [h1]; exact ht.1)))
          self_mem_nhdsWithin) hsub
    have heq : (fun s : ℝ => γ s z) =ᶠ[𝓝[_root_.Set.Iic t] t] (fun s : ℝ => γ' s z) :=
      _root_.Filter.eventually_of_mem hmem fun s hs =>
        (congrArg (fun f : ContinuousFreeLoop E => f z) (hagree s hs)).symm
    have hx : γ t z = γ' t z :=
      (congrArg (fun f : ContinuousFreeLoop E => f z) (hagree t htIcc)).symm
    have hbase := hIoc t ht z
    rw [show X t (γ' t z) = X t (γ t z) from by rw [hx]] at hbase
    exact hbase.congr_of_eventuallyEq heq hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtension_modelSpace_of_globalSmoothExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtension_modelSpace_of_globalSmoothExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtension_modelSpace_of_globalSmoothExtension ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.loopFamilyVelocityExtension_modelSpace_of_globalSmoothExtension

end ModelSpace

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
