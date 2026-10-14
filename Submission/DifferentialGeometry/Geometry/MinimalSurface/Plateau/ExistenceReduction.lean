import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothDiskAreaDensity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Set _root_.ContinuousMap _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def HasMinimalConformalSpanningDisk (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : freeLoop M) : Prop :=
  ∃ u : C(closedDisk, M),
    DiskSmoothInterior (E := E) u ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension u) z) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g (diskExtension u) z = 0) ∧
      _root_.MeasureTheory.IntegrableOn (diskMapEnergyDensity g (diskExtension u)) (Metric.closedBall (0 : ℂ) 1) ∧
      DiskWeakJordanTrace γ u ∧
      ∀ v : C(closedDisk, M), DiskSmoothUpToBoundary (E := E) v → diskTrace v = γ →
        riemannianDiskArea g u ≤ riemannianDiskArea g v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.HasMinimalConformalSpanningDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.HasMinimalConformalSpanningDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.HasMinimalConformalSpanningDisk ``Submission.DifferentialGeometry.Geometry.HasMinimalConformalSpanningDisk

theorem HasMinimalConformalSpanningDisk.of_isMorreyDisk
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (h : IsMorreyDisk g γ u) : HasMinimalConformalSpanningDisk g γ :=
  ⟨u, h.smoothInterior, h.conformal, h.harmonic, h.finiteEnergy, h.trace, h.minimizesSmooth⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Geometry.HasMinimalConformalSpanningDisk
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.HasMinimalConformalSpanningDisk.of_isMorreyDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.HasMinimalConformalSpanningDisk.of_isMorreyDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.HasMinimalConformalSpanningDisk.of_isMorreyDisk ``Submission.DifferentialGeometry.Geometry.HasMinimalConformalSpanningDisk.of_isMorreyDisk

theorem exists_isMorreyDisk_of_hasMinimalConformalSpanningDisk_of_areaDenseForWeakTraces
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    (h : HasMinimalConformalSpanningDisk g γ)
    (hdensity : SmoothDisksAreAreaDenseForWeakTracesAt g γ) :
    ∃ u : C(closedDisk, M), IsMorreyDisk g γ u := by
  obtain ⟨u, hsmooth, hconformal, hharmonic, hfinite, htrace, hmin⟩ := h
  refine ⟨u, hsmooth, hconformal, hharmonic, hfinite, htrace, ?_, hmin⟩
  intro v hv hLip
  obtain ⟨σ, hσ, htr⟩ := hv
  obtain ⟨vj, hvj, ht⟩ := hdensity σ hσ v ⟨htr, hLip⟩
  exact ge_of_tendsto ht
    (Eventually.of_forall fun j => hmin (vj j) (hvj j).1 (hvj j).2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_isMorreyDisk_of_hasMinimalConformalSpanningDisk_of_areaDenseForWeakTraces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_isMorreyDisk_of_hasMinimalConformalSpanningDisk_of_areaDenseForWeakTraces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_isMorreyDisk_of_hasMinimalConformalSpanningDisk_of_areaDenseForWeakTraces ``Submission.DifferentialGeometry.Geometry.exists_isMorreyDisk_of_hasMinimalConformalSpanningDisk_of_areaDenseForWeakTraces

theorem exists_morrey_disk_of_minimalConformalSpanningDisk_of_areaDenseForWeakTraces
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    (h : HasMinimalConformalSpanningDisk g γ)
    (hdensity : SmoothDisksAreAreaDenseForWeakTracesAt g γ) :
    ∃ u : C(closedDisk, M), IsMorreyDisk g γ u :=
  exists_isMorreyDisk_of_hasMinimalConformalSpanningDisk_of_areaDenseForWeakTraces h hdensity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_morrey_disk_of_minimalConformalSpanningDisk_of_areaDenseForWeakTraces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_morrey_disk_of_minimalConformalSpanningDisk_of_areaDenseForWeakTraces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_morrey_disk_of_minimalConformalSpanningDisk_of_areaDenseForWeakTraces ``Submission.DifferentialGeometry.Geometry.exists_morrey_disk_of_minimalConformalSpanningDisk_of_areaDenseForWeakTraces

theorem hasMinimalConformalSpanningDisk_const (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q : M) :
    HasMinimalConformalSpanningDisk g (ContinuousMap.const loopCircle q) :=
  HasMinimalConformalSpanningDisk.of_isMorreyDisk (isMorreyDisk_const g q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.hasMinimalConformalSpanningDisk_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.hasMinimalConformalSpanningDisk_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.hasMinimalConformalSpanningDisk_const ``Submission.DifferentialGeometry.Geometry.hasMinimalConformalSpanningDisk_const

theorem exists_isMorreyDisk_const_of_subsingleton (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    [Subsingleton M] (q : M) :
    ∃ u : C(closedDisk, M), IsMorreyDisk g (ContinuousMap.const loopCircle q) u :=
  exists_isMorreyDisk_of_hasMinimalConformalSpanningDisk_of_areaDenseForWeakTraces
    (hasMinimalConformalSpanningDisk_const g q)
    (smoothDisksAreAreaDenseForWeakTracesAt_of_subsingleton g _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_isMorreyDisk_const_of_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_isMorreyDisk_const_of_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_isMorreyDisk_const_of_subsingleton ``Submission.DifferentialGeometry.Geometry.exists_isMorreyDisk_const_of_subsingleton

private theorem surjective_of_continuous_of_add_one (ψ : ℝ → ℝ) (hcont : Continuous ψ)
    (hper : ∀ t, ψ (t + 1) = ψ t + 1) : Function.Surjective ψ := by
  have hstep : ∀ n : ℕ, ∀ t : ℝ, ψ (t + n) = ψ t + n := by
    intro n
    induction n with
    | zero => intro t; simp
    | succ n ih =>
      intro t
      rw [show (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 by push_cast; ring]
      rw [← add_assoc, hper, ih]
      ring
  have hint : ∀ n : ℤ, ψ (n : ℝ) = ψ 0 + n := by
    intro n
    cases n with
    | ofNat m => simpa using hstep m 0
    | negSucc m =>
      have hcast : ((Int.negSucc m : ℤ) : ℝ) = -((m : ℝ) + 1) := by push_cast; ring
      have hcast' : (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      have hstepm := hstep (m + 1) (-((m : ℝ) + 1))
      have h0 : -((m : ℝ) + 1) + (((m + 1 : ℕ)) : ℝ) = 0 := by push_cast; ring
      rw [h0, hcast'] at hstepm
      rw [hcast]
      linarith
  intro y
  have hmem : ∃ n : ℤ, ψ 0 + (n : ℝ) ≤ y ∧ y ≤ ψ 0 + (n : ℝ) + 1 := by
    refine ⟨⌊y - ψ 0⌋, ?_, ?_⟩
    · have := Int.floor_le (y - ψ 0); linarith
    · have := Int.lt_floor_add_one (y - ψ 0); linarith
  obtain ⟨n, hn1, hn2⟩ := hmem
  have hb1 : ψ (n : ℝ) ≤ y := by rw [hint n]; exact hn1
  have hb2 : y ≤ ψ ((n : ℝ) + 1) := by rw [hper, hint n]; exact hn2
  obtain ⟨s, -, hs⟩ := (intermediate_value_Icc (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)
    hcont.continuousOn) ⟨hb1, hb2⟩
  exact ⟨s, hs⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.surjective_of_continuous_of_add_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.surjective_of_continuous_of_add_one target :: scope.openDecls } }

theorem IsWeaklyMonotoneOnce.surjective {σ : C(loopCircle, loopCircle)}
    (hσ : IsWeaklyMonotoneOnce σ) : Function.Surjective σ := by
  obtain ⟨ψ, hψc, hψl, hinc⟩ := hσ
  have hsurjψ : Function.Surjective ψ := by
    rcases hinc with ⟨-, hper⟩ | ⟨-, hper⟩
    · exact surjective_of_continuous_of_add_one ψ hψc hper
    · have hsurjm : Function.Surjective (fun t : ℝ => ψ (-t)) :=
        surjective_of_continuous_of_add_one (fun t : ℝ => ψ (-t))
          (hψc.comp _root_.ContinuousNeg.continuous_neg) (fun t => by
            have h1 : ψ ((-t - 1) + 1) = ψ (-t - 1) - 1 := hper (-t - 1)
            have h2 : (-t - 1) + 1 = -t := by ring
            rw [h2] at h1
            have h3 : -(t + 1) = -t - 1 := by ring
            rw [h3]
            linarith)
      intro y
      obtain ⟨s, hs⟩ := hsurjm y
      exact ⟨-s, by simpa using hs⟩
  intro y
  obtain ⟨t, ht⟩ : ∃ t : ℝ, (t : loopCircle) = y := Quotient.exists_rep y
  obtain ⟨s, hs⟩ := hsurjψ t
  exact ⟨(s : loopCircle), by rw [← hψl s, hs]; exact ht⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.IsWeaklyMonotoneOnce.surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.IsWeaklyMonotoneOnce.surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.IsWeaklyMonotoneOnce.surjective ``Submission.DifferentialGeometry.Geometry.IsWeaklyMonotoneOnce.surjective

theorem isMorreyDisk_const_iff {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {q : M} :
    IsMorreyDisk g γ (ContinuousMap.const closedDisk q) ↔
      γ = ContinuousMap.const loopCircle q := by
  constructor
  · intro h
    obtain ⟨σ, hσ, htr⟩ := h.trace
    have hconst : ∀ y : loopCircle, γ y = q := by
      intro y
      obtain ⟨s, hs⟩ := hσ.surjective y
      have h1 : γ (σ s) = q := by
        have h2 := congrArg (fun f : freeLoop M => f s) htr
        simpa only [diskTrace, ContinuousMap.comp_apply, ContinuousMap.const_apply] using h2.symm
      rw [← hs]
      exact h1
    exact ContinuousMap.ext hconst
  · intro h
    rw [h]
    exact isMorreyDisk_const g q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.isMorreyDisk_const_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.isMorreyDisk_const_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.isMorreyDisk_const_iff ``Submission.DifferentialGeometry.Geometry.isMorreyDisk_const_iff

theorem not_isMorreyDisk_const_of_isSmoothEmbeddedLoop {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} (hγ : IsSmoothEmbeddedLoop (E := E) γ) (q : M) :
    ¬ IsMorreyDisk g γ (ContinuousMap.const closedDisk q) := by
  intro h
  have hc : γ = ContinuousMap.const loopCircle q := isMorreyDisk_const_iff.mp h
  have hfun : (fun t : ℝ => γ (t : loopCircle)) = fun _ => q := by
    rw [hc]
    rfl
  have hzero : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => γ (t : loopCircle)) 0 1 =
      0 := by
    rw [hfun]
    have h0 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun _ : ℝ => q) (0 : ℝ) =
        (0 : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, E) q) := mfderiv_const
    rw [h0]
    rfl
  exact hγ.immersed 0 hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.not_isMorreyDisk_const_of_isSmoothEmbeddedLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.not_isMorreyDisk_const_of_isSmoothEmbeddedLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.not_isMorreyDisk_const_of_isSmoothEmbeddedLoop ``Submission.DifferentialGeometry.Geometry.not_isMorreyDisk_const_of_isSmoothEmbeddedLoop

end DifferentialGeometry.Geometry
