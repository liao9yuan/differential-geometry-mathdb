import Submission.DifferentialGeometry.Geometry.Geodesic.Equation.Basic
import Submission.DifferentialGeometry.Geometry.Geodesic.Local.Existence
import Submission.DifferentialGeometry.Geometry.Geodesic.Flow.Uniqueness
import Submission.DifferentialGeometry.Geometry.Comparison.Variation.Curve.PathLength

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

def IsGeodesicOnWithInitial
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (s : Set ℝ)
    (p : M) (v : TangentSpace I p) : Prop :=
  ∃ f : ℝ → TangentBundle I M,
    (∀ t, (f t).proj = γ t) ∧
    f 0 = (⟨p, v⟩ : TangentBundle I M) ∧
    IsMIntegralCurveOn f (geodesicVectorField (I := I) g) s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOnWithInitial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOnWithInitial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOnWithInitial ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOnWithInitial

omit [NeZero (Module.finrank ℝ E)] in
lemma IsGeodesicOnWithInitial.isGeodesicAt
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {s : Set ℝ}
    {p : M} {v : TangentSpace I p} {t : ℝ}
    (hγ : IsGeodesicOnWithInitial (I := I) g γ s p v) (ht : s ∈ 𝓝 t) :
    IsGeodesicAt (I := I) g γ t := by
  obtain ⟨f, hproj, _, hf⟩ := hγ
  have hsrc : (f t).proj ∈ (chartAt H (γ t)).source := by
    rw [hproj t]
    exact mem_chart_source H (γ t)
  exact ⟨γ t, f, hproj, hsrc,
    (isMIntegralCurveAt_geodesicVectorFieldChart_iff g (γ t) hsrc).mpr
      (hf.isMIntegralCurveAt ht)⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOnWithInitial
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOnWithInitial.isGeodesicAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOnWithInitial.isGeodesicAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOnWithInitial.isGeodesicAt ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOnWithInitial.isGeodesicAt

omit [NeZero (Module.finrank ℝ E)] in
lemma IsGeodesicOnWithInitial.start_eq
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {s : Set ℝ}
    {p : M} {v : TangentSpace I p}
    (hγ : IsGeodesicOnWithInitial (I := I) g γ s p v) :
    γ 0 = p := by
  obtain ⟨f, hproj, hf0, _⟩ := hγ
  have h := hproj 0
  simp [hf0] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOnWithInitial.start_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOnWithInitial.start_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOnWithInitial.start_eq ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOnWithInitial.start_eq

omit [NeZero (Module.finrank ℝ E)] in
lemma IsGeodesicOnWithInitial.mono
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {s s' : Set ℝ}
    {p : M} {v : TangentSpace I p}
    (hγ : IsGeodesicOnWithInitial (I := I) g γ s p v) (hs : s' ⊆ s) :
    IsGeodesicOnWithInitial (I := I) g γ s' p v := by
  obtain ⟨f, hproj, hf0, hf⟩ := hγ
  exact ⟨f, hproj, hf0, hf.mono hs⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOnWithInitial.mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOnWithInitial.mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOnWithInitial.mono ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOnWithInitial.mono

def HasGeodesicAt
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    (t : ℝ) : Prop :=
  ∃ γ : ℝ → M, ∃ J : Set ℝ,
    IsOpen J ∧ IsPreconnected J ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      IsGeodesicOnWithInitial (I := I) g γ J p v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.HasGeodesicAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.HasGeodesicAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.HasGeodesicAt ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.HasGeodesicAt

def maximalGeodesicInterval
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    Set ℝ :=
  {t : ℝ | HasGeodesicAt (I := I) g p v t}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesicInterval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesicInterval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesicInterval ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesicInterval

omit [NeZero (Module.finrank ℝ E)] in
lemma mem_maximalGeodesicInterval_iff
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} :
    t ∈ maximalGeodesicInterval (I := I) g p v ↔
      HasGeodesicAt (I := I) g p v t :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.mem_maximalGeodesicInterval_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.mem_maximalGeodesicInterval_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.mem_maximalGeodesicInterval_iff ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.mem_maximalGeodesicInterval_iff

omit [NeZero (Module.finrank ℝ E)] in
theorem maximalGeodesicInterval_isOpen
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    IsOpen (maximalGeodesicInterval (I := I) g p v) := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  obtain ⟨γ, J, hJ, hJ_conn, h0, ht_in, hγ⟩ := ht
  refine Filter.mem_of_superset (hJ.mem_nhds ht_in) ?_
  intro t' ht'
  exact ⟨γ, J, hJ, hJ_conn, h0, ht', hγ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesicInterval_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesicInterval_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesicInterval_isOpen ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesicInterval_isOpen

section LocalExistence

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
lemma hasGeodesicAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    HasGeodesicAt (I := I) g p v 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨f, hf0, hf⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
      (I := I.tangent) (M := TangentBundle I M)
      (v := geodesicVectorField (I := I) g)
      (t₀ := (0 : ℝ)) (x₀ := (⟨p, v⟩ : TangentBundle I M))
      ((contMDiff_geodesicVectorField g).contMDiffAt.of_le (by norm_num))
  rw [isMIntegralCurveAt_iff'] at hf
  obtain ⟨ε, hε, hf_on⟩ := hf
  refine ⟨projectCurve (I := I) f, Metric.ball (0 : ℝ) ε,
    Metric.isOpen_ball, ?_, Metric.mem_ball_self hε, Metric.mem_ball_self hε, ?_⟩
  · exact (convex_ball (0 : ℝ) ε).isPreconnected
  exact ⟨f, fun _ => rfl, hf0, hf_on⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.hasGeodesicAt_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.hasGeodesicAt_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.hasGeodesicAt_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.hasGeodesicAt_zero

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem zero_mem_maximalGeodesicInterval
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    (0 : ℝ) ∈ maximalGeodesicInterval (I := I) g p v :=
  hasGeodesicAt_zero (I := I) g p v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.zero_mem_maximalGeodesicInterval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.zero_mem_maximalGeodesicInterval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.zero_mem_maximalGeodesicInterval ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.zero_mem_maximalGeodesicInterval

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem maximalGeodesicInterval_nonempty
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    (maximalGeodesicInterval (I := I) g p v).Nonempty :=
  ⟨0, zero_mem_maximalGeodesicInterval (I := I) g p v⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesicInterval_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesicInterval_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesicInterval_nonempty ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesicInterval_nonempty

end LocalExistence

section MaximalGeodesicDefinition

variable [I.Boundaryless] [CompleteSpace E]

def maximalGeodesicChosenCurve
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {t : ℝ} (h : HasGeodesicAt (I := I) g p v t) :
    ℝ → M :=
  Classical.choose h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesicChosenCurve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesicChosenCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesicChosenCurve ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesicChosenCurve

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [CompleteSpace E] in
lemma maximalGeodesicChosenCurve_spec
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {t : ℝ} (h : HasGeodesicAt (I := I) g p v t) :
    ∃ J : Set ℝ, IsOpen J ∧ IsPreconnected J ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      IsGeodesicOnWithInitial (I := I) g
        (maximalGeodesicChosenCurve (I := I) g p v h) J p v :=
  Classical.choose_spec h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesicChosenCurve_spec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesicChosenCurve_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesicChosenCurve_spec ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesicChosenCurve_spec

def maximalGeodesic
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    (t : ℝ) : M :=
  letI : Decidable (HasGeodesicAt (I := I) g p v t) := Classical.dec _
  if h : HasGeodesicAt (I := I) g p v t then
    maximalGeodesicChosenCurve (I := I) g p v h t
  else p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [CompleteSpace E] in
lemma maximalGeodesic_of_not_mem
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} (ht : t ∉ maximalGeodesicInterval (I := I) g p v) :
    maximalGeodesic (I := I) g p v t = p := by
  unfold maximalGeodesic
  let : Decidable (HasGeodesicAt (I := I) g p v t) := Classical.dec _
  exact dif_neg ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_of_not_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_of_not_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_of_not_mem ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_of_not_mem

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [CompleteSpace E] in
lemma maximalGeodesic_of_mem
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} (h : t ∈ maximalGeodesicInterval (I := I) g p v) :
    maximalGeodesic (I := I) g p v t =
      maximalGeodesicChosenCurve (I := I) g p v h t := by
  unfold maximalGeodesic
  let : Decidable (HasGeodesicAt (I := I) g p v t) := Classical.dec _
  exact dif_pos h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_of_mem ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_of_mem

end MaximalGeodesicDefinition

section MaximalGeodesicValue

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem maximalGeodesic_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    maximalGeodesic (I := I) g p v 0 = p := by
  have h0 := zero_mem_maximalGeodesicInterval (I := I) g p v
  rw [maximalGeodesic_of_mem (I := I) (g := g) (p := p) (v := v) h0]
  obtain ⟨_J, _hJ, _hJ_conn, _h0J, _h0J', hγ⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p v h0
  exact hγ.start_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_zero

end MaximalGeodesicValue

section MaximalGeodesicAtTime

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem exists_isGeodesicAt_of_mem_maximalGeodesicInterval
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} (h : t ∈ maximalGeodesicInterval (I := I) g p v) :
    ∃ (γ : ℝ → M) (J : Set ℝ), IsOpen J ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
      IsGeodesicOnWithInitial (I := I) g γ J p v ∧
      IsGeodesicAt (I := I) g γ t := by
  obtain ⟨γ, J, hJ, _hJ_conn, h0, ht, hγ⟩ := h
  refine ⟨γ, J, hJ, h0, ht, hγ, ?_⟩
  exact hγ.isGeodesicAt (hJ.mem_nhds ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.exists_isGeodesicAt_of_mem_maximalGeodesicInterval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.exists_isGeodesicAt_of_mem_maximalGeodesicInterval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.exists_isGeodesicAt_of_mem_maximalGeodesicInterval ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.exists_isGeodesicAt_of_mem_maximalGeodesicInterval

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem exists_isGeodesicAt_zero_of_mem_maximalGeodesicInterval
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} (h : t ∈ maximalGeodesicInterval (I := I) g p v) :
    ∃ γ : ℝ → M, γ 0 = p ∧ IsGeodesicAt (I := I) g γ 0 ∧
      IsGeodesicAt (I := I) g γ t := by
  obtain ⟨γ, J, hJ, h0, ht, hγ_initial, hγ_at⟩ :=
    exists_isGeodesicAt_of_mem_maximalGeodesicInterval (I := I) h
  refine ⟨γ, hγ_initial.start_eq, ?_, hγ_at⟩
  exact hγ_initial.isGeodesicAt (hJ.mem_nhds h0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.exists_isGeodesicAt_zero_of_mem_maximalGeodesicInterval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.exists_isGeodesicAt_zero_of_mem_maximalGeodesicInterval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.exists_isGeodesicAt_zero_of_mem_maximalGeodesicInterval ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.exists_isGeodesicAt_zero_of_mem_maximalGeodesicInterval

end MaximalGeodesicAtTime

section MaximalGeodesicMain

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem maximalGeodesic_properties
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    let I_max := maximalGeodesicInterval (I := I) g p v
    let γ_max := maximalGeodesic (I := I) g p v
    IsOpen I_max ∧ (0 : ℝ) ∈ I_max ∧ γ_max 0 = p ∧
      (∀ t ∉ I_max, γ_max t = p) ∧
      (∀ t ∈ I_max, ∃ γ : ℝ → M, γ 0 = p ∧
        IsGeodesicAt (I := I) g γ 0 ∧ IsGeodesicAt (I := I) g γ t) := by
  refine ⟨maximalGeodesicInterval_isOpen (I := I) g p v,
    zero_mem_maximalGeodesicInterval (I := I) g p v,
    maximalGeodesic_zero (I := I) g p v, ?_, ?_⟩
  · intro t ht
    exact maximalGeodesic_of_not_mem (I := I) ht
  · intro t ht
    exact exists_isGeodesicAt_zero_of_mem_maximalGeodesicInterval (I := I) ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_properties then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_properties"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_properties ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_properties

end MaximalGeodesicMain

section BridgeLemmas

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [CompleteSpace E] in
lemma isGeodesic_iff_isGeodesicOn_univ
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} :
    IsGeodesic (I := I) g γ ↔ IsGeodesicOn (I := I) g γ (Set.univ : Set ℝ) := by
  constructor
  · intro hγ
    exact hγ.isGeodesicOn _
  · intro hγ t
    exact hγ t (Set.mem_univ t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.isGeodesic_iff_isGeodesicOn_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.isGeodesic_iff_isGeodesicOn_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.isGeodesic_iff_isGeodesicOn_univ ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.isGeodesic_iff_isGeodesicOn_univ

end BridgeLemmas


end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
