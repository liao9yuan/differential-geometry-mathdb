import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.RealizedConnectors
import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.Smooth
import Submission.DifferentialGeometry.Geometry.Comparison.HopfRinow.Basic
import Submission.DifferentialGeometry.Geometry.Comparison.Variation.Curve.SpeedDerivative
import Submission.DifferentialGeometry.Geometry.Geodesic.Chart.Regularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Function _root_.Filter
open scoped _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Toponogov

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]

structure SmoothRepresentative
    {g : SmoothRiemannianMetric I M} {p q : M}
    (c : RealizedMinimizingConnector (I := I) g p q) where
  curve : ℝ → M
  smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ curve
  agrees : Set.EqOn curve c.curve (Set.Icc 0 c.length)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.SmoothRepresentative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.SmoothRepresentative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.SmoothRepresentative ``Submission.DifferentialGeometry.Toponogov.SmoothRepresentative

structure SmoothNeighborhoodExtension
    {g : SmoothRiemannianMetric I M} {p q : M}
    (c : RealizedMinimizingConnector (I := I) g p q) where
  curve : ℝ → M
  margin : ℝ
  margin_pos : 0 < margin
  smoothOn : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ curve
    (Set.Ioo (-margin) (c.length + margin))
  agrees : Set.EqOn curve c.curve (Set.Icc 0 c.length)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.SmoothNeighborhoodExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.SmoothNeighborhoodExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.SmoothNeighborhoodExtension ``Submission.DifferentialGeometry.Toponogov.SmoothNeighborhoodExtension

structure SmoothGeodesicRepresentative
    {g : SmoothRiemannianMetric I M} {p q : M}
    (c : RealizedMinimizingConnector (I := I) g p q) where
  curve : ℝ → M
  smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ curve
  agrees : Set.EqOn curve c.curve (Set.Icc 0 c.length)
  geodesicOn : IsGeodesicOn (I := I) g curve (Set.Icc 0 c.length)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative ``Submission.DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative


structure SmoothGeodesicNeighborhoodExtension
    {g : SmoothRiemannianMetric I M} {p q : M}
    (c : RealizedMinimizingConnector (I := I) g p q) where
  curve : ℝ → M
  margin : ℝ
  margin_pos : 0 < margin
  smoothOn : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ curve
    (Set.Ioo (-margin) (c.length + margin))
  geodesicOn : IsGeodesicOn (I := I) g curve
    (Set.Ioo (-margin) (c.length + margin))
  agrees : Set.EqOn curve c.curve (Set.Icc 0 c.length)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.SmoothGeodesicNeighborhoodExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.SmoothGeodesicNeighborhoodExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.SmoothGeodesicNeighborhoodExtension ``Submission.DifferentialGeometry.Toponogov.SmoothGeodesicNeighborhoodExtension


def SmoothGeodesicRepresentative.toSmoothRepresentative
    {g : SmoothRiemannianMetric I M} {p q : M}
    {c : RealizedMinimizingConnector (I := I) g p q}
    (r : SmoothGeodesicRepresentative c) : SmoothRepresentative c where
  curve := r.curve
  smooth := r.smooth
  agrees := r.agrees

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative.toSmoothRepresentative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative.toSmoothRepresentative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative.toSmoothRepresentative ``Submission.DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative.toSmoothRepresentative


def SmoothGeodesicNeighborhoodExtension.toSmoothNeighborhoodExtension
    {g : SmoothRiemannianMetric I M} {p q : M}
    {c : RealizedMinimizingConnector (I := I) g p q}
    (e : SmoothGeodesicNeighborhoodExtension c) :
    SmoothNeighborhoodExtension c where
  curve := e.curve
  margin := e.margin
  margin_pos := e.margin_pos
  smoothOn := e.smoothOn
  agrees := e.agrees

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Toponogov.SmoothGeodesicNeighborhoodExtension
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.SmoothGeodesicNeighborhoodExtension.toSmoothNeighborhoodExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.SmoothGeodesicNeighborhoodExtension.toSmoothNeighborhoodExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.SmoothGeodesicNeighborhoodExtension.toSmoothNeighborhoodExtension ``Submission.DifferentialGeometry.Toponogov.SmoothGeodesicNeighborhoodExtension.toSmoothNeighborhoodExtension

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem SmoothRepresentative.source
    {g : SmoothRiemannianMetric I M} {p q : M}
    {c : RealizedMinimizingConnector (I := I) g p q}
    (r : SmoothRepresentative c) : r.curve 0 = p := by
  exact (r.agrees ⟨le_rfl, c.length_nonneg⟩).trans c.source

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Toponogov.SmoothRepresentative
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.SmoothRepresentative.source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.SmoothRepresentative.source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.SmoothRepresentative.source ``Submission.DifferentialGeometry.Toponogov.SmoothRepresentative.source

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem SmoothRepresentative.target
    {g : SmoothRiemannianMetric I M} {p q : M}
    {c : RealizedMinimizingConnector (I := I) g p q}
    (r : SmoothRepresentative c) : r.curve c.length = q := by
  exact (r.agrees ⟨c.length_nonneg, le_rfl⟩).trans c.target

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.SmoothRepresentative.target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.SmoothRepresentative.target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.SmoothRepresentative.target ``Submission.DifferentialGeometry.Toponogov.SmoothRepresentative.target

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem SmoothRepresentative.eventuallyEq_at_of_mem_Ioo
    {g : SmoothRiemannianMetric I M} {p q : M}
    {c : RealizedMinimizingConnector (I := I) g p q}
    (r : SmoothRepresentative c) {t : ℝ} (ht : t ∈ Set.Ioo 0 c.length) :
    r.curve =ᶠ[nhds t] c.curve := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact r.agrees ⟨hs.1.le, hs.2.le⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.SmoothRepresentative.eventuallyEq_at_of_mem_Ioo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.SmoothRepresentative.eventuallyEq_at_of_mem_Ioo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.SmoothRepresentative.eventuallyEq_at_of_mem_Ioo ``Submission.DifferentialGeometry.Toponogov.SmoothRepresentative.eventuallyEq_at_of_mem_Ioo

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem SmoothRepresentative.mfderiv_eq_of_mem_Ioo
    {g : SmoothRiemannianMetric I M} {p q : M}
    {c : RealizedMinimizingConnector (I := I) g p q}
    (r : SmoothRepresentative c) {t : ℝ} (ht : t ∈ Set.Ioo 0 c.length) :
    mfderiv 𝓘(ℝ, ℝ) I r.curve t =
      mfderiv 𝓘(ℝ, ℝ) I c.curve t :=
  (r.eventuallyEq_at_of_mem_Ioo ht).mfderiv_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.SmoothRepresentative.mfderiv_eq_of_mem_Ioo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.SmoothRepresentative.mfderiv_eq_of_mem_Ioo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.SmoothRepresentative.mfderiv_eq_of_mem_Ioo ``Submission.DifferentialGeometry.Toponogov.SmoothRepresentative.mfderiv_eq_of_mem_Ioo

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem SmoothRepresentative.isGeodesicOn_Ioo
    {g : SmoothRiemannianMetric I M} {p q : M}
    {c : RealizedMinimizingConnector (I := I) g p q}
    (r : SmoothRepresentative c) :
    IsGeodesicOn (I := I) g r.curve (Set.Ioo 0 c.length) := by
  intro t ht
  have heq := r.eventuallyEq_at_of_mem_Ioo ht
  exact HasGeodesicEquationAt.congr_of_eventuallyEq_at
    heq.self_of_nhds heq (c.geodesic t ⟨ht.1.le, ht.2.le⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.SmoothRepresentative.isGeodesicOn_Ioo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.SmoothRepresentative.isGeodesicOn_Ioo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.SmoothRepresentative.isGeodesicOn_Ioo ``Submission.DifferentialGeometry.Toponogov.SmoothRepresentative.isGeodesicOn_Ioo

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem SmoothRepresentative.unitSpeed
    {g : SmoothRiemannianMetric I M} {p q : M}
    {c : RealizedMinimizingConnector (I := I) g p q}
    (r : SmoothRepresentative c) {t : ℝ} (ht : t ∈ Set.Ioo 0 c.length) :
    g.inner (r.curve t) (mfderiv 𝓘(ℝ, ℝ) I r.curve t 1)
        (mfderiv 𝓘(ℝ, ℝ) I r.curve t 1) = 1 := by
  have heq := r.eventuallyEq_at_of_mem_Ioo ht
  rw [show r.curve t = c.curve t from heq.self_of_nhds]
  simpa only [heq.mfderiv_eq] using c.unitSpeed t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.SmoothRepresentative.unitSpeed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.SmoothRepresentative.unitSpeed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.SmoothRepresentative.unitSpeed ``Submission.DifferentialGeometry.Toponogov.SmoothRepresentative.unitSpeed

def SmoothRepresentative.ofConnector
    {g : SmoothRiemannianMetric I M} {p q : M}
    (c : RealizedMinimizingConnector (I := I) g p q)
    (h : ContMDiff 𝓘(ℝ, ℝ) I ∞ c.curve) : SmoothRepresentative c where
  curve := c.curve
  smooth := h
  agrees := fun _ _ ↦ rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.SmoothRepresentative.ofConnector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.SmoothRepresentative.ofConnector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.SmoothRepresentative.ofConnector ``Submission.DifferentialGeometry.Toponogov.SmoothRepresentative.ofConnector

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem exists_smoothRepresentative_of_length_eq_zero
    {g : SmoothRiemannianMetric I M} {p q : M}
    (c : RealizedMinimizingConnector (I := I) g p q)
    (hL : c.length = 0) : Nonempty (SmoothRepresentative c) := by
  refine ⟨⟨fun _ ↦ p, contMDiff_const, ?_⟩⟩
  intro t ht
  exact (c.constant_on_of_length_eq_zero hL t ht).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.exists_smoothRepresentative_of_length_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.exists_smoothRepresentative_of_length_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.exists_smoothRepresentative_of_length_eq_zero ``Submission.DifferentialGeometry.Toponogov.exists_smoothRepresentative_of_length_eq_zero

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem SmoothNeighborhoodExtension.exists_smoothRepresentative
    {g : SmoothRiemannianMetric I M} {p q : M}
    {c : RealizedMinimizingConnector (I := I) g p q}
    (e : SmoothNeighborhoodExtension c) :
    Nonempty (SmoothRepresentative c) := by
  let A : ℝ := -e.margin / 2
  let D : ℝ := c.length + e.margin / 2
  let ε : ℝ := e.margin / 4
  have hAD : A < D := by
    dsimp only [A, D]
    linarith [c.length_nonneg, e.margin_pos]
  have hε : 0 < ε := by
    dsimp only [ε]
    linarith [e.margin_pos]
  obtain ⟨ρ, hρsmooth, hρid, _hρderiv, hρrange⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp A D ε hAD hε
  have hρrange' : ∀ t : ℝ,
      ρ t ∈ Set.Ioo (-e.margin) (c.length + e.margin) := by
    intro t
    have ht := hρrange t
    dsimp only [A, D, ε] at ht
    constructor
    · linarith [ht.1, e.margin_pos]
    · linarith [ht.2, e.margin_pos]
  have hcomp : ContMDiff 𝓘(ℝ, ℝ) I ∞ (e.curve ∘ ρ) :=
    e.smoothOn.comp_contMDiff hρsmooth.contMDiff hρrange'
  refine ⟨⟨e.curve ∘ ρ, hcomp, ?_⟩⟩
  intro t ht
  have htAD : t ∈ Set.Icc A D := by
    dsimp only [A, D]
    constructor <;> linarith [ht.1, ht.2, e.margin_pos]
  change e.curve (ρ t) = c.curve t
  rw [hρid t htAD]
  exact e.agrees ht

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Toponogov.SmoothNeighborhoodExtension
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.SmoothNeighborhoodExtension.exists_smoothRepresentative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.SmoothNeighborhoodExtension.exists_smoothRepresentative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.SmoothNeighborhoodExtension.exists_smoothRepresentative ``Submission.DifferentialGeometry.Toponogov.SmoothNeighborhoodExtension.exists_smoothRepresentative

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem SmoothGeodesicNeighborhoodExtension.exists_smoothGeodesicRepresentative
    {g : SmoothRiemannianMetric I M} {p q : M}
    {c : RealizedMinimizingConnector (I := I) g p q}
    (e : SmoothGeodesicNeighborhoodExtension c) :
    Nonempty (SmoothGeodesicRepresentative c) := by
  let A : ℝ := -e.margin / 2
  let D : ℝ := c.length + e.margin / 2
  let ε : ℝ := e.margin / 4
  have hAD : A < D := by
    dsimp only [A, D]
    linarith [c.length_nonneg, e.margin_pos]
  have hε : 0 < ε := by
    dsimp only [ε]
    linarith [e.margin_pos]
  obtain ⟨ρ, hρsmooth, hρid, _hρderiv, hρrange⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp A D ε hAD hε
  have hρrange' : ∀ t : ℝ,
      ρ t ∈ Set.Ioo (-e.margin) (c.length + e.margin) := by
    intro t
    have ht := hρrange t
    dsimp only [A, D, ε] at ht
    constructor
    · linarith [ht.1, e.margin_pos]
    · linarith [ht.2, e.margin_pos]
  have hcomp : ContMDiff 𝓘(ℝ, ℝ) I ∞ (e.curve ∘ ρ) :=
    e.smoothOn.comp_contMDiff hρsmooth.contMDiff hρrange'
  have hagrees : Set.EqOn (e.curve ∘ ρ) c.curve
      (Set.Icc 0 c.length) := by
    intro t ht
    have htAD : t ∈ Set.Icc A D := by
      dsimp only [A, D]
      constructor <;> linarith [ht.1, ht.2, e.margin_pos]
    change e.curve (ρ t) = c.curve t
    rw [hρid t htAD]
    exact e.agrees ht
  refine ⟨⟨e.curve ∘ ρ, hcomp, hagrees, ?_⟩⟩
  intro t ht
  have htAD : t ∈ Set.Ioo A D := by
    dsimp only [A, D]
    constructor <;> linarith [ht.1, ht.2, e.margin_pos]
  have heq : (e.curve ∘ ρ) =ᶠ[nhds t] e.curve := by
    filter_upwards [isOpen_Ioo.mem_nhds htAD] with s hs
    change e.curve (ρ s) = e.curve s
    rw [hρid s ⟨hs.1.le, hs.2.le⟩]
  have htDomain : t ∈ Set.Ioo (-e.margin) (c.length + e.margin) := by
    constructor <;> linarith [ht.1, ht.2, e.margin_pos]
  exact HasGeodesicEquationAt.congr_of_eventuallyEq_at
    heq.self_of_nhds heq (e.geodesicOn t htDomain)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.SmoothGeodesicNeighborhoodExtension.exists_smoothGeodesicRepresentative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.SmoothGeodesicNeighborhoodExtension.exists_smoothGeodesicRepresentative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.SmoothGeodesicNeighborhoodExtension.exists_smoothGeodesicRepresentative ``Submission.DifferentialGeometry.Toponogov.SmoothGeodesicNeighborhoodExtension.exists_smoothGeodesicRepresentative

def SmoothGeodesicRepresentative.toRealizedMinimizingConnector
    {g : SmoothRiemannianMetric I M} {p q : M}
    {c : RealizedMinimizingConnector (I := I) g p q}
    (r : SmoothGeodesicRepresentative c) :
    RealizedMinimizingConnector (I := I) g p q where
  curve := r.curve
  length := c.length
  length_nonneg := c.length_nonneg
  source := (r.agrees ⟨le_rfl, c.length_nonneg⟩).trans c.source
  target := (r.agrees ⟨c.length_nonneg, le_rfl⟩).trans c.target
  smooth := (r.smooth.of_le (by norm_num)).contMDiffOn
  geodesic := r.geodesicOn
  unitSpeed := by
    intro t ht
    exact r.toSmoothRepresentative.unitSpeed ht
  realizes := c.realizes

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative.toRealizedMinimizingConnector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative.toRealizedMinimizingConnector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative.toRealizedMinimizingConnector ``Submission.DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative.toRealizedMinimizingConnector

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem SmoothGeodesicRepresentative.toRealizedMinimizingConnector_agrees
    {g : SmoothRiemannianMetric I M} {p q : M}
    {c : RealizedMinimizingConnector (I := I) g p q}
    (r : SmoothGeodesicRepresentative c) :
    Set.EqOn r.toRealizedMinimizingConnector.curve c.curve
      (Set.Icc 0 c.length) :=
  r.agrees

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative.toRealizedMinimizingConnector_agrees then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative.toRealizedMinimizingConnector_agrees"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative.toRealizedMinimizingConnector_agrees ``Submission.DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative.toRealizedMinimizingConnector_agrees

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem SmoothGeodesicRepresentative.toRealizedMinimizingConnector_smooth_global
    {g : SmoothRiemannianMetric I M} {p q : M}
    {c : RealizedMinimizingConnector (I := I) g p q}
    (r : SmoothGeodesicRepresentative c) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ r.toRealizedMinimizingConnector.curve :=
  r.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative.toRealizedMinimizingConnector_smooth_global then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative.toRealizedMinimizingConnector_smooth_global"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative.toRealizedMinimizingConnector_smooth_global ``Submission.DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative.toRealizedMinimizingConnector_smooth_global

def SmoothRepresentative.toNeighborhoodExtension
    {g : SmoothRiemannianMetric I M} {p q : M}
    {c : RealizedMinimizingConnector (I := I) g p q}
    (r : SmoothRepresentative c) : SmoothNeighborhoodExtension c where
  curve := r.curve
  margin := 1
  margin_pos := by norm_num
  smoothOn := r.smooth.contMDiffOn
  agrees := r.agrees

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.SmoothRepresentative.toNeighborhoodExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.SmoothRepresentative.toNeighborhoodExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.SmoothRepresentative.toNeighborhoodExtension ``Submission.DifferentialGeometry.Toponogov.SmoothRepresentative.toNeighborhoodExtension

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem nonempty_smoothRepresentative_iff_neighborhoodExtension
    {g : SmoothRiemannianMetric I M} {p q : M}
    {c : RealizedMinimizingConnector (I := I) g p q} :
    Nonempty (SmoothRepresentative c) ↔
      Nonempty (SmoothNeighborhoodExtension c) := by
  constructor
  · rintro ⟨r⟩
    exact ⟨r.toNeighborhoodExtension⟩
  · rintro ⟨e⟩
    exact e.exists_smoothRepresentative

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.nonempty_smoothRepresentative_iff_neighborhoodExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.nonempty_smoothRepresentative_iff_neighborhoodExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.nonempty_smoothRepresentative_iff_neighborhoodExtension ``Submission.DifferentialGeometry.Toponogov.nonempty_smoothRepresentative_iff_neighborhoodExtension

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem hasEndpointContinuation_of_unitSpeed
    (g : SmoothRiemannianMetric I M) {gamma : ℝ → M} {a b : ℝ}
    (y : M) (hab : a < b)
    (hsmooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Set.Ioo a b))
    (hunit : ∀ t ∈ Set.Ioo a b,
      g.inner (gamma t) (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)
        (mfderiv 𝓘(ℝ, ℝ) I gamma t 1) = 1)
    (hgeo : IsGeodesicOn (I := I) g gamma (Set.Ioo a b))
    (hlim : _root_.Filter.Tendsto gamma (nhdsWithin b (Set.Iio b)) (nhds y)) :
    HasEndpointContinuation (I := I) g gamma b := by
  let : _root_.Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  apply endpointCont_of_lim (I := I) g (c := 1) y hab (by norm_num)
  · exact hsmooth
  · intro t ht
    let v : TangentSpace I (gamma t) :=
      mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ)
    change ‖v‖ₑ ≤ ENNReal.ofReal 1
    have hvnorm :
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner (gamma t) v v)) :=
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) g (gamma t) v
    rw [hvnorm]
    change ENNReal.ofReal (Real.sqrt
      (g.inner (gamma t)
        (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)
        (mfderiv 𝓘(ℝ, ℝ) I gamma t 1))) ≤ ENNReal.ofReal 1
    rw [hunit t ht]
    norm_num
  · intro t ht
    rw [hunit t ht]
    norm_num
  · exact hgeo
  · exact hlim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.hasEndpointContinuation_of_unitSpeed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.hasEndpointContinuation_of_unitSpeed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.hasEndpointContinuation_of_unitSpeed ``Submission.DifferentialGeometry.Toponogov.hasEndpointContinuation_of_unitSpeed

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] in
theorem mfderiv_comp_neg_apply_one
    {gamma : ℝ → M} {t : ℝ}
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma (-t)) :
    mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ gamma (-s)) t 1 =
      -(mfderiv 𝓘(ℝ, ℝ) I gamma (-t) 1) := by
  have hneg : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ ↦ -s)
      t (-ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, ℝ) t)) := by
    exact ((hasMFDerivAt_id (I := 𝓘(ℝ, ℝ)) t).neg).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ gamma (-s)) t
      ((mfderiv 𝓘(ℝ, ℝ) I gamma (-t)).comp
        (-ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, ℝ) t))) :=
    hgamma.hasMFDerivAt.comp t hneg
  rw [hcomp.mfderiv]
  change (mfderiv 𝓘(ℝ, ℝ) I gamma (-t))
    ((-ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, ℝ) t)) 1) =
      -(mfderiv 𝓘(ℝ, ℝ) I gamma (-t) 1)
  rw [neg_apply, ContinuousLinearMap.id_apply]
  exact map_neg (mfderiv 𝓘(ℝ, ℝ) I gamma (-t)) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.mfderiv_comp_neg_apply_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.mfderiv_comp_neg_apply_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.mfderiv_comp_neg_apply_one ``Submission.DifferentialGeometry.Toponogov.mfderiv_comp_neg_apply_one

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem unitSpeed_comp_neg
    (g : SmoothRiemannianMetric I M) {gamma : ℝ → M} {a b t : ℝ}
    (hsmooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Set.Ioo a b))
    (hunit : ∀ s ∈ Set.Ioo a b,
      g.inner (gamma s) (mfderiv 𝓘(ℝ, ℝ) I gamma s 1)
        (mfderiv 𝓘(ℝ, ℝ) I gamma s 1) = 1)
    (ht : -t ∈ Set.Ioo a b) :
    g.inner (gamma (-t))
        (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ gamma (-s)) t 1)
        (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ gamma (-s)) t 1) = 1 := by
  have hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma (-t) :=
    (hsmooth (-t) ht).mdifferentiableWithinAt (by norm_num) |>.mdifferentiableAt
      (isOpen_Ioo.mem_nhds ht)
  rw [mfderiv_comp_neg_apply_one hgamma]
  simpa only [map_neg, neg_apply, neg_neg] using hunit (-t) ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.unitSpeed_comp_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.unitSpeed_comp_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.unitSpeed_comp_neg ``Submission.DifferentialGeometry.Toponogov.unitSpeed_comp_neg

omit [T2Space (TangentBundle I M)] in
theorem RealizedMinimizingConnector.hasEndpointContinuation_comp_neg
    {g : SmoothRiemannianMetric I M} {p q : M}
    (c : RealizedMinimizingConnector (I := I) g p q)
    (hL : 0 < c.length) :
    HasEndpointContinuation (I := I) g (fun t : ℝ ↦ c.curve (-t)) 0 := by
  let gammaRev : ℝ → M := fun t ↦ c.curve (-t)
  have hmapsOpen : _root_.Set.MapsTo (fun t : ℝ ↦ -t) (Set.Ioo (-c.length) 0)
      (Set.Icc 0 c.length) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hsmoothRev : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gammaRev
      (Set.Ioo (-c.length) 0) := by
    exact c.smooth.comp contDiff_neg.contMDiff.contMDiffOn hmapsOpen
  have hunitRev : ∀ t ∈ Set.Ioo (-c.length) 0,
      g.inner (gammaRev t) (mfderiv 𝓘(ℝ, ℝ) I gammaRev t 1)
        (mfderiv 𝓘(ℝ, ℝ) I gammaRev t 1) = 1 := by
    intro t ht
    apply unitSpeed_comp_neg g
      (c.smooth.mono (fun _ hs ↦ ⟨hs.1.le, hs.2.le⟩)) c.unitSpeed
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hgeoRev : IsGeodesicOn (I := I) g gammaRev
      (Set.Ioo (-c.length) 0) := by
    have hcgeo : IsGeodesicOn (I := I) g c.curve (Set.Ioo 0 c.length) :=
      c.geodesic.mono (by
        intro t ht
        exact ⟨ht.1.le, ht.2.le⟩)
    have h := isGeodesicOn_comp_neg (I := I) hcgeo
    exact h.mono (by
      intro t ht
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  have hcontClosed : ContinuousOn gammaRev (Set.Icc (-c.length) 0) := by
    exact c.smooth.continuousOn.comp continuous_neg.continuousOn (by
      intro t ht
      constructor <;> linarith [ht.1, ht.2])
  have hlim : _root_.Filter.Tendsto gammaRev (nhdsWithin 0 (Set.Iio 0))
      (nhds (gammaRev 0)) := by
    have hc' := hcontClosed 0 ⟨by linarith, le_rfl⟩
    apply hc'.mono_left
    intro s hs
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hs ⊢
    obtain ⟨u, hu, hus⟩ := hs
    refine ⟨u ∩ Set.Ioi (-c.length),
      _root_.Filter.inter_mem hu (Ioi_mem_nhds (by linarith)), ?_⟩
    intro t ht
    exact hus ⟨ht.1.1, ⟨ht.1.2.le, ht.2.le⟩⟩
  have hlimP : _root_.Filter.Tendsto gammaRev (nhdsWithin 0 (Set.Iio 0)) (nhds p) := by
    have htarget : nhds (gammaRev 0) = nhds p := by
      apply congrArg nhds
      simpa [gammaRev] using c.source
    exact htarget ▸ hlim
  exact hasEndpointContinuation_of_unitSpeed g p (by linarith)
    hsmoothRev hunitRev hgeoRev hlimP

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.RealizedMinimizingConnector.hasEndpointContinuation_comp_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.RealizedMinimizingConnector.hasEndpointContinuation_comp_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.RealizedMinimizingConnector.hasEndpointContinuation_comp_neg ``Submission.DifferentialGeometry.Toponogov.RealizedMinimizingConnector.hasEndpointContinuation_comp_neg

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem hasEndpointContinuation_congr_left
    (g : SmoothRiemannianMetric I M) {gamma gamma' : ℝ → M} {b : ℝ}
    (h : HasEndpointContinuation (I := I) g gamma b)
    (heq : gamma' =ᶠ[nhdsWithin b (Set.Iio b)] gamma) :
    HasEndpointContinuation (I := I) g gamma' b := by
  obtain ⟨eta, delta, hdelta, hgeo, hmdiff, hmatch⟩ := h
  exact ⟨eta, delta, hdelta, hgeo, hmdiff, heq.trans hmatch⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.hasEndpointContinuation_congr_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.hasEndpointContinuation_congr_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.hasEndpointContinuation_congr_left ``Submission.DifferentialGeometry.Toponogov.hasEndpointContinuation_congr_left

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem RealizedMinimizingConnector.exists_smoothGeodesicNeighborhoodExtension
    {g : SmoothRiemannianMetric I M} {p q : M}
    (c : RealizedMinimizingConnector (I := I) g p q) :
    Nonempty (SmoothGeodesicNeighborhoodExtension c) := by
  rcases eq_or_lt_of_le c.length_nonneg with hzero | hL
  · refine ⟨⟨fun _ ↦ p, 1, by norm_num, contMDiff_const.contMDiffOn,
        (isGeodesic_const (I := I) g p).isGeodesicOn _, ?_⟩⟩
    intro t ht
    exact (c.constant_on_of_length_eq_zero hzero.symm t ht).symm
  let gammaRev : ℝ → M := fun t ↦ c.curve (-t)
  have hrevSmooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gammaRev
      (Set.Ioo (-c.length) 0) := by
    exact c.smooth.comp contDiff_neg.contMDiff.contMDiffOn (by
      intro t ht
      constructor <;> linarith [ht.1, ht.2])
  have hrevGeo : IsGeodesicOn (I := I) g gammaRev
      (Set.Ioo (-c.length) 0) := by
    have hcgeo : IsGeodesicOn (I := I) g c.curve (Set.Ioo 0 c.length) :=
      c.geodesic.mono (by
        intro t ht
        exact ⟨ht.1.le, ht.2.le⟩)
    have h := isGeodesicOn_comp_neg (I := I) hcgeo
    exact h.mono (by
      intro t ht
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  have hrevCont : ContinuousOn gammaRev (Set.Ioo (-c.length) 0) :=
    hrevSmooth.continuousOn
  have hleftEndpoint := c.hasEndpointContinuation_comp_neg hL
  obtain ⟨gammaRevExt, bLeft, hbLeft, hrevExtGeo, hrevExtCont,
      hrevExtAgree⟩ :=
    isGeodesicOn_Ioo_extend (I := I) g
      (by linarith : -c.length < (0 : ℝ))
      hrevGeo hrevCont hleftEndpoint
  let gammaLeft : ℝ → M := fun t ↦ gammaRevExt (-t)
  have hleftGeo : IsGeodesicOn (I := I) g gammaLeft
      (Set.Ioo (-bLeft) c.length) := by
    have h := isGeodesicOn_comp_neg (I := I) hrevExtGeo
    exact h.mono (by
      intro t ht
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  have hleftCont : ContinuousOn gammaLeft
      (Set.Ioo (-bLeft) c.length) := by
    exact hrevExtCont.comp continuous_neg.continuousOn (by
      intro t ht
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  have hleftAgree : Set.EqOn gammaLeft c.curve
      (Set.Ioo 0 c.length) := by
    intro t ht
    have hagree := hrevExtAgree (-t) (by linarith [ht.1])
    simpa only [gammaLeft, gammaRev, neg_neg] using hagree
  have hrightEndpoint :
      HasEndpointContinuation (I := I) g c.curve c.length := by
    apply hasEndpointContinuation_of_unitSpeed g q hL
    · exact c.smooth.mono (fun _ ht ↦ ⟨ht.1.le, ht.2.le⟩)
    · exact c.unitSpeed
    · exact c.geodesic.mono (fun _ ht ↦ ⟨ht.1.le, ht.2.le⟩)
    · have hc : _root_.Filter.Tendsto c.curve
          (nhdsWithin c.length (Set.Iio c.length))
          (nhds (c.curve c.length)) := by
        have hc' := c.smooth.continuousOn c.length ⟨hL.le, le_rfl⟩
        apply hc'.mono_left
        intro s hs
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hs ⊢
        obtain ⟨u, hu, hus⟩ := hs
        refine ⟨u ∩ Set.Ioi 0, _root_.Filter.inter_mem hu (Ioi_mem_nhds hL), ?_⟩
        intro t ht
        exact hus ⟨ht.1.1, ⟨ht.1.2.le, ht.2.le⟩⟩
      have htarget : nhds (c.curve c.length) = nhds q :=
        congrArg nhds c.target
      exact htarget ▸ hc
  have hleftEventually :
      gammaLeft =ᶠ[nhdsWithin c.length (Set.Iio c.length)] c.curve := by
    filter_upwards [Ioo_mem_nhdsLT hL] with t ht
    exact hleftAgree ht
  have hrightForLeft :
      HasEndpointContinuation (I := I) g gammaLeft c.length :=
    hasEndpointContinuation_congr_left g hrightEndpoint hleftEventually
  obtain ⟨gammaFinal, bRight, hbRight, hfinalGeo, hfinalCont,
      hfinalAgreeLeft⟩ :=
    isGeodesicOn_Ioo_extend (I := I) g
      (by linarith : -bLeft < c.length)
      hleftGeo hleftCont hrightForLeft
  have hfinalAgreeOpen : Set.EqOn gammaFinal c.curve
      (Set.Ioo 0 c.length) := by
    intro t ht
    exact (hfinalAgreeLeft t ht.2).trans (hleftAgree ht)
  have hIccSubset : Set.Icc (0 : ℝ) c.length ⊆
      Set.Ioo (-bLeft) bRight := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2, hbLeft, hbRight]
  have hfinalAgreeClosed : Set.EqOn gammaFinal c.curve
      (Set.Icc 0 c.length) := by
    apply hfinalAgreeOpen.of_subset_closure
      (hfinalCont.mono hIccSubset) c.smooth.continuousOn
      (fun _ ht ↦ ⟨ht.1.le, ht.2.le⟩)
    rw [closure_Ioo hL.ne]
  have hfinalSmooth : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ gammaFinal
      (Set.Ioo (-bLeft) bRight) :=
    isGeodesicOn_contMDiffOn_infty
      (I := I) g isOpen_Ioo hfinalGeo hfinalCont
  let margin : ℝ := _root_.Min.min bLeft (bRight - c.length)
  have hmargin : 0 < margin := by
    exact lt_min hbLeft (sub_pos.mpr hbRight)
  let ext : SmoothGeodesicNeighborhoodExtension c :=
    { curve := gammaFinal
      margin := margin
      margin_pos := hmargin
      smoothOn := hfinalSmooth.mono (by
        intro t ht
        constructor
        · dsimp only [margin] at ht ⊢
          linarith [ht.1, min_le_left bLeft (bRight - c.length)]
        · dsimp only [margin] at ht ⊢
          linarith [ht.2, min_le_right bLeft (bRight - c.length)])
      geodesicOn := hfinalGeo.mono (by
        intro t ht
        constructor
        · dsimp only [margin] at ht ⊢
          linarith [ht.1, min_le_left bLeft (bRight - c.length)]
        · dsimp only [margin] at ht ⊢
          linarith [ht.2, min_le_right bLeft (bRight - c.length)])
      agrees := hfinalAgreeClosed }
  exact ⟨ext⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.RealizedMinimizingConnector.exists_smoothGeodesicNeighborhoodExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.RealizedMinimizingConnector.exists_smoothGeodesicNeighborhoodExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.RealizedMinimizingConnector.exists_smoothGeodesicNeighborhoodExtension ``Submission.DifferentialGeometry.Toponogov.RealizedMinimizingConnector.exists_smoothGeodesicNeighborhoodExtension

omit [T2Space (TangentBundle I M)] in
theorem RealizedMinimizingConnector.exists_smoothNeighborhoodExtension
    {g : SmoothRiemannianMetric I M} {p q : M}
    (c : RealizedMinimizingConnector (I := I) g p q) :
    Nonempty (SmoothNeighborhoodExtension c) := by
  obtain ⟨e⟩ := c.exists_smoothGeodesicNeighborhoodExtension
  exact ⟨e.toSmoothNeighborhoodExtension⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.RealizedMinimizingConnector.exists_smoothNeighborhoodExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.RealizedMinimizingConnector.exists_smoothNeighborhoodExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.RealizedMinimizingConnector.exists_smoothNeighborhoodExtension ``Submission.DifferentialGeometry.Toponogov.RealizedMinimizingConnector.exists_smoothNeighborhoodExtension

omit [T2Space (TangentBundle I M)] in
theorem RealizedMinimizingConnector.exists_smoothGeodesicRepresentative
    {g : SmoothRiemannianMetric I M} {p q : M}
    (c : RealizedMinimizingConnector (I := I) g p q) :
    Nonempty (SmoothGeodesicRepresentative c) := by
  obtain ⟨e⟩ := c.exists_smoothGeodesicNeighborhoodExtension
  exact e.exists_smoothGeodesicRepresentative

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.RealizedMinimizingConnector.exists_smoothGeodesicRepresentative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.RealizedMinimizingConnector.exists_smoothGeodesicRepresentative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.RealizedMinimizingConnector.exists_smoothGeodesicRepresentative ``Submission.DifferentialGeometry.Toponogov.RealizedMinimizingConnector.exists_smoothGeodesicRepresentative

omit [T2Space (TangentBundle I M)] in
theorem RealizedMinimizingConnector.exists_globallySmooth_replacement
    {g : SmoothRiemannianMetric I M} {p q : M}
    (c : RealizedMinimizingConnector (I := I) g p q) :
    ∃ c' : RealizedMinimizingConnector (I := I) g p q,
      ContMDiff 𝓘(ℝ, ℝ) I ∞ c'.curve ∧
      c'.length = c.length ∧
      Set.EqOn c'.curve c.curve (Set.Icc 0 c.length) := by
  obtain ⟨r⟩ := c.exists_smoothGeodesicRepresentative
  exact ⟨r.toRealizedMinimizingConnector, r.smooth, rfl, r.agrees⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.RealizedMinimizingConnector.exists_globallySmooth_replacement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.RealizedMinimizingConnector.exists_globallySmooth_replacement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.RealizedMinimizingConnector.exists_globallySmooth_replacement ``Submission.DifferentialGeometry.Toponogov.RealizedMinimizingConnector.exists_globallySmooth_replacement

omit [T2Space (TangentBundle I M)] in
theorem RealizedMinimizingConnector.exists_smoothRepresentative
    {g : SmoothRiemannianMetric I M} {p q : M}
    (c : RealizedMinimizingConnector (I := I) g p q) :
    Nonempty (SmoothRepresentative c) := by
  obtain ⟨r⟩ := c.exists_smoothGeodesicRepresentative
  exact ⟨r.toSmoothRepresentative⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.RealizedMinimizingConnector.exists_smoothRepresentative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.RealizedMinimizingConnector.exists_smoothRepresentative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.RealizedMinimizingConnector.exists_smoothRepresentative ``Submission.DifferentialGeometry.Toponogov.RealizedMinimizingConnector.exists_smoothRepresentative

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem SmoothGeodesicRepresentative.unitSpeed_Icc
    {g : SmoothRiemannianMetric I M} {p q : M}
    {c : RealizedMinimizingConnector (I := I) g p q}
    (r : SmoothGeodesicRepresentative c) (hL : 0 < c.length) :
    ∀ t ∈ Set.Icc (0 : ℝ) c.length,
      g.inner (r.curve t)
        (mfderiv 𝓘(ℝ, ℝ) I r.curve t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I r.curve t (1 : ℝ)) = 1 := by
  let f : ℝ → ℝ → M := fun _ t ↦ r.curve t
  have hf : IsSmoothVariation (I := I) f := by
    change ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (8 : ℕ)
      (fun z : ℝ × ℝ ↦ r.curve z.2)
    have h8le : ((8 : ℕ) : WithTop ℕ∞) ≤
        ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact WithTop.coe_le_coe.mpr (le_top : ((8 : ℕ) : ℕ∞) ≤ ⊤)
    exact (r.smooth.of_le h8le).comp contMDiff_snd
  have hcontinuous : Continuous (fun t : ℝ ↦ speedSq (I := I) g f 0 t) :=
    (speedSq_contDiff (I := I) (M := M) g f hf).continuous.comp
      (show Continuous (fun t : ℝ ↦ ((0 : ℝ), t)) from
        continuous_const.prodMk continuous_id)
  have heq : Set.EqOn (fun t : ℝ ↦ speedSq (I := I) g f 0 t)
      (fun _ : ℝ ↦ 1) (Set.Ioo 0 c.length) := by
    intro t ht
    change g.inner (r.curve t)
      (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ r.curve u) t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ r.curve u) t (1 : ℝ)) = 1
    rw [show (fun u : ℝ ↦ r.curve u) = r.curve by funext u; rfl]
    exact r.toSmoothRepresentative.unitSpeed ht
  have heqClosed := heq.closure hcontinuous continuous_const
  rw [closure_Ioo hL.ne] at heqClosed
  intro t ht
  simpa only [f, speedSq] using heqClosed ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative.unitSpeed_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative.unitSpeed_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative.unitSpeed_Icc ``Submission.DifferentialGeometry.Toponogov.SmoothGeodesicRepresentative.unitSpeed_Icc

end DifferentialGeometry.Toponogov
