import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecenterAux
import Submission.DifferentialGeometry.Geometry.Neck.NormalizedDatum
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.EndNeckDatum
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalDiffeomorphEmbedding
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Submission.Set _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Metric
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Topology.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck (bufferedCylinder referenceMetric normalizedDatum
  spherePoint cylinderCenter)

universe u

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat target :: scope.openDecls } }

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {h : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.sphereMark_eq_of_chart_eq_of_center_eq {N₁ N₂ : NormalizedNeck h δ k}
    (hchart : N₁.chart = N₂.chart) (hcenter : N₁.center = N₂.center) :
    N₁.sphereMark = N₂.sphereMark := by
  have h₁ : N₂.chart ⟨(N₁.sphereMark, 0), by
      have := inv_pos.mpr N₁.delta_pos
      constructor <;> linarith⟩ = N₂.center := by
    rw [← hchart, ← hcenter]
    exact N₁.marked
  have h₂ : N₂.chart ⟨(N₂.sphereMark, 0), by
      have := inv_pos.mpr N₂.delta_pos
      constructor <;> linarith⟩ = N₂.center := N₂.marked
  have h₃ := N₂.chart_smooth.isEmbedding.injective (h₁.trans h₂.symm)
  have h₄ := congrArg (fun x : neckBuffer δ => ((x : Sphere 2 × ℝ).1)) h₃
  simpa using h₄

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.sphereMark_eq_of_chart_eq_of_center_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.sphereMark_eq_of_chart_eq_of_center_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.sphereMark_eq_of_chart_eq_of_center_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.sphereMark_eq_of_chart_eq_of_center_eq

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.sphereMark_eq_spherePoint_iff_chart_cylinderCenter
    (N : NormalizedNeck h δ k) :
    N.sphereMark = spherePoint ↔
      N.chart (cylinderCenter δ N.delta_pos : neckBuffer δ) = N.center := by
  constructor
  · intro hmark
    have hp : (cylinderCenter δ N.delta_pos : neckBuffer δ) =
        ⟨(N.sphereMark, 0), by
          have := inv_pos.mpr N.delta_pos
          constructor <;> linarith⟩ := by
      apply Subtype.ext
      simp only [cylinderCenter, hmark]
    rw [hp]
    exact N.marked
  · intro hcenter
    have h₁ : N.chart ⟨(N.sphereMark, 0), by
        have := inv_pos.mpr N.delta_pos
        constructor <;> linarith⟩ = N.center := N.marked
    have h₃ := N.chart_smooth.isEmbedding.injective (h₁.trans hcenter.symm)
    have h₄ := congrArg (fun x : neckBuffer δ => ((x : Sphere 2 × ℝ).1)) h₃
    have h₅ : ((cylinderCenter δ N.delta_pos : neckBuffer δ) : Sphere 2 × ℝ) =
        (spherePoint, 0) :=
      rfl
    rw [h₅] at h₄
    simpa using h₄

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.sphereMark_eq_spherePoint_iff_chart_cylinderCenter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.sphereMark_eq_spherePoint_iff_chart_cylinderCenter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.sphereMark_eq_spherePoint_iff_chart_cylinderCenter ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.sphereMark_eq_spherePoint_iff_chart_cylinderCenter

omit [SigmaCompactSpace M] in
theorem NormalizedNeck.sphereMark_eq_spherePoint_of_datum (N : NormalizedNeck h δ k)
    (d : normalizedDatum h N.center δ k)
    (hchart : ∀ x : bufferedCylinder δ, d.map x = N.chart x) : N.sphereMark = spherePoint := by
  rw [N.sphereMark_eq_spherePoint_iff_chart_cylinderCenter]
  exact (hchart _).symm.trans ((rfl : d.map (cylinderCenter δ N.delta_pos : bufferedCylinder δ) =
    d.map (cylinderCenter δ d.precision_pos)).trans d.center_eq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.sphereMark_eq_spherePoint_of_datum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.sphereMark_eq_spherePoint_of_datum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.sphereMark_eq_spherePoint_of_datum ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.sphereMark_eq_spherePoint_of_datum

omit [SigmaCompactSpace M] in
theorem NormalizedNeck.not_exists_datum_of_sphereMark_ne (N : NormalizedNeck h δ k)
    (hne : N.sphereMark ≠ spherePoint) :
    ¬ ∃ d : normalizedDatum h N.center δ k,
        ∀ x : bufferedCylinder δ, d.map x = N.chart x := by
  rintro ⟨d, hchart⟩
  exact hne (N.sphereMark_eq_spherePoint_of_datum d hchart)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.not_exists_datum_of_sphereMark_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.not_exists_datum_of_sphereMark_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.not_exists_datum_of_sphereMark_ne ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.not_exists_datum_of_sphereMark_ne

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.exists_sphereMark_ne_of_scalar_eq (N : NormalizedNeck h δ k)
    (y : Sphere 2) (hy : y ≠ N.sphereMark) (hmem : (y, 0) ∈ neckBuffer δ)
    (hscalar : metricScalarAt h (N.chart ⟨(y, 0), hmem⟩) = N.scale) :
    ∃ N' : NormalizedNeck h δ k, N'.sphereMark ≠ N.sphereMark ∧ N'.chart = N.chart ∧
      N'.normalizedMetric = N.normalizedMetric := by
  exact ⟨{ N with
    sphereMark := y
    center := N.chart ⟨(y, 0), hmem⟩
    marked := congrArg (fun q : neckBuffer δ => N.chart q) (Subtype.ext rfl)
    scale_scalar := hscalar.symm }, hy, rfl, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.exists_sphereMark_ne_of_scalar_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.exists_sphereMark_ne_of_scalar_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.exists_sphereMark_ne_of_scalar_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck.exists_sphereMark_ne_of_scalar_eq

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
  (localDiffeomorphAt_isImmersionAtOfComplement)
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceOfNat : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp [ThreeSpace]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceOfNat target :: scope.openDecls } }

theorem referenceMetric_eq_roundCylinderMetric_neckBuffer (δ : ℝ) :
    referenceMetric δ = roundCylinderMetric.restrictOpen (neckBuffer δ) := by
  rw [referenceMetric, roundCylinderMetric_eq_geometry]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.referenceMetric_eq_roundCylinderMetric_neckBuffer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.referenceMetric_eq_roundCylinderMetric_neckBuffer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.referenceMetric_eq_roundCylinderMetric_neckBuffer ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.referenceMetric_eq_roundCylinderMetric_neckBuffer

private theorem metricDerivNormSupOn_self_neckClosedTest (δ : ℝ) (k : ℕ)
    (g : SmoothRiemannianMetric NeckCylinderModel (neckBuffer δ)) :
    metricDerivNormSupOn (neckClosedTest δ) k g g g = 0 := by
  refine le_antisymm ?_ ?_
  · refine Real.sSup_le (fun r hr => ?_) le_rfl
    obtain ⟨a, _ha, x, _hx, rfl⟩ := hr
    exact le_of_eq (metricDerivNorm_self a g g x)
  · exact Real.sSup_nonneg (fun r hr => by
      obtain ⟨a, _ha, x, _hx, rfl⟩ := hr
      rw [metricDerivNorm_self])

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.metricDerivNormSupOn_self_neckClosedTest
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.metricDerivNormSupOn_self_neckClosedTest target :: scope.openDecls } }

private theorem endNeckMarker_mem (y : Sphere 2) {δ : ℝ} (hδ : 0 < δ) :
    ((y, 0) : Sphere 2 × ℝ) ∈ neckBuffer δ := by
  change -δ⁻¹ - 1 < (0 : ℝ) ∧ (0 : ℝ) < δ⁻¹ + 1
  have hi := inv_pos.mpr hδ
  constructor <;> linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckMarker_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckMarker_mem target :: scope.openDecls } }

private theorem endNeckMap_marker (r δ : ℝ) (hδ : 0 < δ) (y : Sphere 2) :
    endNeckMap r δ ⟨(y, 0), endNeckMarker_mem y hδ⟩ = r • (y : ThreeSpace) := by
  rw [endNeckMap_apply]
  simp only [add_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckMap_marker
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckMap_marker target :: scope.openDecls } }

private theorem metricScalarAt_endNeckMap_marker (r δ : ℝ) (hδ : 0 < δ)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (y : Sphere 2) :
    metricScalarAt metric (r • (y : ThreeSpace)) = 1 := by
  rw [← endNeckMap_marker r δ hδ y]
  exact endNeckMap_scalar hr _

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.metricScalarAt_endNeckMap_marker
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.metricScalarAt_endNeckMap_marker target :: scope.openDecls } }

private theorem metricScalarAt_endNeckMap_center (r δ : ℝ) (hδ : 0 < δ)
    (hr : transitionEnd + δ⁻¹ + 1 < r) :
    metricScalarAt metric (r • (spherePoint : ThreeSpace)) = 1 :=
  metricScalarAt_endNeckMap_marker r δ hδ hr spherePoint

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.metricScalarAt_endNeckMap_center
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.metricScalarAt_endNeckMap_center target :: scope.openDecls } }

private theorem endNeckMap_isImmersion (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) :
    Manifold.IsImmersion NeckCylinderModel ThreeModel ∞
      (fun z : neckBuffer δ => endNeckMap r δ z) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
      Module.finrank ℝ ThreeSpace := by
    simp
  have hloc : IsLocalDiffeomorph NeckCylinderModel (𝓡 3) ∞ (endNeckMap r δ) :=
    isLocalDiffeomorph_of_injective_mfderiv (endNeckMap r δ)
      (endNeckDatum r δ hδ hδ1 hr k _root_.Bool.false).smooth
      (endNeckDatum r δ hδ hδ1 hr k _root_.Bool.false).immersion hdim
  have h : Manifold.IsImmersion NeckCylinderModel (𝓡 3) ∞ (endNeckMap r δ) :=
    Manifold.IsImmersionOfComplement.isImmersion fun z =>
      localDiffeomorphAt_isImmersionAtOfComplement (hloc z)
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckMap_isImmersion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckMap_isImmersion target :: scope.openDecls } }

private theorem endNeckMap_isEmbedding (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) :
    Topology.IsEmbedding (fun z : neckBuffer δ => endNeckMap r δ z) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
      Module.finrank ℝ ThreeSpace := by
    simp
  have h : _root_.Topology.IsOpenEmbedding (endNeckMap r δ) :=
    isOpenEmbedding_of_injective_immersion (endNeckMap r δ)
      (endNeckDatum r δ hδ hδ1 hr k _root_.Bool.false).smooth
      (endNeckDatum r δ hδ hδ1 hr k _root_.Bool.false).injective
      (endNeckDatum r δ hδ hδ1 hr k _root_.Bool.false).immersion hdim
  exact h.toIsEmbedding

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckMap_isEmbedding
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckMap_isEmbedding target :: scope.openDecls } }

def endNeckNormalizedNeck (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (y : Sphere 2) :
    NormalizedNeck metric δ k where
  delta_pos := hδ
  delta_lt_one := hδ1
  sphereMark := y
  center := r • (y : ThreeSpace)
  chart := ⟨fun z : neckBuffer δ => endNeckMap r δ z,
    (endNeckDatum r δ hδ hδ1 hr k _root_.Bool.false).smooth.continuous⟩
  chart_smooth := ⟨endNeckMap_isImmersion r δ hδ hδ1 hr k,
    endNeckMap_isEmbedding r δ hδ hδ1 hr k⟩
  marked := endNeckMap_marker r δ hδ y
  scale := 1
  scale_pos := one_pos
  scale_scalar := (metricScalarAt_endNeckMap_marker r δ hδ hr y).symm
  normalizedMetric := (endNeckDatum r δ hδ hδ1 hr k _root_.Bool.false).normalizedMetric
  normalized_inner := by
    intro x V W
    have h := (endNeckDatum r δ hδ hδ1 hr k _root_.Bool.false).normalizedMetric_inner x V W
    rw [metricScalarAt_endNeckMap_center r δ hδ hr, one_mul] at h
    have h' : ((endNeckDatum r δ hδ hδ1 hr k _root_.Bool.false).normalizedMetric.inner x V W) =
        metric.inner ((fun z : neckBuffer δ => endNeckMap r δ z) x)
          (mfderiv NeckCylinderModel ThreeModel (fun z : neckBuffer δ => endNeckMap r δ z) x V)
          (mfderiv NeckCylinderModel ThreeModel
            (fun z : neckBuffer δ => endNeckMap r δ z) x W) := h
    rw [one_mul]
    exact h'
  closeness := by
    rw [endNeckDatum_normalizedMetric, referenceMetric_eq_roundCylinderMetric_neckBuffer,
      metricDerivNormSupOn_self_neckClosedTest]
    exact hδ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck

theorem endNeckNormalizedNeck_sphereMark (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (y : Sphere 2) :
    (endNeckNormalizedNeck r δ hδ hδ1 hr k y).sphereMark = y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_sphereMark then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_sphereMark"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_sphereMark ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_sphereMark

theorem endNeckNormalizedNeck_center (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (y : Sphere 2) :
    (endNeckNormalizedNeck r δ hδ hδ1 hr k y).center = r • (y : ThreeSpace) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_center then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_center"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_center ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_center

theorem endNeckNormalizedNeck_chart (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (y : Sphere 2) :
    ((endNeckNormalizedNeck r δ hδ hδ1 hr k y).chart : neckBuffer δ → ThreeSpace) =
      fun z : neckBuffer δ => endNeckMap r δ z := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_chart ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_chart

theorem endNeckNormalizedNeck_normalizedMetric (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (y : Sphere 2) :
    (endNeckNormalizedNeck r δ hδ hδ1 hr k y).normalizedMetric = referenceMetric δ :=
  endNeckDatum_normalizedMetric r δ hδ hδ1 hr k _root_.Bool.false

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_normalizedMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_normalizedMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_normalizedMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_normalizedMetric

theorem neg_spherePoint_ne_spherePoint : (-spherePoint : Sphere 2) ≠ spherePoint :=
  fun h => ne_neg_of_mem_unit_sphere ℝ spherePoint h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neg_spherePoint_ne_spherePoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neg_spherePoint_ne_spherePoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neg_spherePoint_ne_spherePoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neg_spherePoint_ne_spherePoint

theorem endNeckNormalizedNeck_sphereMark_countermodel (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) :
    (endNeckNormalizedNeck r δ hδ hδ1 hr k (-spherePoint)).sphereMark ≠
        (endNeckNormalizedNeck r δ hδ hδ1 hr k spherePoint).sphereMark ∧
      (endNeckNormalizedNeck r δ hδ hδ1 hr k (-spherePoint)).chart =
        (endNeckNormalizedNeck r δ hδ hδ1 hr k spherePoint).chart ∧
      (endNeckNormalizedNeck r δ hδ hδ1 hr k (-spherePoint)).normalizedMetric =
        (endNeckNormalizedNeck r δ hδ hδ1 hr k spherePoint).normalizedMetric :=
  ⟨neg_spherePoint_ne_spherePoint, rfl, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_sphereMark_countermodel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_sphereMark_countermodel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_sphereMark_countermodel ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_sphereMark_countermodel

theorem endNeckNormalizedNeck_exists_datum (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) :
    ∃ d : normalizedDatum metric
        (endNeckNormalizedNeck r δ hδ hδ1 hr k spherePoint).center δ k,
      ∀ x : bufferedCylinder δ,
        d.map x = (endNeckNormalizedNeck r δ hδ hδ1 hr k spherePoint).chart x :=
  ⟨endNeckDatum r δ hδ hδ1 hr k _root_.Bool.false, fun _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_exists_datum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_exists_datum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_exists_datum ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_exists_datum

theorem endNeckNormalizedNeck_not_exists_datum_neg (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) :
    ¬ ∃ d : normalizedDatum metric
        (endNeckNormalizedNeck r δ hδ hδ1 hr k (-spherePoint)).center δ k,
      ∀ x : bufferedCylinder δ,
        d.map x = (endNeckNormalizedNeck r δ hδ hδ1 hr k (-spherePoint)).chart x := by
  refine NormalizedNeck.not_exists_datum_of_sphereMark_ne
    (endNeckNormalizedNeck r δ hδ hδ1 hr k (-spherePoint)) ?_
  rw [endNeckNormalizedNeck_sphereMark]
  exact neg_spherePoint_ne_spherePoint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_not_exists_datum_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_not_exists_datum_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_not_exists_datum_neg ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckNormalizedNeck_not_exists_datum_neg

theorem endNeckDatum_retainedSide_countermodel (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) :
    (endNeckDatum r δ hδ hδ1 hr k _root_.Bool.false).retainedSign ≠
        (endNeckDatum r δ hδ hδ1 hr k _root_.Bool.true).retainedSign ∧
      (endNeckDatum r δ hδ hδ1 hr k _root_.Bool.false).map =
        (endNeckDatum r δ hδ hδ1 hr k _root_.Bool.true).map ∧
      (endNeckDatum r δ hδ hδ1 hr k _root_.Bool.false).normalizedMetric =
        (endNeckDatum r δ hδ hδ1 hr k _root_.Bool.true).normalizedMetric := by
  refine ⟨?_, rfl, ?_⟩
  · rw [normalizedDatum.retainedSign, normalizedDatum.retainedSign,
      endNeckDatum_retainedSide, endNeckDatum_retainedSide]
    norm_num
  · rw [endNeckDatum_normalizedMetric, endNeckDatum_normalizedMetric]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckDatum_retainedSide_countermodel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckDatum_retainedSide_countermodel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckDatum_retainedSide_countermodel ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endNeckDatum_retainedSide_countermodel

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.Geometry.Neck

open scoped _root_.ContDiff _root_.ENNReal

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealProdEuclideanSpaceFinOfNat_differentialGeometry : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3) :=
  ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealProdEuclideanSpaceFinOfNat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealProdEuclideanSpaceFinOfNat_differentialGeometry target :: scope.openDecls } }

def normalizedDatum.withRetainedSide (d : normalizedDatum g x₀ δ k) (b : Bool) :
    normalizedDatum g x₀ δ k :=
  { d with retainedSide := b }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.withRetainedSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.withRetainedSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.withRetainedSide ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.withRetainedSide

theorem normalizedDatum.withRetainedSide_retainedSide (d : normalizedDatum g x₀ δ k) (b : Bool) :
    (d.withRetainedSide b).retainedSide = b := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.withRetainedSide_retainedSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.withRetainedSide_retainedSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.withRetainedSide_retainedSide ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.withRetainedSide_retainedSide

theorem normalizedDatum.withRetainedSide_geometric_eq (d : normalizedDatum g x₀ δ k) (b : Bool) :
    (d.withRetainedSide b).map = d.map ∧ (d.withRetainedSide b).smooth = d.smooth ∧
      (d.withRetainedSide b).center_eq = d.center_eq ∧
      (d.withRetainedSide b).normalizedMetric = d.normalizedMetric ∧
      (d.withRetainedSide b).error_lt = d.error_lt :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.withRetainedSide_geometric_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.withRetainedSide_geometric_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.withRetainedSide_geometric_eq ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.withRetainedSide_geometric_eq

theorem normalizedDatum.withRetainedSide_ne (d : normalizedDatum g x₀ δ k) (b : Bool)
    (hb : b ≠ d.retainedSide) : d.withRetainedSide b ≠ d := by
  intro h
  exact hb (by rw [← h, d.withRetainedSide_retainedSide])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.withRetainedSide_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.withRetainedSide_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.withRetainedSide_ne ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.withRetainedSide_ne

theorem roundCylinderDatum_retainedSide_countermodel (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (k : ℕ) :
    (roundCylinderDatum δ hδ hδ1 k _root_.Bool.false).retainedSign ≠
        (roundCylinderDatum δ hδ hδ1 k _root_.Bool.true).retainedSign ∧
      (roundCylinderDatum δ hδ hδ1 k _root_.Bool.false).map =
        (roundCylinderDatum δ hδ hδ1 k _root_.Bool.true).map := by
  refine ⟨?_, rfl⟩
  · rw [normalizedDatum.retainedSign, normalizedDatum.retainedSign,
      roundCylinderDatum_retainedSide, roundCylinderDatum_retainedSide]
    norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.roundCylinderDatum_retainedSide_countermodel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.roundCylinderDatum_retainedSide_countermodel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.roundCylinderDatum_retainedSide_countermodel ``Submission.DifferentialGeometry.Geometry.Neck.roundCylinderDatum_retainedSide_countermodel

end DifferentialGeometry.Geometry.Neck


namespace DifferentialGeometry.Geometry.Neck.normalizedDatum

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Metric
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.Topology.Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
variable {g : SmoothRiemannianMetric ThreeModel M} {x₀ : M} {δ : ℝ} {k : ℕ}

private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.instFactEqNatFinrankRealThreeSpaceHAddOfNat : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.instFactEqNatFinrankRealThreeSpaceHAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.instFactEqNatFinrankRealThreeSpaceHAddOfNat target :: scope.openDecls } }

def toNormalizedNeck (d : normalizedDatum g x₀ δ k) :
    NormalizedNeck g δ k := by
  refine ⟨d.precision_pos, d.precision_lt_one, spherePoint, x₀,
    ⟨d.map, d.smooth.continuous⟩, ?_, ?_, metricScalarAt g x₀, d.scalar_pos, rfl,
    d.normalizedMetric, ?_, ?_⟩
  · exact DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_injective_mfderiv
      d.smooth d.injective d.immersion (by simp [ThreeSpace])
  · exact d.center_eq
  · exact d.normalizedMetric_inner
  · have hE := d.error_lt
    change metricDerivENormSupOn (controlledCylinder δ) k d.normalizedMetric
      (referenceMetric δ) (referenceMetric δ) < ENNReal.ofReal δ at hE
    rw [metricDerivENormSupOn_eq_ofReal_of_isCompact
      (isCompact_controlledCylinder δ) k d.normalizedMetric (referenceMetric δ) (referenceMetric δ)] at hE
    have hnorm : metricDerivNormSupOn (controlledCylinder δ) k d.normalizedMetric
        (referenceMetric δ) (referenceMetric δ) < δ :=
      (ENNReal.ofReal_lt_ofReal_iff d.precision_pos).mp hE
    have hset : controlledCylinder δ = neckClosedTest δ := by
      ext x
      rfl
    rw [hset] at hnorm
    rw [← referenceMetric_eq_roundCylinderMetric_neckBuffer δ]
    exact hnorm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.toNormalizedNeck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.toNormalizedNeck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.toNormalizedNeck ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.toNormalizedNeck

@[simp] theorem toNormalizedNeck_chart (d : normalizedDatum g x₀ δ k) :
    (d.toNormalizedNeck.chart : neckBuffer δ → M) = d.map := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.toNormalizedNeck_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.toNormalizedNeck_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.toNormalizedNeck_chart ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.toNormalizedNeck_chart

@[simp] theorem toNormalizedNeck_center (d : normalizedDatum g x₀ δ k) :
    d.toNormalizedNeck.center = x₀ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.toNormalizedNeck_center then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.toNormalizedNeck_center"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.toNormalizedNeck_center ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.toNormalizedNeck_center

@[simp] theorem toNormalizedNeck_sphereMark (d : normalizedDatum g x₀ δ k) :
    d.toNormalizedNeck.sphereMark = spherePoint := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.toNormalizedNeck_sphereMark then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.toNormalizedNeck_sphereMark"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.toNormalizedNeck_sphereMark ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.toNormalizedNeck_sphereMark

end DifferentialGeometry.Geometry.Neck.normalizedDatum
