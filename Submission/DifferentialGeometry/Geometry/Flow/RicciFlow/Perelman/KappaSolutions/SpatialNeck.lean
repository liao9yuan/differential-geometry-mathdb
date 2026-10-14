import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UnitCylinderMetric
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Defs
import Submission.DifferentialGeometry.Geometry.Metric.Completeness
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity
import Mathlib.Geometry.Manifold.SmoothEmbedding

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

universe u uE uH

private local instance spatialNeckSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckSphereDimension target :: scope.openDecls } }


def spatialNeckBuffer (epsilon : ℝ) : TopologicalSpace.Opens SpatialNeckCylinder :=
  ⟨{x | -epsilon⁻¹ - 1 < x.2 ∧ x.2 < epsilon⁻¹ + 1},
    (isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckBuffer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckBuffer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckBuffer ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckBuffer


def spatialNeckClosedCore (epsilon : ℝ) : Set (spatialNeckBuffer epsilon) :=
  {x | -epsilon⁻¹ ≤ x.1.2 ∧ x.1.2 ≤ epsilon⁻¹}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckClosedCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckClosedCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckClosedCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckClosedCore


def spatialNeckCentralDomain (epsilon : ℝ) : Set (spatialNeckBuffer epsilon) :=
  {x | x.1.2 = 0}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCentralDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCentralDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCentralDomain ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCentralDomain

def spatialNeckCentralPoint (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (y : SpatialNeckSphere) : spatialNeckBuffer epsilon :=
  ⟨(y, 0), by
    have hinv : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
    constructor <;> linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCentralPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCentralPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCentralPoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCentralPoint

theorem spatialNeckCentralPoint_mem (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (y : SpatialNeckSphere) :
    spatialNeckCentralPoint epsilon hepsilon y ∈ spatialNeckCentralDomain epsilon := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCentralPoint_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCentralPoint_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCentralPoint_mem ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCentralPoint_mem

theorem spatialNeckCentralDomain_subset_core (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    spatialNeckCentralDomain epsilon ⊆ spatialNeckClosedCore epsilon := by
  intro x hx
  change x.1.2 = 0 at hx
  change -epsilon⁻¹ ≤ x.1.2 ∧ x.1.2 ≤ epsilon⁻¹
  rw [hx]
  have hinv : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
  constructor <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCentralDomain_subset_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCentralDomain_subset_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCentralDomain_subset_core ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckCentralDomain_subset_core

theorem spatialNeckClosedCore_isCompact (epsilon : ℝ) :
    IsCompact (spatialNeckClosedCore epsilon) := by
  have hcompact : IsCompact
      ((Set.univ : Set SpatialNeckSphere) ×ˢ Set.Icc (-epsilon⁻¹) epsilon⁻¹) :=
    isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc
  have hsubset :
      ((Set.univ : Set SpatialNeckSphere) ×ˢ Set.Icc (-epsilon⁻¹) epsilon⁻¹) ⊆
        Set.range (Subtype.val : spatialNeckBuffer epsilon → SpatialNeckCylinder) := by
    intro x hx
    have hxlo : -epsilon⁻¹ ≤ x.2 := hx.2.1
    have hxhi : x.2 ≤ epsilon⁻¹ := hx.2.2
    exact ⟨⟨x, by constructor <;> linarith⟩, rfl⟩
  have hpre := Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
    hcompact hsubset
  simpa only [spatialNeckClosedCore, Set.preimage, Set.mem_prod,
    Set.mem_univ, true_and, Set.mem_Icc] using hpre

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckClosedCore_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckClosedCore_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckClosedCore_isCompact ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckClosedCore_isCompact

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance spatialNeckC1 : IsManifold I 1 N :=
  IsManifold.of_le (I := I) (M := N) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckC1 target :: scope.openDecls } }

def spatialNeckScale (h : SmoothRiemannianMetric I N) (p : N) : ℝ :=
  Real.sqrt 2 / Real.sqrt (metricScalarAt (I := I) h p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckScale ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckScale

omit [T2Space N] [SigmaCompactSpace N] in
theorem spatialNeckScale_pos (h : SmoothRiemannianMetric I N) (p : N)
    (hscalar : 0 < metricScalarAt (I := I) h p) : 0 < spatialNeckScale h p :=
  div_pos (by positivity) (Real.sqrt_pos.mpr hscalar)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckScale_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckScale_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckScale_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckScale_pos

omit [T2Space N] [SigmaCompactSpace N] in
theorem spatialNeckScale_inv_sq (h : SmoothRiemannianMetric I N) (p : N)
    (hscalar : 0 < metricScalarAt (I := I) h p) :
    ((spatialNeckScale h p) ^ 2)⁻¹ = metricScalarAt (I := I) h p / 2 := by
  rw [spatialNeckScale, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt hscalar.le, inv_div]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckScale_inv_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckScale_inv_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckScale_inv_sq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.spatialNeckScale_inv_sq

structure SpatialNeckWitness (h : SmoothRiemannianMetric I N)
    (yStar : SpatialNeckSphere) (p : N) (epsilon : ℝ) where
  dimension_three : Module.finrank ℝ E = 3
  complete : RiemannianMetricComplete (I := I) h
  epsilon_pos : 0 < epsilon
  scalar_pos : 0 < metricScalarAt (I := I) h p
  embedding : C(spatialNeckBuffer epsilon, N)
  smooth_embedding : _root_.Manifold.IsSmoothEmbedding SpatialNeckCylinderModel I ∞ embedding
  marked : embedding (spatialNeckCentralPoint epsilon epsilon_pos yStar) = p
  normalizedMetric :
    SmoothRiemannianMetric SpatialNeckCylinderModel (spatialNeckBuffer epsilon)
  normalized_inner : ∀ (x : spatialNeckBuffer epsilon)
      (V W : TangentSpace SpatialNeckCylinderModel x),
    normalizedMetric.inner x V W = ((spatialNeckScale h p) ^ 2)⁻¹ *
      h.inner (embedding x)
        (mfderiv SpatialNeckCylinderModel I embedding x V)
        (mfderiv SpatialNeckCylinderModel I embedding x W)
  closeness : metricDerivNormSupOn (I := SpatialNeckCylinderModel)
    (spatialNeckClosedCore epsilon) (Nat.ceil epsilon⁻¹) normalizedMetric
    (unitCylinderMetric.restrictOpen (spatialNeckBuffer epsilon))
    (unitCylinderMetric.restrictOpen (spatialNeckBuffer epsilon)) < epsilon

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness

def IsSpatialNeckCenter (h : SmoothRiemannianMetric I N)
    (yStar : SpatialNeckSphere) (p : N) (epsilon : ℝ) : Prop :=
  Nonempty (SpatialNeckWitness h yStar p epsilon)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.IsSpatialNeckCenter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.IsSpatialNeckCenter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.IsSpatialNeckCenter ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.IsSpatialNeckCenter

namespace SpatialNeckWitness

variable {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
  {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon)


def image : Set N := Set.range W.embedding

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.image ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.image


def core : Set N := W.embedding '' spatialNeckClosedCore epsilon

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.core ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.core


def centralSphere : Set N := W.embedding '' spatialNeckCentralDomain epsilon

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralSphere ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralSphere


def centralMap (y : SpatialNeckSphere) : N :=
  W.embedding (spatialNeckCentralPoint epsilon W.epsilon_pos y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralMap ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralMap

theorem centralMap_marked : W.centralMap yStar = p := W.marked

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralMap_marked then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralMap_marked"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralMap_marked ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralMap_marked

theorem core_subset_image : W.core ⊆ W.image := by
  rintro q ⟨x, _hx, rfl⟩
  exact ⟨x, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.core_subset_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.core_subset_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.core_subset_image ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.core_subset_image

theorem centralSphere_subset_core : W.centralSphere ⊆ W.core :=
  Set.image_mono (spatialNeckCentralDomain_subset_core epsilon W.epsilon_pos)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralSphere_subset_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralSphere_subset_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralSphere_subset_core ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralSphere_subset_core

theorem marked_mem_centralSphere : p ∈ W.centralSphere :=
  ⟨spatialNeckCentralPoint epsilon W.epsilon_pos yStar,
    spatialNeckCentralPoint_mem epsilon W.epsilon_pos yStar, W.marked⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.marked_mem_centralSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.marked_mem_centralSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.marked_mem_centralSphere ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.marked_mem_centralSphere

theorem marked_mem_core : p ∈ W.core :=
  W.centralSphere_subset_core W.marked_mem_centralSphere

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.marked_mem_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.marked_mem_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.marked_mem_core ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.marked_mem_core

theorem marked_mem_image : p ∈ W.image := W.core_subset_image W.marked_mem_core

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.marked_mem_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.marked_mem_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.marked_mem_image ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.marked_mem_image

theorem centralSphere_eq_range : W.centralSphere = Set.range W.centralMap := by
  ext q
  constructor
  · rintro ⟨x, hx, hq⟩
    change x.1.2 = 0 at hx
    refine ⟨x.1.1, ?_⟩
    have hpoint : spatialNeckCentralPoint epsilon W.epsilon_pos x.1.1 = x :=
      Subtype.ext (Prod.ext rfl hx.symm)
    change W.embedding (spatialNeckCentralPoint epsilon W.epsilon_pos x.1.1) = q
    rw [hpoint]
    exact hq
  · rintro ⟨y, rfl⟩
    exact ⟨spatialNeckCentralPoint epsilon W.epsilon_pos y,
      spatialNeckCentralPoint_mem epsilon W.epsilon_pos y, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralSphere_eq_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralSphere_eq_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralSphere_eq_range ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralSphere_eq_range

theorem centralMap_injective : Function.Injective W.centralMap := by
  intro y z hyz
  have hpoint := W.smooth_embedding.isEmbedding.injective hyz
  exact congrArg (fun x : spatialNeckBuffer epsilon => x.1.1) hpoint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralMap_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralMap_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralMap_injective ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.centralMap_injective

theorem normalizedMetric_unique
    (g : SmoothRiemannianMetric SpatialNeckCylinderModel (spatialNeckBuffer epsilon))
    (hg : ∀ (x : spatialNeckBuffer epsilon)
      (V Z : TangentSpace SpatialNeckCylinderModel x),
      g.inner x V Z = ((spatialNeckScale h p) ^ 2)⁻¹ * h.inner (W.embedding x)
        (mfderiv SpatialNeckCylinderModel I W.embedding x V)
        (mfderiv SpatialNeckCylinderModel I W.embedding x Z)) :
    g = W.normalizedMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro x V Z
  exact (hg x V Z).trans (W.normalized_inner x V Z).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.normalizedMetric_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.normalizedMetric_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.normalizedMetric_unique ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.normalizedMetric_unique

theorem differential_injective (x : spatialNeckBuffer epsilon) :
    Function.Injective (mfderiv SpatialNeckCylinderModel I W.embedding x) := by
  intro V Z hVZ
  apply sub_eq_zero.mp
  by_contra hnonzero
  have hpositive := W.normalizedMetric.pos x (V - Z) hnonzero
  have hzero : mfderiv SpatialNeckCylinderModel I W.embedding x (V - Z) = 0 := by
    rw [map_sub, hVZ, sub_self]
  rw [W.normalized_inner, hzero] at hpositive
  simp at hpositive

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.differential_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.differential_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.differential_injective ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.differential_injective

theorem metricDerivNorm_lt (a : ℕ) (ha : a ≤ Nat.ceil epsilon⁻¹)
    (x : spatialNeckBuffer epsilon) (hx : x ∈ spatialNeckClosedCore epsilon) :
    metricDerivNorm (I := SpatialNeckCylinderModel) a W.normalizedMetric
      (unitCylinderMetric.restrictOpen (spatialNeckBuffer epsilon))
      (unitCylinderMetric.restrictOpen (spatialNeckBuffer epsilon)) x < epsilon :=
  (derivNorm_le_sup (I := SpatialNeckCylinderModel)
    (spatialNeckClosedCore_isCompact epsilon) ha W.normalizedMetric
    (unitCylinderMetric.restrictOpen (spatialNeckBuffer epsilon))
    (unitCylinderMetric.restrictOpen (spatialNeckBuffer epsilon)) hx).trans_lt W.closeness

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.metricDerivNorm_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.metricDerivNorm_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.metricDerivNorm_lt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckWitness.metricDerivNorm_lt

end SpatialNeckWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
