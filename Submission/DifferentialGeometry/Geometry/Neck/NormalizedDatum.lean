import Submission.DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback
import Submission.DifferentialGeometry.Geometry.Metric.DerivativeENorm
import Submission.DifferentialGeometry.Geometry.Curvature.ScalarRoundCylinder
import Submission.DifferentialGeometry.Geometry.Curvature.RoundCylinder
import Submission.DifferentialGeometry.Geometry.Metric.RoundCylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Topology.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.Geometry.Neck

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.S2 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.IC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

def spherePoint : S2 := ⟨EuclideanSpace.single 0 1, by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.spherePoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.spherePoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.spherePoint ``Submission.DifferentialGeometry.Geometry.Neck.spherePoint

def bufferedCylinder (δ : ℝ) : _root_.TopologicalSpace.Opens (S2 × ℝ) :=
  ⟨{q | q.2 ∈ _root_.Set.Ioo (-δ⁻¹ - 1) (δ⁻¹ + 1)}, isOpen_Ioo.preimage continuous_snd⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.bufferedCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.bufferedCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.bufferedCylinder ``Submission.DifferentialGeometry.Geometry.Neck.bufferedCylinder

def controlledCylinder (δ : ℝ) : Set (bufferedCylinder δ) :=
  {q | q.val.2 ∈ _root_.Set.Icc (-δ⁻¹) δ⁻¹}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.controlledCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.controlledCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.controlledCylinder ``Submission.DifferentialGeometry.Geometry.Neck.controlledCylinder

def cylinderCenter (δ : ℝ) (hδ : 0 < δ) : bufferedCylinder δ :=
  ⟨(spherePoint, 0), by
    change -δ⁻¹ - 1 < 0 ∧ (0 : ℝ) < δ⁻¹ + 1
    have hi := inv_pos.mpr hδ
    constructor <;> linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.cylinderCenter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.cylinderCenter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.cylinderCenter ``Submission.DifferentialGeometry.Geometry.Neck.cylinderCenter

def referenceMetric (δ : ℝ) : SmoothRiemannianMetric IC (bufferedCylinder δ) :=
  (roundCylinderMetric (E := E3) (n := 2)).restrictOpen (bufferedCylinder δ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.referenceMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.referenceMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.referenceMetric ``Submission.DifferentialGeometry.Geometry.Neck.referenceMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] in
private theorem cylinder_dimension_eq :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = Module.finrank ℝ E := by
  rw [show Module.finrank ℝ E = 3 from Fact.out]
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.cylinder_dimension_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.cylinder_dimension_eq target :: scope.openDecls } }

structure normalizedDatum (g : SmoothRiemannianMetric I M) (x₀ : M) (δ : ℝ) (k : ℕ) where
  precision_pos : 0 < δ
  precision_lt_one : δ < 1
  map : bufferedCylinder δ → M
  smooth : ContMDiff IC I ∞ map
  injective : _root_.Function.Injective map
  immersion : ∀ x, _root_.Function.Injective (mfderiv IC I map x)
  center_eq : map (cylinderCenter δ precision_pos) = x₀
  scalar_pos : 0 < metricScalarAt g x₀
  error_lt : metricDerivENormSupOn (controlledCylinder δ) k
    (pullbackMetricOfInjectiveLocalDiffeomorph
      (scaleMetric (metricScalarAt g x₀) scalar_pos g) map
      (isLocalDiffeomorph_of_injective_mfderiv map smooth immersion cylinder_dimension_eq)
      injective) (referenceMetric δ) (referenceMetric δ) < ENNReal.ofReal δ
  retainedSide : Bool

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum

namespace normalizedDatum

variable {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

theorem isOpenEmbedding_map (d : normalizedDatum g x₀ δ k) :
    _root_.Topology.IsOpenEmbedding d.map :=
  isOpenEmbedding_of_injective_immersion d.map d.smooth d.injective d.immersion
    cylinder_dimension_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.isOpenEmbedding_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.isOpenEmbedding_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.isOpenEmbedding_map ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.isOpenEmbedding_map

def normalizedMetric (d : normalizedDatum g x₀ δ k) :
    SmoothRiemannianMetric IC (bufferedCylinder δ) :=
  pullbackMetricOfInjectiveLocalDiffeomorph
    (scaleMetric (metricScalarAt g x₀) d.scalar_pos g) d.map
    (isLocalDiffeomorph_of_injective_mfderiv d.map d.smooth d.immersion cylinder_dimension_eq)
    d.injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.normalizedMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.normalizedMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.normalizedMetric ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.normalizedMetric

theorem normalizedMetric_inner (d : normalizedDatum g x₀ δ k)
    (x : bufferedCylinder δ) (v w : TangentSpace IC x) :
    d.normalizedMetric.inner x v w = metricScalarAt g x₀ *
      g.inner (d.map x) (mfderiv IC I d.map x v) (mfderiv IC I d.map x w) := by
  rw [normalizedMetric, pullbackMetricOfInjectiveLocalDiffeomorph_inner, scaleMetric_inner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.normalizedMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.normalizedMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.normalizedMetric_inner ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.normalizedMetric_inner

theorem normalizedMetric_error_lt (d : normalizedDatum g x₀ δ k) :
    metricDerivENormSupOn (controlledCylinder δ) k d.normalizedMetric
      (referenceMetric δ) (referenceMetric δ) < ENNReal.ofReal δ := d.error_lt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.normalizedMetric_error_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.normalizedMetric_error_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.normalizedMetric_error_lt ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.normalizedMetric_error_lt

def retainedSign (d : normalizedDatum g x₀ δ k) : ℝ := if d.retainedSide then 1 else -1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.retainedSign then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.retainedSign"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.retainedSign ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.retainedSign

theorem retainedSign_sq (d : normalizedDatum g x₀ δ k) : d.retainedSign ^ 2 = 1 := by
  unfold retainedSign
  split_ifs <;> norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.retainedSign_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.retainedSign_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.retainedSign_sq ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.retainedSign_sq

end normalizedDatum
end DifferentialGeometry.Geometry.Neck

namespace DifferentialGeometry.Geometry.Neck

private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat_1 : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealProdEuclideanSpaceFinOfNat_differentialGeometry : Fact
    (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealProdEuclideanSpaceFinOfNat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealProdEuclideanSpaceFinOfNat_differentialGeometry target :: scope.openDecls } }

def roundCylinderDatum (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (k : ℕ)
    (side : Bool) : normalizedDatum (roundCylinderMetric (E := E3) (n := 2))
      (spherePoint, 0) δ k := by
  let φ : bufferedCylinder δ → S2 × ℝ := Subtype.val
  have hs : ContMDiff IC IC ∞ φ := contMDiff_subtype_val
  have hi : _root_.Function.Injective φ := Subtype.val_injective
  have hm : ∀ x, _root_.Function.Injective (mfderiv IC IC φ x) := by
    intro x v w hvw
    simpa only [φ, mfderiv_subtype_val, ContinuousLinearMap.id_apply] using! hvw
  have hscalar : metricScalarAt (roundCylinderMetric (E := E3) (n := 2))
      (spherePoint, 0) = 1 := by
    rw [metricScalarAt_roundCylinder]
    norm_num
  have hp : 0 < metricScalarAt (roundCylinderMetric (E := E3) (n := 2))
      (spherePoint, 0) := by rw [hscalar]; norm_num
  have hloc := isLocalDiffeomorph_of_injective_mfderiv φ hs hm (by rfl)
  have he : pullbackMetricOfInjectiveLocalDiffeomorph
      (scaleMetric _ hp (roundCylinderMetric (E := E3) (n := 2))) φ hloc hi =
        referenceMetric δ := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner, scaleMetric_inner, hscalar,
      one_mul, mfderiv_subtype_val]
    rfl
  refine
    { precision_pos := hδ
      precision_lt_one := hδ1
      map := φ
      smooth := hs
      injective := hi
      immersion := hm
      center_eq := rfl
      scalar_pos := hp
      retainedSide := side
      error_lt := ?_ }
  change metricDerivENormSupOn (controlledCylinder δ) k
    (pullbackMetricOfInjectiveLocalDiffeomorph
      (scaleMetric _ hp (roundCylinderMetric (E := E3) (n := 2))) φ hloc hi)
        (referenceMetric δ) (referenceMetric δ) < ENNReal.ofReal δ
  rw [he, metricDerivENormSupOn_self]
  exact ENNReal.ofReal_pos.mpr hδ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.roundCylinderDatum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.roundCylinderDatum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.roundCylinderDatum ``Submission.DifferentialGeometry.Geometry.Neck.roundCylinderDatum

theorem roundCylinderDatum_map (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (k : ℕ)
    (side : Bool) (x : bufferedCylinder δ) :
    (roundCylinderDatum δ hδ hδ1 k side).map x = x.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.roundCylinderDatum_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.roundCylinderDatum_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.roundCylinderDatum_map ``Submission.DifferentialGeometry.Geometry.Neck.roundCylinderDatum_map

theorem roundCylinderDatum_retainedSide (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (k : ℕ) (side : Bool) :
    (roundCylinderDatum δ hδ hδ1 k side).retainedSide = side := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.roundCylinderDatum_retainedSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.roundCylinderDatum_retainedSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.roundCylinderDatum_retainedSide ``Submission.DifferentialGeometry.Geometry.Neck.roundCylinderDatum_retainedSide

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fact (Module.finrank ℝ E = 3)]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Fact (Module.finrank ℝ F = 3)]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

structure datumIsometry {g : SmoothRiemannianMetric I M}
    {g' : SmoothRiemannianMetric J N} {x₀ : M} {x₀' : N} {δ : ℝ} {k : ℕ}
    (d : normalizedDatum g x₀ δ k) (d' : normalizedDatum g' x₀' δ k) where
  source : _root_.TopologicalSpace.Opens M
  target : _root_.TopologicalSpace.Opens N
  image_source : ∀ z, d.map z ∈ source
  image_target : ∀ z, d'.map z ∈ target
  equiv : source ≃ₘ⟮I, J⟯ target
  metric_eq : Diffeomorph.pullbackMetricCross (g'.restrictOpen target) equiv =
    g.restrictOpen source
  chart_eq : ∀ z, (equiv ⟨d.map z, image_source z⟩ : N) = d'.map z
  scalar_eq : metricScalarAt g' x₀' = metricScalarAt g x₀
  retainedSide_eq : d'.retainedSide = d.retainedSide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.datumIsometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.datumIsometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.datumIsometry ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry

namespace datumIsometry

variable {g : SmoothRiemannianMetric I M} {g' : SmoothRiemannianMetric J N}
  {x₀ : M} {x₀' : N} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k} {d' : normalizedDatum g' x₀' δ k}

theorem center_mem_source (F : datumIsometry d d') : x₀ ∈ F.source := by
  simpa only [d.center_eq] using F.image_source (cylinderCenter δ d.precision_pos)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.datumIsometry.center_mem_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.datumIsometry.center_mem_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.datumIsometry.center_mem_source ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.center_mem_source

theorem center_mem_target (F : datumIsometry d d') : x₀' ∈ F.target := by
  simpa only [d'.center_eq] using F.image_target (cylinderCenter δ d'.precision_pos)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.datumIsometry.center_mem_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.datumIsometry.center_mem_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.datumIsometry.center_mem_target ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.center_mem_target

theorem center_eq (F : datumIsometry d d') :
    (F.equiv ⟨x₀, F.center_mem_source⟩ : N) = x₀' := by
  simpa only [d.center_eq, d'.center_eq] using
    F.chart_eq (cylinderCenter δ d.precision_pos)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.datumIsometry.center_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.datumIsometry.center_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.datumIsometry.center_eq ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.center_eq

def refl (d : normalizedDatum g x₀ δ k) : datumIsometry d d where
  source := ⊤
  target := ⊤
  image_source := fun _ => Set.mem_univ _
  image_target := fun _ => Set.mem_univ _
  equiv := Diffeomorph.refl I (⊤ : _root_.TopologicalSpace.Opens M) ∞
  metric_eq := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [Diffeomorph.pullbackMetricCross_inner]
    change (g.restrictOpen ⊤).inner x (mfderiv I I id x v) (mfderiv I I id x w) = _
    rw [mfderiv_id]
    rfl
  chart_eq := fun _ => rfl
  scalar_eq := rfl
  retainedSide_eq := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.datumIsometry.refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.datumIsometry.refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.datumIsometry.refl ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.refl

end datumIsometry
end DifferentialGeometry.Geometry.Neck

namespace DifferentialGeometry.Geometry.Neck

theorem isCompact_controlledCylinder (δ : ℝ) : IsCompact (controlledCylinder δ) := by
  rw [Subtype.isCompact_iff]
  have he : (Subtype.val : bufferedCylinder δ → S2 × ℝ) '' controlledCylinder δ =
      (_root_.Set.univ : Set S2) ×ˢ _root_.Set.Icc (-δ⁻¹) δ⁻¹ := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨mem_univ _, hx⟩
    · intro hq
      have hb : q ∈ bufferedCylinder δ := by
        change -δ⁻¹ - 1 < q.2 ∧ q.2 < δ⁻¹ + 1
        constructor <;> linarith [hq.2.1, hq.2.2]
      exact ⟨⟨q, hb⟩, hq.2, rfl⟩
  rw [he]
  exact isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.isCompact_controlledCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.isCompact_controlledCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.isCompact_controlledCylinder ``Submission.DifferentialGeometry.Geometry.Neck.isCompact_controlledCylinder

theorem cylinderCenter_mem_controlledCylinder (δ : ℝ) (hδ : 0 < δ) :
    cylinderCenter δ hδ ∈ controlledCylinder δ := by
  change -δ⁻¹ ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ δ⁻¹
  constructor <;> have hi := inv_pos.mpr hδ <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.cylinderCenter_mem_controlledCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.cylinderCenter_mem_controlledCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.cylinderCenter_mem_controlledCylinder ``Submission.DifferentialGeometry.Geometry.Neck.cylinderCenter_mem_controlledCylinder

end DifferentialGeometry.Geometry.Neck
