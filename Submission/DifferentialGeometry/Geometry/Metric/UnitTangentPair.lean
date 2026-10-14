import Submission.DifferentialGeometry.Geometry.Metric.QuadraticBounds.Unit

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


abbrev SameBaseUnitTangentPair (g : SmoothRiemannianMetric I M) :=
  {p : MetricUnitTangent g × MetricUnitTangent g //
    MetricUnitTangent.base p.1 = MetricUnitTangent.base p.2}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair ``Submission.DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair

namespace SameBaseUnitTangentPair

variable (g : SmoothRiemannianMetric I M)


def base (p : SameBaseUnitTangentPair g) : M := MetricUnitTangent.base p.val.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.base then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.base"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.base ``Submission.DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.base


def first (p : SameBaseUnitTangentPair g) : TangentSpace I (base g p) :=
  MetricUnitTangent.vec p.val.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.first then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.first"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.first ``Submission.DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.first


def second (p : SameBaseUnitTangentPair g) : TangentSpace I (base g p) :=
  (MetricUnitTangent.vec p.val.2 : E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.second then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.second"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.second ``Submission.DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.second

omit [FiniteDimensional ℝ E] in
theorem continuous_base : Continuous (base g) :=
  (FiberBundle.continuous_proj E (TangentSpace I)).comp
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.continuous_base then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.continuous_base"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.continuous_base ``Submission.DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.continuous_base

omit [FiniteDimensional ℝ E] in
theorem continuous_first : Continuous (fun p : SameBaseUnitTangentPair g =>
    (⟨base g p, first g p⟩ : TangentBundle I M)) :=
  continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.continuous_first then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.continuous_first"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.continuous_first ``Submission.DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.continuous_first

omit [FiniteDimensional ℝ E] in
theorem continuous_second : Continuous (fun p : SameBaseUnitTangentPair g =>
    (⟨base g p, second g p⟩ : TangentBundle I M)) := by
  have h := continuous_subtype_val.comp (continuous_snd.comp
    (continuous_subtype_val : Continuous (Subtype.val : SameBaseUnitTangentPair g → _)))
  apply h.congr
  intro p
  apply TotalSpace.ext
  · exact p.property.symm
  · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.continuous_second then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.continuous_second"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.continuous_second ``Submission.DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.continuous_second

omit [FiniteDimensional ℝ E] in
theorem unit (p : SameBaseUnitTangentPair g) :
    g.inner (base g p) (first g p) (first g p) = 1 ∧
      g.inner (base g p) (second g p) (second g p) = 1 := by
  refine ⟨p.val.1.property, ?_⟩
  have h := p.val.2.property
  change g.inner (MetricUnitTangent.base p.val.2)
    (MetricUnitTangent.vec p.val.2) (MetricUnitTangent.vec p.val.2) = 1 at h
  unfold base second
  erw [p.property]
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.unit ``Submission.DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.unit

theorem compactSpace [T2Space M] [CompactSpace M] : CompactSpace (SameBaseUnitTangentPair g) := by
  let : CompactSpace (MetricUnitTangent g) :=
    isCompact_univ_iff.mp (metricUnit_compact g)
  have hb : Continuous (MetricUnitTangent.base (g := g)) :=
    (FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_subtype_val
  exact isCompact_iff_compactSpace.mp
    (isClosed_eq (hb.comp continuous_fst) (hb.comp continuous_snd)).isCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.compactSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.compactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.compactSpace ``Submission.DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.compactSpace

omit [FiniteDimensional ℝ E] in
theorem continuous_inner : Continuous (fun p : SameBaseUnitTangentPair g =>
    g.inner (base g p) (first g p) (second g p)) := by
  have h := Continuous.clm_bundle_apply₂ (𝕜 := ℝ) (E₃ := fun _ : M => ℝ) (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (g.contMDiff.continuous.comp (continuous_base g)) (continuous_first g) (continuous_second g)
  exact (continuous_snd.comp (Bundle.Trivial.homeomorphProd M ℝ).continuous).comp h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.continuous_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.continuous_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.continuous_inner ``Submission.DifferentialGeometry.Geometry.Riemannian.SameBaseUnitTangentPair.continuous_inner

end SameBaseUnitTangentPair

abbrev OrthonormalTangentPair (g : SmoothRiemannianMetric I M) :=
  {p : SameBaseUnitTangentPair g //
    g.inner (SameBaseUnitTangentPair.base g p)
      (SameBaseUnitTangentPair.first g p) (SameBaseUnitTangentPair.second g p) = 0}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.OrthonormalTangentPair then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.OrthonormalTangentPair"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.OrthonormalTangentPair ``Submission.DifferentialGeometry.Geometry.Riemannian.OrthonormalTangentPair


theorem orthonormalTangentPair_compactSpace [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) : CompactSpace (OrthonormalTangentPair g) := by
  let := SameBaseUnitTangentPair.compactSpace g
  exact isCompact_iff_compactSpace.mp
    (isClosed_eq (SameBaseUnitTangentPair.continuous_inner g) continuous_const).isCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.orthonormalTangentPair_compactSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.orthonormalTangentPair_compactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.orthonormalTangentPair_compactSpace ``Submission.DifferentialGeometry.Geometry.Riemannian.orthonormalTangentPair_compactSpace

end DifferentialGeometry.Geometry.Riemannian
