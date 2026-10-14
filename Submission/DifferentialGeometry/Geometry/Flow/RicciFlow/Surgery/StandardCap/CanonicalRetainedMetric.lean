import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckMarkSideBridge
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import Submission.DifferentialGeometry.Topology.Handle.Manifold
import Submission.DifferentialGeometry.Topology.Manifold.SmoothModelTransportSource
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Neck
open _root_.Submission.DifferentialGeometry.Topology.Handle
open _root_.Submission.DifferentialGeometry.Topology.Manifold
open _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
open _root_.Submission.DifferentialGeometry.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private abbrev IR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IR target :: scope.openDecls } }
private abbrev PM := ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat target :: scope.openDecls } }

def neckRetainedCollarHomeomorph (δ : ℝ) :
    neckRetainedCollar δ ≃ₜ Sphere 2 × _root_.Set.Ico (0 : ℝ) δ⁻¹ where
  toFun := fun x => (x.1.1, ⟨x.1.2, x.2⟩)
  invFun := fun p => ⟨(p.1, p.2.1), p.2.2⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => rfl
  continuous_toFun := Continuous.prodMk
    (continuous_fst.comp continuous_subtype_val)
    (Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) _)
  continuous_invFun := Continuous.subtype_mk
    (Continuous.prodMk continuous_fst (continuous_subtype_val.comp continuous_snd)) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckRetainedCollarHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckRetainedCollarHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckRetainedCollarHomeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckRetainedCollarHomeomorph

@[instance_reducible] def neckRetainedCollarChartedSpace {δ : ℝ} (hδ : 0 < δ) :
    ChartedSpace (EuclideanHalfSpace 3) (neckRetainedCollar δ) :=
  letI := halfClosedIntervalChartedSpace (inv_pos.mpr hδ)
  letI : ChartedSpace PM (neckRetainedCollar δ) :=
    chartedSpaceOfHomeomorph (neckRetainedCollarHomeomorph δ)
  euclideanHalfSpaceProdChartedSpace (neckRetainedCollar δ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckRetainedCollarChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckRetainedCollarChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckRetainedCollarChartedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckRetainedCollarChartedSpace

theorem neckRetainedCollar_isManifold {δ : ℝ} (hδ : 0 < δ) :
    letI := neckRetainedCollarChartedSpace hδ
    IsManifold (𝓡∂ 3) ∞ (neckRetainedCollar δ) := by
  let := halfClosedIntervalChartedSpace (inv_pos.mpr hδ)
  let := halfClosedInterval_isManifold (inv_pos.mpr hδ)
  let : ChartedSpace PM (neckRetainedCollar δ) :=
    chartedSpaceOfHomeomorph (neckRetainedCollarHomeomorph δ)
  let : IsManifold IR ∞ (neckRetainedCollar δ) :=
    isManifoldOfHomeomorph IR (neckRetainedCollarHomeomorph δ)
  exact euclideanHalfSpaceProd_isManifold (neckRetainedCollar δ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckRetainedCollar_isManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckRetainedCollar_isManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckRetainedCollar_isManifold ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckRetainedCollar_isManifold

def neckRetainedCollarDiffeomorph {δ : ℝ} (hδ : 0 < δ) :
    letI := halfClosedIntervalChartedSpace (inv_pos.mpr hδ)
    letI := neckRetainedCollarChartedSpace hδ
    neckRetainedCollar δ ≃ₘ⟮𝓡∂ 3, (𝓡 2).prod (𝓡∂ 1)⟯ Sphere 2 × _root_.Set.Ico (0 : ℝ) δ⁻¹ := by
  letI := halfClosedIntervalChartedSpace (inv_pos.mpr hδ)
  letI := halfClosedInterval_isManifold (inv_pos.mpr hδ)
  letI : ChartedSpace PM (neckRetainedCollar δ) :=
    chartedSpaceOfHomeomorph (neckRetainedCollarHomeomorph δ)
  letI : IsManifold IR ∞ (neckRetainedCollar δ) :=
    isManifoldOfHomeomorph IR (neckRetainedCollarHomeomorph δ)
  letI := euclideanHalfSpaceProdChartedSpace (neckRetainedCollar δ)
  exact
    { toEquiv := (neckRetainedCollarHomeomorph δ).toEquiv
      contMDiff_toFun :=
        (contMDiff_chartedSpaceTransHomeomorph_source_iff IR (𝓡∂ 3)
          euclideanHalfSpaceProdHomeomorph euclideanHalfSpaceProdCoordinates
          euclideanHalfSpaceProdHomeomorph_model IR).mpr
          (contMDiff_homeomorph_of_chartedSpaceOfHomeomorph
            (neckRetainedCollarHomeomorph δ) IR ∞)
      contMDiff_invFun :=
        (contMDiff_chartedSpaceTransHomeomorph_iff IR (𝓡∂ 3)
          euclideanHalfSpaceProdHomeomorph euclideanHalfSpaceProdCoordinates
          euclideanHalfSpaceProdHomeomorph_model IR).mpr
          (contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph
            (neckRetainedCollarHomeomorph δ) IR ∞) }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckRetainedCollarDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckRetainedCollarDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckRetainedCollarDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckRetainedCollarDiffeomorph


theorem neckRetainedCollar_inclusion_isSmoothEmbedding {δ : ℝ} (hδ : 0 < δ) :
    letI := neckRetainedCollarChartedSpace hδ
    _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) NeckCylinderModel ∞
      (Subtype.val : neckRetainedCollar δ → NeckCylinder) := by
  let := halfClosedIntervalChartedSpace (inv_pos.mpr hδ)
  let := halfClosedInterval_isManifold (inv_pos.mpr hδ)
  let : ChartedSpace PM (neckRetainedCollar δ) :=
    chartedSpaceOfHomeomorph (neckRetainedCollarHomeomorph δ)
  let : IsManifold IR ∞ (neckRetainedCollar δ) :=
    isManifoldOfHomeomorph IR (neckRetainedCollarHomeomorph δ)
  let Hd : neckRetainedCollar δ ≃ₘ⟮IR, IR⟯ Sphere 2 × _root_.Set.Ico (0 : ℝ) δ⁻¹ :=
    { toEquiv := (neckRetainedCollarHomeomorph δ).toEquiv
      contMDiff_toFun := contMDiff_homeomorph_of_chartedSpaceOfHomeomorph
        (neckRetainedCollarHomeomorph δ) IR ∞
      contMDiff_invFun := contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph
        (neckRetainedCollarHomeomorph δ) IR ∞ }
  have hp : _root_.Manifold.IsSmoothEmbedding IR NeckCylinderModel ∞
      (Prod.map (id : Sphere 2 → Sphere 2) (Subtype.val : _root_.Set.Ico (0 : ℝ) δ⁻¹ → ℝ)) :=
    (IsSmoothEmbedding.id (I := 𝓡 2) (M := Sphere 2)).prodMap
      (isSmoothEmbedding_halfClosedInterval_inclusion (inv_pos.mpr hδ))
  have hh := isSmoothEmbedding_diffeomorph_precomp _ hp Hd
  exact (isSmoothEmbedding_chartedSpaceTransHomeomorph_source_iff IR (𝓡∂ 3)
    euclideanHalfSpaceProdHomeomorph euclideanHalfSpaceProdCoordinates
    euclideanHalfSpaceProdHomeomorph_model NeckCylinderModel).mpr hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckRetainedCollar_inclusion_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckRetainedCollar_inclusion_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckRetainedCollar_inclusion_isSmoothEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.neckRetainedCollar_inclusion_isSmoothEmbedding

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.IR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.IR target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) := radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientChartedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientChartedSpace target :: scope.openDecls } }
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) := radialCapAttachment_isManifold transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientIsManifold
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientIsManifold target :: scope.openDecls } }

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k}
  {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}

namespace CanonicalStaticInsertionWitness

variable (w : CanonicalStaticInsertionWitness d A hA D m ε)

def retainedMap : C(neckRetainedCollar δ, InsertionQuotient (inv_pos.mpr d.precision_pos)) := by
  letI := halfClosedIntervalChartedSpace (inv_pos.mpr d.precision_pos)
  exact ⟨w.data.retainedInclusion ∘ neckRetainedCollarHomeomorph δ,
    w.properties.retained_embedding.contMDiff.continuous.comp
      (neckRetainedCollarHomeomorph δ).continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap


@[simp] theorem retainedMap_apply (x : neckRetainedCollar δ) :
    w.retainedMap x = w.data.retainedInclusion (x.1.1, ⟨x.1.2, x.2⟩) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap_apply


theorem retainedMap_range : _root_.Set.range w.retainedMap = _root_.Set.range w.data.retainedInclusion :=
  (neckRetainedCollarHomeomorph δ).surjective.range_comp w.data.retainedInclusion

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap_range ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap_range

theorem retainedMap_contMDiff :
    letI := neckRetainedCollarChartedSpace d.precision_pos
    ContMDiff (𝓡∂ 3) (𝓡 3) ∞ w.retainedMap := by
  let := halfClosedIntervalChartedSpace (inv_pos.mpr d.precision_pos)
  let := neckRetainedCollarChartedSpace d.precision_pos
  exact w.properties.retained_embedding.contMDiff.comp
    (neckRetainedCollarDiffeomorph d.precision_pos).contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap_contMDiff ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap_contMDiff

theorem retainedMap_mfderiv_injective :
    letI := neckRetainedCollarChartedSpace d.precision_pos
    ∀ x, _root_.Function.Injective (mfderiv (𝓡∂ 3) (𝓡 3) w.retainedMap x) := by
  let := halfClosedIntervalChartedSpace (inv_pos.mpr d.precision_pos)
  let := halfClosedInterval_isManifold (inv_pos.mpr d.precision_pos)
  let := neckRetainedCollarChartedSpace d.precision_pos
  let := neckRetainedCollar_isManifold d.precision_pos
  let Hd := neckRetainedCollarDiffeomorph d.precision_pos
  intro x
  change _root_.Function.Injective (mfderiv (𝓡∂ 3) (𝓡 3) (w.data.retainedInclusion ∘ Hd) x)
  rw [mfderiv_comp x
    (w.properties.retained_embedding.contMDiff.mdifferentiableAt (by simp))
    (Hd.contMDiff.mdifferentiableAt (by simp))]
  exact ((w.properties.retained_embedding.isImmersion.isImmersionAt (Hd x)).injective_mfderiv
    (by simp)).comp ((Hd.mfderivToContinuousLinearEquiv (by simp) x).injective)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap_mfderiv_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap_mfderiv_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap_mfderiv_injective ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap_mfderiv_injective


theorem retainedMap_isSmoothEmbedding :
    letI := neckRetainedCollarChartedSpace d.precision_pos
    IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ w.retainedMap := by
  let := halfClosedIntervalChartedSpace (inv_pos.mpr d.precision_pos)
  let := halfClosedInterval_isManifold (inv_pos.mpr d.precision_pos)
  let : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1))
      (neckRetainedCollar δ) := chartedSpaceOfHomeomorph (neckRetainedCollarHomeomorph δ)
  let : IsManifold IR ∞ (neckRetainedCollar δ) :=
    isManifoldOfHomeomorph IR (neckRetainedCollarHomeomorph δ)
  let Hd : neckRetainedCollar δ ≃ₘ⟮IR, IR⟯ Sphere 2 × _root_.Set.Ico (0 : ℝ) δ⁻¹ :=
    { toEquiv := (neckRetainedCollarHomeomorph δ).toEquiv
      contMDiff_toFun := contMDiff_homeomorph_of_chartedSpaceOfHomeomorph
        (neckRetainedCollarHomeomorph δ) IR ∞
      contMDiff_invFun := contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph
        (neckRetainedCollarHomeomorph δ) IR ∞ }
  have hh := isSmoothEmbedding_diffeomorph_precomp _ w.properties.retained_embedding Hd
  exact (isSmoothEmbedding_chartedSpaceTransHomeomorph_source_iff IR (𝓡∂ 3)
    euclideanHalfSpaceProdHomeomorph euclideanHalfSpaceProdCoordinates
    euclideanHalfSpaceProdHomeomorph_model (𝓡 3)).mpr hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap_isSmoothEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMap_isSmoothEmbedding

def retainedMetric :
    letI := neckRetainedCollarChartedSpace d.precision_pos
    letI := neckRetainedCollar_isManifold d.precision_pos
    SmoothRiemannianMetric (𝓡∂ 3) (neckRetainedCollar δ) := by
  letI := neckRetainedCollarChartedSpace d.precision_pos
  letI := neckRetainedCollar_isManifold d.precision_pos
  exact w.data.outMetric.pullback w.retainedMap w.retainedMap_contMDiff
    w.retainedMap_mfderiv_injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retainedMetric

theorem retained_metric_output :
    letI := neckRetainedCollarChartedSpace d.precision_pos
    letI := neckRetainedCollar_isManifold d.precision_pos
    ∀ x V W, w.retainedMetric.inner x V W =
      w.data.outMetric.inner (w.retainedMap x)
        (mfderiv (𝓡∂ 3) (𝓡 3) w.retainedMap x V)
        (mfderiv (𝓡∂ 3) (𝓡 3) w.retainedMap x W) := by
  let := neckRetainedCollarChartedSpace d.precision_pos
  let := neckRetainedCollar_isManifold d.precision_pos
  intro x V W
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retained_metric_output then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retained_metric_output"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retained_metric_output ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retained_metric_output

theorem retained_metric_input :
    letI := neckRetainedCollarChartedSpace d.precision_pos
    letI := neckRetainedCollar_isManifold d.precision_pos
    ∀ x V W, w.retainedMetric.inner x V W =
      g.inner ((d.oriented.positiveRetainedMap ∘ neckRetainedCollarHomeomorph δ) x)
        (mfderiv (𝓡∂ 3) I (d.oriented.positiveRetainedMap ∘ neckRetainedCollarHomeomorph δ) x V)
        (mfderiv (𝓡∂ 3) I
          (d.oriented.positiveRetainedMap ∘ neckRetainedCollarHomeomorph δ) x W) := by
  let := halfClosedIntervalChartedSpace (inv_pos.mpr d.precision_pos)
  let := halfClosedInterval_isManifold (inv_pos.mpr d.precision_pos)
  let := neckRetainedCollarChartedSpace d.precision_pos
  let := neckRetainedCollar_isManifold d.precision_pos
  let Hd := neckRetainedCollarDiffeomorph d.precision_pos
  intro x V W
  rw [w.retained_metric_output]
  change w.data.outMetric.inner ((w.data.retainedInclusion ∘ Hd) x)
    (mfderiv (𝓡∂ 3) (𝓡 3) (w.data.retainedInclusion ∘ Hd) x V)
    (mfderiv (𝓡∂ 3) (𝓡 3) (w.data.retainedInclusion ∘ Hd) x W) =
      g.inner ((d.oriented.positiveRetainedMap ∘ Hd) x)
        (mfderiv (𝓡∂ 3) I (d.oriented.positiveRetainedMap ∘ Hd) x V)
        (mfderiv (𝓡∂ 3) I (d.oriented.positiveRetainedMap ∘ Hd) x W)
  rw [mfderiv_comp x (w.properties.retained_embedding.contMDiff.mdifferentiableAt (by simp))
      (Hd.contMDiff.mdifferentiableAt (by simp)),
    mfderiv_comp x (d.oriented.positiveRetainedMap_smooth.mdifferentiableAt (by simp))
      (Hd.contMDiff.mdifferentiableAt (by simp))]
  exact w.properties.retained_metric (Hd x)
    (mfderiv (𝓡∂ 3) IR Hd x V) (mfderiv (𝓡∂ 3) IR Hd x W)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retained_metric_input then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retained_metric_input"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retained_metric_input ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retained_metric_input

end CanonicalStaticInsertionWitness
end DifferentialGeometry.PDE.RicciFlow.StandardCap

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric ThreeModel M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k}
  {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}

private def retainedBufferInclusion {δ : ℝ} (hδ : 0 < δ) :
    neckRetainedCollar δ → neckBuffer δ := fun y =>
  ⟨y.1, by
    have := inv_pos.mpr hδ
    constructor <;> linarith [y.2.1, y.2.2]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.retainedBufferInclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.retainedBufferInclusion target :: scope.openDecls } }

theorem CanonicalStaticInsertionWitness.retained_metric_input_neck
    (w : CanonicalStaticInsertionWitness d A hA D m ε) :
    letI := neckRetainedCollarChartedSpace d.precision_pos
    letI := neckRetainedCollar_isManifold d.precision_pos
    ∀ x V W,
      let inclusion : neckRetainedCollar δ → neckBuffer δ := fun y =>
        ⟨y.1, by
          have := inv_pos.mpr d.precision_pos
          constructor <;> linarith [y.2.1, y.2.2]⟩
      w.retainedMetric.inner x V W =
        g.inner (d.oriented.toNormalizedNeck.chart (inclusion x))
          (mfderiv (𝓡∂ 3) ThreeModel (d.oriented.toNormalizedNeck.chart ∘ inclusion) x V)
          (mfderiv (𝓡∂ 3) ThreeModel (d.oriented.toNormalizedNeck.chart ∘ inclusion) x W) := by
  let := neckRetainedCollarChartedSpace d.precision_pos
  let := neckRetainedCollar_isManifold d.precision_pos
  have he : d.oriented.positiveRetainedMap ∘ neckRetainedCollarHomeomorph δ =
      d.oriented.toNormalizedNeck.chart ∘ retainedBufferInclusion d.precision_pos := by
    funext y
    rfl
  intro x V W
  change w.retainedMetric.inner x V W =
    g.inner ((d.oriented.toNormalizedNeck.chart ∘ retainedBufferInclusion d.precision_pos) x)
      (mfderiv (𝓡∂ 3) ThreeModel
        (d.oriented.toNormalizedNeck.chart ∘ retainedBufferInclusion d.precision_pos) x V)
      (mfderiv (𝓡∂ 3) ThreeModel
        (d.oriented.toNormalizedNeck.chart ∘ retainedBufferInclusion d.precision_pos) x W)
  rw [← he]
  exact w.retained_metric_input x V W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retained_metric_input_neck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retained_metric_input_neck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retained_metric_input_neck ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.retained_metric_input_neck

end DifferentialGeometry.PDE.RicciFlow.StandardCap
