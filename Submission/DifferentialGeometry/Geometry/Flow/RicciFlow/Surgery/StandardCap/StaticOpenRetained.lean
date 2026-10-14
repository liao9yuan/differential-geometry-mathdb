import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev OpenE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.OpenE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.OpenE3 target :: scope.openDecls } }
private abbrev OpenS2 := Metric.sphere (0 : OpenE3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.OpenS2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.OpenS2 target :: scope.openDecls } }
private abbrev OpenIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.OpenIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.OpenIC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealOpenE3HAddOfNat : Fact (Module.finrank ℝ OpenE3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealOpenE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealOpenE3HAddOfNat target :: scope.openDecls } }
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} : ChartedSpace OpenE3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientChartedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientChartedSpace target :: scope.openDecls } }
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientIsManifold
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientIsManifold target :: scope.openDecls } }

theorem insertionCylinder_subset_original {A B : ℝ} (hAB : 2 * A < B) :
    insertionCylinder A B ≤ openCylinder B := by
  intro q hq
  change -2 * A < q.2 ∧ q.2 < B at hq
  change -B < q.2 ∧ q.2 < B
  exact ⟨by linarith [hq.1], hq.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCylinder_subset_original then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCylinder_subset_original"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCylinder_subset_original ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionCylinder_subset_original

def insertionQuotientCollarMap {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) (hB : 0 < B) :
    insertionCylinder A B → InsertionQuotient hB :=
  (radialCapAttachmentDiffeomorph transitionEnd_pos hB).symm ∘ insertionMap hA hAB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionQuotientCollarMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionQuotientCollarMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionQuotientCollarMap ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionQuotientCollarMap

theorem contMDiff_insertionQuotientCollarMap {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) (hB : 0 < B) :
    ContMDiff OpenIC (𝓡 3) ∞ (insertionQuotientCollarMap hA hAB hB) :=
  (radialCapAttachmentDiffeomorph transitionEnd_pos hB).symm.contMDiff.comp (contMDiff_insertionMap hA hAB)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.contMDiff_insertionQuotientCollarMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.contMDiff_insertionQuotientCollarMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.contMDiff_insertionQuotientCollarMap ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.contMDiff_insertionQuotientCollarMap

theorem insertionQuotientCollarMap_radial {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) (hB : 0 < B)
    (q : insertionCylinder A B) :
    radialCapAttachmentDiffeomorph transitionEnd_pos hB (insertionQuotientCollarMap hA hAB hB q) =
      insertionMap hA hAB q := (radialCapAttachmentDiffeomorph transitionEnd_pos hB).apply_symm_apply _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionQuotientCollarMap_radial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionQuotientCollarMap_radial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionQuotientCollarMap_radial ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionQuotientCollarMap_radial

theorem insertionQuotientCollarMap_radial_mfderiv {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) (hB : 0 < B)
    (q : insertionCylinder A B) :
    (mfderiv (𝓡 3) (𝓡 3) (radialCapAttachmentDiffeomorph transitionEnd_pos hB)
      (insertionQuotientCollarMap hA hAB hB q)).comp
        (mfderiv OpenIC (𝓡 3) (insertionQuotientCollarMap hA hAB hB) q) =
          mfderiv OpenIC (𝓡 3) (insertionMap hA hAB) q := by
  let J := insertionQuotientCollarMap hA hAB hB
  let D := radialCapAttachmentDiffeomorph transitionEnd_pos hB
  have he : D ∘ J = insertionMap hA hAB := funext (insertionQuotientCollarMap_radial hA hAB hB)
  have hd := mfderiv_comp q (D.contMDiff.mdifferentiable (by simp) (J q))
    ((contMDiff_insertionQuotientCollarMap hA hAB hB).mdifferentiable (by simp) q)
  rw [he] at hd
  exact hd.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionQuotientCollarMap_radial_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionQuotientCollarMap_radial_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionQuotientCollarMap_radial_mfderiv ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionQuotientCollarMap_radial_mfderiv

theorem injective_insertionQuotientCollarMap {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) (hB : 0 < B) :
    Injective (insertionQuotientCollarMap hA hAB hB) :=
  (radialCapAttachmentDiffeomorph transitionEnd_pos hB).symm.injective.comp (injective_insertionMap hA hAB)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.injective_insertionQuotientCollarMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.injective_insertionQuotientCollarMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.injective_insertionQuotientCollarMap ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.injective_insertionQuotientCollarMap

theorem insertionQuotientCollarMap_mfderiv_injective {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) (hB : 0 < B)
    (q : insertionCylinder A B) :
    Injective (mfderiv OpenIC (𝓡 3) (insertionQuotientCollarMap hA hAB hB) q) := by
  have he := insertionQuotientCollarMap_radial_mfderiv hA hAB hB q
  intro v w hvw
  apply insertionMap_mfderiv_injective hA hAB q
  have hd := congrArg (mfderiv (𝓡 3) (𝓡 3) (radialCapAttachmentDiffeomorph transitionEnd_pos hB)
    (insertionQuotientCollarMap hA hAB hB q)) hvw
  exact (congrArg (fun D => D v) he).symm.trans (hd.trans (congrArg (fun D => D w) he))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionQuotientCollarMap_mfderiv_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionQuotientCollarMap_mfderiv_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionQuotientCollarMap_mfderiv_injective ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionQuotientCollarMap_mfderiv_injective

theorem isLocalDiffeomorph_insertionQuotientCollarMap {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) (hB : 0 < B) :
    IsLocalDiffeomorph OpenIC (𝓡 3) ∞ (insertionQuotientCollarMap hA hAB hB) :=
  DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    (contMDiff_insertionQuotientCollarMap hA hAB hB)
    (insertionQuotientCollarMap_mfderiv_injective hA hAB hB) (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.isLocalDiffeomorph_insertionQuotientCollarMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.isLocalDiffeomorph_insertionQuotientCollarMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.isLocalDiffeomorph_insertionQuotientCollarMap ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.isLocalDiffeomorph_insertionQuotientCollarMap

theorem insertionQuotientCollarMap_retained {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) (hB : 0 < B)
    (q : insertionCylinder A B) (hq : 0 ≤ q.val.2) :
    insertionQuotientCollarMap hA hAB hB q =
      adjunctionLower (i := radialCapBoundary transitionEnd_pos) (retainedBoundary hB)
        (q.val.1, ⟨q.val.2, hq, q.property.2⟩) := by
  apply (radialCapAttachmentDiffeomorph transitionEnd_pos hB).injective
  apply Subtype.ext
  have hh := congrArg Subtype.val (insertionQuotientCollarMap_radial hA hAB hB q)
  refine hh.trans ?_
  change conformalRadius q.val.2 • q.val.1.val = (transitionEnd + q.val.2) • q.val.1.val
  rw [conformalRadius_cylindrical hq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionQuotientCollarMap_retained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionQuotientCollarMap_retained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionQuotientCollarMap_retained ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionQuotientCollarMap_retained

theorem insertedQuotientMetric_openRetained {A B η : ℝ} (hA : 0 < A) (hAB : 2 * A < B) (hB : 0 < B)
    (hη : 0 < η) (h : SmoothRiemannianMetric OpenIC (openCylinder B))
    (q : insertionCylinder A B) (hq : 0 ≤ q.val.2) (v w : TangentSpace OpenIC q) :
    (insertedQuotientMetric hA hAB hη h).inner (insertionQuotientCollarMap hA hAB hB q)
      (mfderiv OpenIC (𝓡 3) (insertionQuotientCollarMap hA hAB hB) q v)
      (mfderiv OpenIC (𝓡 3) (insertionQuotientCollarMap hA hAB hB) q w) =
        h.inner (Opens.inclusion (insertionCylinder_subset_original hAB) q) v w := by
  have hd := insertionQuotientCollarMap_radial_mfderiv hA hAB hB q
  have hv := congrArg (fun D => D v) hd
  have hw := congrArg (fun D => D w) hd
  rw [insertedQuotientMetric_inner]
  erw [hv, hw, insertionQuotientCollarMap_radial]
  exact insertedMetric_retained hA hAB hη h q hq v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedQuotientMetric_openRetained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedQuotientMetric_openRetained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedQuotientMetric_openRetained ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedQuotientMetric_openRetained

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

theorem physicalInsertionMetric_openRetained (d : normalizedDatum g x₀ δ k)
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹)
    (q : insertionCylinder A δ⁻¹) (hq : 0 ≤ q.val.2) (v w : TangentSpace OpenIC q) :
    (d.positiveSideInsertionMetric hA hAB).inner
      (insertionQuotientCollarMap hA hAB (inv_pos.mpr d.precision_pos) q)
      (mfderiv OpenIC (𝓡 3) (insertionQuotientCollarMap hA hAB (inv_pos.mpr d.precision_pos)) q v)
      (mfderiv OpenIC (𝓡 3) (insertionQuotientCollarMap hA hAB (inv_pos.mpr d.precision_pos)) q w) =
        g.inner (d.controlledMap (Opens.inclusion (insertionCylinder_subset_original hAB) q))
          (mfderiv OpenIC I d.controlledMap (Opens.inclusion (insertionCylinder_subset_original hAB) q) v)
          (mfderiv OpenIC I d.controlledMap (Opens.inclusion (insertionCylinder_subset_original hAB) q) w) := by
  simp only [normalizedDatum.positiveSideInsertionMetric, scaleMetric_inner]
  erw [insertedQuotientMetric_openRetained hA hAB (inv_pos.mpr d.precision_pos) _ _ q hq,
    normalizedDatum.controlledMetric_inner]
  rw [← mul_assoc, inv_mul_cancel₀ d.scalar_pos.ne', one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.physicalInsertionMetric_openRetained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.physicalInsertionMetric_openRetained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.physicalInsertionMetric_openRetained ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.physicalInsertionMetric_openRetained

theorem staticWitness_openRetained (d : normalizedDatum g x₀ δ k)
    {A D ε : ℝ} {hA : 0 < A} {m : ℕ} (s : CanonicalStaticInsertionWitness d A hA D m ε)
    (q : insertionCylinder A δ⁻¹) (hq : 0 ≤ q.val.2) (v w : TangentSpace OpenIC q) :
    s.data.outMetric.inner (insertionQuotientCollarMap hA s.properties.cut_fit (inv_pos.mpr d.precision_pos) q)
      (mfderiv OpenIC (𝓡 3) (insertionQuotientCollarMap hA s.properties.cut_fit (inv_pos.mpr d.precision_pos)) q v)
      (mfderiv OpenIC (𝓡 3) (insertionQuotientCollarMap hA s.properties.cut_fit (inv_pos.mpr d.precision_pos)) q w) =
        g.inner (d.oriented.controlledMap (Opens.inclusion (insertionCylinder_subset_original s.properties.cut_fit) q))
          (mfderiv OpenIC I d.oriented.controlledMap (Opens.inclusion (insertionCylinder_subset_original s.properties.cut_fit) q) v)
          (mfderiv OpenIC I d.oriented.controlledMap (Opens.inclusion (insertionCylinder_subset_original s.properties.cut_fit) q) w) := by
  rw [s.properties.outMetric_eq]
  exact physicalInsertionMetric_openRetained d.oriented hA s.properties.cut_fit q hq v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.staticWitness_openRetained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.staticWitness_openRetained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.staticWitness_openRetained ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.staticWitness_openRetained
end DifferentialGeometry.PDE.RicciFlow.StandardCap
