import Submission.DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Function _root_.Filter _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.SmoothBoundaryAtlas

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ} [NeZero n] {K : Set M} (C : SmoothBoundaryAtlas I n K)
  {F G X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  [TopologicalSpace X] [ChartedSpace G X]

theorem contMDiffWithinAt_iff_subtype_val (f : X → K) (s : Set X) (x : X) :
    let _ := C.toChartedSpace
    ContMDiffWithinAt J (𝓡∂ n) ∞ f s x ↔
      ContMDiffWithinAt J I ∞ (Subtype.val ∘ f) s x := by
  let _ := C.toChartedSpace
  constructor
  · intro hf
    exact C.contMDiff_subtype_val.contMDiffAt.comp_contMDiffWithinAt x hf
  · intro hf
    have hcont : ContinuousWithinAt f s x := Topology.IsInducing.subtypeVal.continuousWithinAt_iff.mpr hf.continuousWithinAt
    rw [contMDiffWithinAt_iff_target]
    refine ⟨hcont, ?_⟩
    have hc : ContMDiffAt I (𝓡 n) ∞ (C.ambientChart (f x)) (f x).val :=
      (C.ambientChart (f x)).contMDiffOn_toFun.contMDiffAt
        ((C.ambientChart (f x)).open_source.mem_nhds (C.mem_source (f x)))
    have h := hc.comp_contMDiffWithinAt x hf
    apply h.congr_of_eventuallyEq
    · filter_upwards [hcont ((C.chart (f x)).open_source.mem_nhds
        (C.mem_source (f x)))] with y hy
      change ((C.chart (f x)) (f y)).val = C.ambientChart (f x) ((f y).val)
      exact OpenPartialHomeomorph.restrictSubtypes_apply _ _ _ _ _ _ _ hy
    · change ((C.chart (f x)) (f x)).val = C.ambientChart (f x) ((f x).val)
      exact OpenPartialHomeomorph.restrictSubtypes_apply _ _ _ _ _ _ _ (C.mem_source (f x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothBoundaryAtlas.contMDiffWithinAt_iff_subtype_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothBoundaryAtlas.contMDiffWithinAt_iff_subtype_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothBoundaryAtlas.contMDiffWithinAt_iff_subtype_val ``Submission.DifferentialGeometry.Topology.SmoothBoundaryAtlas.contMDiffWithinAt_iff_subtype_val

theorem contMDiff_iff_subtype_val (f : X → K) :
    let _ := C.toChartedSpace
    ContMDiff J (𝓡∂ n) ∞ f ↔ ContMDiff J I ∞ (Subtype.val ∘ f) := by
  let _ := C.toChartedSpace
  simp only [ContMDiff, ContMDiffAt, C.contMDiffWithinAt_iff_subtype_val]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothBoundaryAtlas.contMDiff_iff_subtype_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothBoundaryAtlas.contMDiff_iff_subtype_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothBoundaryAtlas.contMDiff_iff_subtype_val ``Submission.DifferentialGeometry.Topology.SmoothBoundaryAtlas.contMDiff_iff_subtype_val

theorem contMDiffOn_iff_subtype_val (f : X → K) (s : Set X) :
    let _ := C.toChartedSpace
    ContMDiffOn J (𝓡∂ n) ∞ f s ↔ ContMDiffOn J I ∞ (Subtype.val ∘ f) s := by
  let _ := C.toChartedSpace
  simp only [ContMDiffOn, C.contMDiffWithinAt_iff_subtype_val]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothBoundaryAtlas.contMDiffOn_iff_subtype_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothBoundaryAtlas.contMDiffOn_iff_subtype_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothBoundaryAtlas.contMDiffOn_iff_subtype_val ``Submission.DifferentialGeometry.Topology.SmoothBoundaryAtlas.contMDiffOn_iff_subtype_val

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M']
  {m : ℕ} [NeZero m] {K' : Set M'} (C' : SmoothBoundaryAtlas I' m K')

def diffeomorphOfAmbient (D : M ≃ₘ⟮I, I'⟯ M') (hK : ∀ x, x ∈ K ↔ D x ∈ K') :
    let _ := C.toChartedSpace
    let _ := C'.toChartedSpace
    K ≃ₘ⟮𝓡∂ n, 𝓡∂ m⟯ K' := by
  let _ := C.toChartedSpace
  let _ := C'.toChartedSpace
  refine
    { toFun := fun x => ⟨D x.val, (hK x.val).mp x.property⟩
      invFun := fun y => ⟨D.symm y.val, (hK (D.symm y.val)).mpr (by simpa only [D.apply_symm_apply] using y.property)⟩
      left_inv := fun x => Subtype.ext (D.symm_apply_apply x.val)
      right_inv := fun y => Subtype.ext (D.apply_symm_apply y.val)
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · apply (C'.contMDiff_iff_subtype_val _).mpr
    exact D.contMDiff.comp C.contMDiff_subtype_val
  · apply (C.contMDiff_iff_subtype_val _).mpr
    exact D.symm.contMDiff.comp C'.contMDiff_subtype_val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothBoundaryAtlas.diffeomorphOfAmbient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothBoundaryAtlas.diffeomorphOfAmbient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothBoundaryAtlas.diffeomorphOfAmbient ``Submission.DifferentialGeometry.Topology.SmoothBoundaryAtlas.diffeomorphOfAmbient

@[simp] theorem diffeomorphOfAmbient_apply_val (D : M ≃ₘ⟮I, I'⟯ M')
    (hK : ∀ x, x ∈ K ↔ D x ∈ K') (x : K) :
    (C.diffeomorphOfAmbient C' D hK x).val = D x.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothBoundaryAtlas.diffeomorphOfAmbient_apply_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothBoundaryAtlas.diffeomorphOfAmbient_apply_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothBoundaryAtlas.diffeomorphOfAmbient_apply_val ``Submission.DifferentialGeometry.Topology.SmoothBoundaryAtlas.diffeomorphOfAmbient_apply_val

theorem diffeomorphOfAmbient_symm_apply_val (D : M ≃ₘ⟮I, I'⟯ M')
    (hK : ∀ x, x ∈ K ↔ D x ∈ K') (y : K') :
    let _ := C.toChartedSpace
    let _ := C'.toChartedSpace
    ((C.diffeomorphOfAmbient C' D hK).symm y).val = D.symm y.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothBoundaryAtlas.diffeomorphOfAmbient_symm_apply_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothBoundaryAtlas.diffeomorphOfAmbient_symm_apply_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothBoundaryAtlas.diffeomorphOfAmbient_symm_apply_val ``Submission.DifferentialGeometry.Topology.SmoothBoundaryAtlas.diffeomorphOfAmbient_symm_apply_val

end DifferentialGeometry.Topology.SmoothBoundaryAtlas
