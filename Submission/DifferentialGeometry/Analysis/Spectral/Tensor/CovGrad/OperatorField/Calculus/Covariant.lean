import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.EvaluationLeibniz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection.Realization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.TensorMultilinear
open _root_.Submission.DifferentialGeometry.TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
omit [CompleteSpace E] in
theorem riemannianFiberNormSq_comp_clm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (φ : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) :
    ∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ W : TensorRSSpace 0 r I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (show TensorRSSpace 0 s I x from
          φ.comp (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W)) ≤
        Cφ * riemannianFiberNormSq (I := I) (M := M) g 0 r x W := by
  let instSource : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 r I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g 0 r
  let instTarget : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g 0 s
  let appOp : TensorRSSpace 0 r I x →L[ℝ] TensorRSSpace 0 s I x :=
    LinearMap.toContinuousLinearMap
      { toFun := fun W => (show TensorRSSpace 0 s I x from
          φ.comp (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W))
        map_add' := fun W₁ W₂ => ContinuousLinearMap.comp_add φ _ _
        map_smul' := fun c W => ContinuousLinearMap.comp_smul φ c _ }
  obtain ⟨Cφ, hCφ_nn, hCφ⟩ :=
    riemannianFiberNormSq_clm_apply_le (I := I) (M := M) g r s x appOp
  refine ⟨Cφ, hCφ_nn, fun W => ?_⟩
  have happ : appOp W = (show TensorRSSpace 0 s I x from
      φ.comp (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W)) := rfl
  rw [← happ]
  exact hCφ W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_comp_clm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_comp_clm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_comp_clm_le ``Submission.DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_comp_clm_le

def operatorFieldApplyPointwise (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) (x : M) :
    TensorRSSpace 0 s I x :=
  (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.operatorFieldApplyPointwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.operatorFieldApplyPointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.operatorFieldApplyPointwise ``Submission.DifferentialGeometry.Analysis.Spectral.operatorFieldApplyPointwise

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] [CompleteSpace E] in
theorem operatorFieldApplyPointwise_contMDiff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) x
        (operatorFieldApplyPointwise (I := I) (M := M) g r s Φ W x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 0 ℝ E) (V₁ := fun x : M => Tensor0SSpace 0 I x)
    (F₂ := Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SSpace s I x)
    (φ := fun x => operatorFieldApplyPointwise (I := I) (M := M) g r s Φ W x)
  intro Y
  have heq : (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
      (E := fun z : M => Tensor0SSpace s I z) x
      (operatorFieldApplyPointwise (I := I) (M := M) g r s Φ W x (Y x))) =
      (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
      (E := fun z : M => Tensor0SSpace s I z) x
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) (Y x)))) := by
    funext x; rfl
  rw [heq]
  have hWY : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SSpace r I z) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) (Y x))) :=
    ContMDiff.clm_bundle_apply (b := id) W.toSection.contMDiff Y.contMDiff
  exact ContMDiff.clm_bundle_apply (b := id) Φ.toSection.contMDiff hWY

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.operatorFieldApplyPointwise_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.operatorFieldApplyPointwise_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.operatorFieldApplyPointwise_contMDiff ``Submission.DifferentialGeometry.Analysis.Spectral.operatorFieldApplyPointwise_contMDiff

def operatorFieldApply (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) : SmoothCcTensor g 0 s where
  toSection :=
    { toFun := fun x : M => operatorFieldApplyPointwise (I := I) (M := M) g r s Φ W x
      contMDiff_toFun := operatorFieldApplyPointwise_contMDiff (I := I) (M := M) g r s Φ W }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.operatorFieldApply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.operatorFieldApply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.operatorFieldApply ``Submission.DifferentialGeometry.Analysis.Spectral.operatorFieldApply

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M]
    [CompleteSpace E] in
@[simp] lemma operatorFieldApplication_toSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) (x : M) :
    (operatorFieldApply (I := I) (M := M) g r s Φ W).toSection x =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_toSection ``Submission.DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_toSection

def slotExtendPointwise (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) :
    Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace (r + 1) I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s x).symm
          (A.comp ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x) D))
      map_add' := fun D₁ D₂ => by
        rw [map_add (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x),
          ContinuousLinearMap.comp_add, map_add
            (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s x).symm]
      map_smul' := fun c D => by
        rw [map_smul (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x),
          ContinuousLinearMap.comp_smul, map_smul
            (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s x).symm]
        rfl }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.slotExtendPointwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.slotExtendPointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.slotExtendPointwise ``Submission.DifferentialGeometry.Analysis.Spectral.slotExtendPointwise

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
@[simp] lemma slotExtendFib_apply (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) (D : Tensor0SSpace (r + 1) I x) :
    slotExtendPointwise (I := I) (M := M) r s x A D =
      (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        (A.comp ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x) D)) := by
  rw [slotExtendPointwise, LinearMap.coe_toContinuousLinearMap']
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.slotExtendFib_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.slotExtendFib_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.slotExtendFib_apply ``Submission.DifferentialGeometry.Analysis.Spectral.slotExtendFib_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
lemma slotExtendFib_apply_eval (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) (D : Tensor0SSpace (r + 1) I x)
    (v0 : E) (vs : Fin s → E) :
    Tensor0SSpace.toModel (slotExtendPointwise (I := I) (M := M) r s x A D) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        (A ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x) D
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v0))) vs := by
  rw [← TensorMultilinear.tensor0S_curry_toModel_apply (I := I) (M := M) (n := s)
    (slotExtendPointwise (I := I) (M := M) r s x A D) v0 vs]
  have hcurry : tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s x
      (slotExtendPointwise (I := I) (M := M) r s x A D) =
      A.comp ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x) D) := by
    rw [slotExtendFib_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [hcurry]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.slotExtendFib_apply_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.slotExtendFib_apply_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.slotExtendFib_apply_eval ``Submission.DifferentialGeometry.Analysis.Spectral.slotExtendFib_apply_eval

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
lemma slotExtendFib_apply_natural (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) (D : Tensor0SSpace (r + 1) I x)
    (v0 : TangentSpace I x) (vs : Fin s → TangentSpace I x) :
    Tensor0SSpace.eval (slotExtendPointwise (I := I) (M := M) r s x A D) (Fin.cons v0 vs) =
      Tensor0SSpace.eval
        (A ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x) D v0)) vs := by
  rw [← TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := slotExtendPointwise (I := I) (M := M) r s x A D) (v0 := v0) (vs := vs)]
  rw [slotExtendFib_apply, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearMap.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.slotExtendFib_apply_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.slotExtendFib_apply_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.slotExtendFib_apply_natural ``Submission.DifferentialGeometry.Analysis.Spectral.slotExtendFib_apply_natural

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
theorem contMDiff_uncurriedSection_of_contMDiff_homSection {n : ℕ}
    (G : ∀ b : M, TangentSpace I b →L[ℝ] Tensor0SSpace n I b)
    (hG : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel n ℝ E)) ∞
      (fun b : M =>
        TotalSpace.mk' (E →L[ℝ] Tensor0SModel n ℝ E)
          (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y) b (G b))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (n + 1) ℝ E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel (n + 1) ℝ E)
          (E := fun y : M => Tensor0SSpace (n + 1) I y) b
          ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) n b).symm (G b))) := by
  let : TopologicalSpace (_root_.Bundle.TotalSpace (Tensor0SModel (n + 1) ℝ E)
      (fun y : M => Tensor0SSpace (n + 1) I y)) :=
    tensor0SBundleTopology (n + 1)
  intro x
  rw [Bundle.contMDiffAt_section (F := Tensor0SModel (n + 1) ℝ E)
    (E := fun y : M => Tensor0SSpace (n + 1) I y)]
  have hG_at := (Bundle.contMDiffAt_section (F := E →L[ℝ] Tensor0SModel n ℝ E)
    (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y) x).mp (hG x)
  have huncurry :
      ContMDiff 𝓘(ℝ, E →L[ℝ] Tensor0SModel n ℝ E) 𝓘(ℝ, Tensor0SModel (n + 1) ℝ E)
        (∞ : WithTop ℕ∞)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ).symm :=
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ
      ).toContinuousLinearEquiv.symm.toContinuousLinearMap).contMDiff
  have hcomp := huncurry.contMDiffAt.comp x hG_at
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [(_root_.FiberBundle.trivializationAt (Tensor0SModel n ℝ E)
    (fun y : M => Tensor0SSpace n I y) x).open_baseSet.mem_nhds
    (_root_.FiberBundle.mem_baseSet_trivializationAt _ _ _)] with b hb
  have hUcurry : curriedSection (I := I) (M := M)
      (fun y : M => (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) n y).symm (G y)) b = G b := by
    rw [curriedSection]
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  have hfwd := trivializationAt_homBundle_curriedSection_eq (I := I) (M := M)
    (fun y : M => (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) n y).symm (G y)) x b hb
  rw [hUcurry] at hfwd
  change (_root_.FiberBundle.trivializationAt (Tensor0SModel (n + 1) ℝ E)
      (fun y : M => Tensor0SSpace (n + 1) I y) x
      ⟨b, (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) n b).symm (G b)⟩).2 =
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ).symm
      ((_root_.FiberBundle.trivializationAt (E →L[ℝ] Tensor0SModel n ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] Tensor0SSpace n I y) x ⟨b, G b⟩).2)
  rw [hfwd]
  exact (LinearIsometryEquiv.symm_apply_apply
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ) _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.contMDiff_uncurriedSection_of_contMDiff_homSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.contMDiff_uncurriedSection_of_contMDiff_homSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.contMDiff_uncurriedSection_of_contMDiff_homSection ``Submission.DifferentialGeometry.Analysis.Spectral.contMDiff_uncurriedSection_of_contMDiff_homSection

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] [CompleteSpace E] in
theorem slotExtendFib_contMDiff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel (r + 1) (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel (r + 1) (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace (r + 1) (s + 1) I z) x
        (slotExtendPointwise (I := I) (M := M) r s x
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel (r + 1) ℝ E) (V₁ := fun x : M => Tensor0SSpace (r + 1) I x)
    (F₂ := Tensor0SModel (s + 1) ℝ E) (V₂ := fun x : M => Tensor0SSpace (s + 1) I x)
    (φ := fun x => slotExtendPointwise (I := I) (M := M) r s x
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x))
  intro Y
  have heq : (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SSpace (s + 1) I z) x
      (slotExtendPointwise (I := I) (M := M) r s x
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x) (Y x))) =
      (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
      (E := fun z : M => Tensor0SSpace (s + 1) I z) x
      ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
          ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x) (Y x))))) := by
    funext x
    rw [slotExtendFib_apply]
  rw [heq]
  have hG : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace s I z) x
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
          ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x) (Y x)))) := by
    apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
      (F₂ := Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SSpace s I x)
      (φ := fun x => (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
        ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x) (Y x)))
    intro Z
    have heqZ : (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        (((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
          ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x) (Y x))) (Z x))) =
        (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
          ((curriedSection (I := I) (M := M) (fun y : M => Y y) x) (Z x)))) := by
      funext x; rfl
    rw [heqZ]
    have hcurriedY : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel r ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel r ℝ E)
          (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace r I z) x
          (curriedSection (I := I) (M := M) (fun y : M => Y y) x)) :=
      fun x => contMDiffAt_curriedSection_of_contMDiffAt_section (I := I) (M := M)
        (fun y : M => Y y) x (Y.contMDiff x)
    have hinner : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
          (E := fun z : M => Tensor0SSpace r I z) x
          ((curriedSection (I := I) (M := M) (fun y : M => Y y) x) (Z x))) :=
      ContMDiff.clm_bundle_apply (b := id) hcurriedY Z.contMDiff
    exact ContMDiff.clm_bundle_apply (b := id) Φ.toSection.contMDiff hinner
  exact contMDiff_uncurriedSection_of_contMDiff_homSection (I := I) (M := M)
    (fun x : M => (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
      ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x) (Y x))) hG

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.slotExtendFib_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.slotExtendFib_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.slotExtendFib_contMDiff ``Submission.DifferentialGeometry.Analysis.Spectral.slotExtendFib_contMDiff

def slotExtend (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) : SmoothCcTensor g (r + 1) (s + 1) where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace (r + 1) (s + 1) I x from
          slotExtendPointwise (I := I) (M := M) r s x
            (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x))
      contMDiff_toFun := slotExtendFib_contMDiff (I := I) (M := M) g r s Φ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.slotExtend then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.slotExtend"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.slotExtend ``Submission.DifferentialGeometry.Analysis.Spectral.slotExtend

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M]
    [CompleteSpace E] in
@[simp] lemma slotExtend_toSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (x : M) :
    (slotExtend (I := I) (M := M) g r s Φ).toSection x =
      (show TensorRSSpace (r + 1) (s + 1) I x from
        slotExtendPointwise (I := I) (M := M) r s x
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.slotExtend_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.slotExtend_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.slotExtend_toSection ``Submission.DifferentialGeometry.Analysis.Spectral.slotExtend_toSection

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M]
    [CompleteSpace E] in
theorem slotExtend_sub (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : SmoothCcTensor g r s) :
    slotExtend (I := I) (M := M) g r s (X - Y) =
      slotExtend (I := I) (M := M) g r s X - slotExtend (I := I) (M := M) g r s Y := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((slotExtend (I := I) (M := M) g r s X -
        slotExtend (I := I) (M := M) g r s Y).toSection x) =
      (slotExtend (I := I) (M := M) g r s X).toSection x -
        (slotExtend (I := I) (M := M) g r s Y).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [sub_apply]
  rw [show ((slotExtend (I := I) (M := M) g r s (X - Y)).toSection x) D =
      (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          (X - Y).toSection x).comp
          (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
  rw [show ((slotExtend (I := I) (M := M) g r s X).toSection x) D =
      (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X.toSection x).comp
          (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
  rw [show ((slotExtend (I := I) (M := M) g r s Y).toSection x) D =
      (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Y.toSection x).comp
          (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
  rw [show ((X - Y).toSection x) = X.toSection x - Y.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [show ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      X.toSection x - Y.toSection x).comp
      (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x D)) =
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X.toSection x).comp
        (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x D)) -
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Y.toSection x).comp
        (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x D)) from by
    apply ContinuousLinearMap.ext
    intro w
    rfl]
  rw [map_sub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.slotExtend_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.slotExtend_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.slotExtend_sub ``Submission.DifferentialGeometry.Analysis.Spectral.slotExtend_sub

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M]
    [CompleteSpace E] in
theorem operatorFieldApplication_add_right (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W₁ W₂ : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s Φ (W₁ + W₂) =
      operatorFieldApply (I := I) (M := M) g r s Φ W₁ + operatorFieldApply (I := I) (M := M) g r s Φ
        W₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((operatorFieldApply (I := I) (M := M) g r s Φ W₁ + operatorFieldApply (I := I) (M := M)
    g r s Φ W₂).toSection x) =
      (operatorFieldApply (I := I) (M := M) g r s Φ W₁).toSection x +
        (operatorFieldApply (I := I) (M := M) g r s Φ W₂).toSection x from rfl]
  rw [operatorFieldApplication_toSection, operatorFieldApplication_toSection, operatorFieldApplication_toSection]
  rw [show ((W₁ + W₂).toSection x : TensorRSSpace 0 r I x) = W₁.toSection x + W₂.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.comp_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_add_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_add_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_add_right ``Submission.DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_add_right

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M]
    [CompleteSpace E] in
theorem operatorFieldApplication_smul_right (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s Φ (c • W) =
      c • operatorFieldApply (I := I) (M := M) g r s Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • operatorFieldApply (I := I) (M := M) g r s Φ W).toSection x) =
      c • (operatorFieldApply (I := I) (M := M) g r s Φ W).toSection x from rfl]
  rw [operatorFieldApplication_toSection, operatorFieldApplication_toSection]
  rw [show ((c • W).toSection x : TensorRSSpace 0 r I x) = c • W.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.comp_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_smul_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_smul_right ``Submission.DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_smul_right

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] [CompleteSpace E] in
theorem operatorFieldApplication_zero_right (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) :
    operatorFieldApply (I := I) (M := M) g r s Φ (0 : SmoothCcTensor g 0 r) = 0 := by
  simpa using operatorFieldApplication_smul_right (I := I) (M := M) g r s
    (0 : ℝ) Φ (0 : SmoothCcTensor g 0 r)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_zero_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_zero_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_zero_right ``Submission.DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_zero_right

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] [CompleteSpace E] in
theorem operatorFieldApplication_neg_right (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s Φ (-W) =
      -operatorFieldApply (I := I) (M := M) g r s Φ W := by
  simpa using operatorFieldApplication_smul_right (I := I) (M := M) g r s
    (-1 : ℝ) Φ W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_neg_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_neg_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_neg_right ``Submission.DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_neg_right

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] [CompleteSpace E] in
theorem operatorFieldApplication_sub_right (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W₁ W₂ : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s Φ (W₁ - W₂) =
      operatorFieldApply (I := I) (M := M) g r s Φ W₁ -
        operatorFieldApply (I := I) (M := M) g r s Φ W₂ := by
  rw [sub_eq_add_neg, operatorFieldApplication_add_right,
    operatorFieldApplication_neg_right, sub_eq_add_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_sub_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_sub_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_sub_right ``Submission.DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_sub_right

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M]
    [CompleteSpace E] in
theorem operatorFieldApplication_smul_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s (c • Φ) W =
      c • operatorFieldApply (I := I) (M := M) g r s Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • operatorFieldApply (I := I) (M := M) g r s Φ W).toSection x) =
      c • (operatorFieldApply (I := I) (M := M) g r s Φ W).toSection x from rfl]
  rw [operatorFieldApplication_toSection, operatorFieldApplication_toSection]
  rw [show ((c • Φ).toSection x : TensorRSSpace r s I x) = c • Φ.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.smul_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_smul_left ``Submission.DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_smul_left

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M]
    [CompleteSpace E] in
theorem operatorFieldApplication_add_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s (Φ₁ + Φ₂) W =
      operatorFieldApply (I := I) (M := M) g r s Φ₁ W + operatorFieldApply (I := I) (M := M) g r s
        Φ₂ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((operatorFieldApply (I := I) (M := M) g r s Φ₁ W + operatorFieldApply (I := I) (M := M)
    g r s Φ₂ W).toSection x) =
      (operatorFieldApply (I := I) (M := M) g r s Φ₁ W).toSection x +
        (operatorFieldApply (I := I) (M := M) g r s Φ₂ W).toSection x from rfl]
  rw [operatorFieldApplication_toSection, operatorFieldApplication_toSection, operatorFieldApplication_toSection]
  rw [show ((Φ₁ + Φ₂).toSection x : TensorRSSpace r s I x) = Φ₁.toSection x + Φ₂.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_add_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_add_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_add_left ``Submission.DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_add_left

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] [CompleteSpace E] in
theorem operatorFieldApplication_zero_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) (g := g) r s (0 : SmoothCcTensor g r s) W = 0 := by
  have h := operatorFieldApplication_add_left (I := I) (M := M) g r s
    (0 : SmoothCcTensor g r s) 0 W
  rw [add_zero] at h
  have h2 : operatorFieldApply (I := I) (M := M) (g := g) r s
      (0 : SmoothCcTensor g r s) W -
        operatorFieldApply (I := I) (M := M) (g := g) r s
          (0 : SmoothCcTensor g r s) W =
      operatorFieldApply (I := I) (M := M) (g := g) r s
        (0 : SmoothCcTensor g r s) W := by
    nth_rewrite 1 [h]
    abel
  rwa [sub_self] at h2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_zero_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_zero_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_zero_left ``Submission.DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_zero_left

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] [CompleteSpace E] in
theorem operatorFieldApplication_neg_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) (g := g) r s (-Φ) W =
      -operatorFieldApply (I := I) (M := M) (g := g) r s Φ W := by
  have h := operatorFieldApplication_add_left (I := I) (M := M) g r s Φ (-Φ) W
  rw [add_neg_cancel, operatorFieldApplication_zero_left] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_neg_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_neg_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_neg_left ``Submission.DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_neg_left

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] [CompleteSpace E] in
theorem operatorFieldApplication_sub_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) (g := g) r s (Φ₁ - Φ₂) W =
      operatorFieldApply (I := I) (M := M) (g := g) r s Φ₁ W -
        operatorFieldApply (I := I) (M := M) (g := g) r s Φ₂ W := by
  rw [sub_eq_add_neg, operatorFieldApplication_add_left,
    operatorFieldApplication_neg_left, sub_eq_add_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_sub_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_sub_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_sub_left ``Submission.DifferentialGeometry.Analysis.Spectral.operatorFieldApplication_sub_left

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem tensorCovDerivAt_operatorFieldApplication_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) (x : M) (v : E) :
    (show TensorRSSpace 0 s I x from
        tensorCovDerivAt (I := I) (M := M) g 0 s (operatorFieldApply (I := I) (M := M) g r s Φ W) x
          v) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g r s Φ x v).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) +
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
            tensorCovDerivAt (I := I) (M := M) g 0 r W x v) := by
  apply ContinuousLinearMap.ext
  intro d
  obtain ⟨dSec, hdSec⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 0 ℝ E) (V := fun y : M => Tensor0SSpace 0 I y) (n := (⊤ : ℕ∞)) x d
  have hWd_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SSpace r I z) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace r I y from W.toSection y) (dSec y))) :=
    ContMDiff.clm_bundle_apply (b := id) W.toSection.contMDiff dSec.contMDiff
  let Wd : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun y : M => Tensor0SSpace r I y)⟯ :=
    ⟨fun y : M => (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace r I y from W.toSection y) (dSec y),
      hWd_smooth⟩
  have hLHS :
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g 0 s (operatorFieldApply (I := I) (M := M) g r s Φ W)
            x v) d =
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
            (fun y : M =>
              (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) (Wd y)) x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v)) -
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x)
              (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
                (fun y : M => dSec y) x
                ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v))) := by
    have hval : (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from
            (operatorFieldApply (I := I) (M := M) g r s Φ W).toSection y) (dSec y)) =
        (fun y : M =>
          (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) (Wd y)) := by
      funext y
      rw [operatorFieldApplication_toSection (I := I) (M := M) g r s Φ W y]
      rfl
    rw [show d = dSec x from hdSec.symm,
      tensorCovDerivAt_def (I := I) (M := M) g 0 s (operatorFieldApply (I := I) (M := M) g r s Φ W)
        x v,
      tensorRSCovariantDerivative_apply (I := I) (M := M) 0 s (LeviCivita (I := I) g)
        (operatorFieldApply (I := I) (M := M) g r s Φ W).toSection dSec x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v), hval,
      operatorFieldApplication_toSection (I := I) (M := M) g r s Φ W x, ContinuousLinearMap.comp_apply]
  have hT1 :
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g r s Φ x v)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) d) =
        (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
            (fun y : M =>
              (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) (Wd y)) x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v)) -
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
            (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)
              (fun y : M => Wd y) x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v)) := by
    rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) d = Wd x
      from by
      rw [show d = dSec x from hdSec.symm]; rfl,
      tensorCovDerivAt_def (I := I) (M := M) g r s Φ x v,
      tensorRSCovariantDerivative_apply (I := I) (M := M) r s (LeviCivita (I := I) g)
        Φ.toSection Wd x ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v)]
  have hT2 :
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
          tensorCovDerivAt (I := I) (M := M) g 0 r W x v) d) =
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
          (Tensor0SNabla.tensor0SCovariantDerivative I M r (LeviCivita (I := I) g)
              (fun y : M => Wd y) x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v)) -
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x)
              (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
                (fun y : M => dSec y) x
                ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v))) := by
    rw [show d = dSec x from hdSec.symm,
      tensorCovDerivAt_def (I := I) (M := M) g 0 r W x v,
      tensorRSCovariantDerivative_apply (I := I) (M := M) 0 r (LeviCivita (I := I) g)
        W.toSection dSec x ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v)]
    rw [map_sub (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)]
    rfl
  rw [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    hLHS, hT1, hT2]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorCovDerivAt_operatorFieldApplication_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorCovDerivAt_operatorFieldApplication_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorCovDerivAt_operatorFieldApplication_eq ``Submission.DifferentialGeometry.Analysis.Spectral.tensorCovDerivAt_operatorFieldApplication_eq

omit [BoundarylessManifold I M] [CompleteSpace E] [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensor0S_curry_covGrad_operatorFieldApplication_eq (g : SmoothRiemannianMetric I M) (r : ℕ)
    (W : SmoothCcTensor g 0 r) (x : M) (d : Tensor0SSpace 0 I x) (v0 : E) :
    (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from
          (covGrad (I := I) (M := M) g 0 r W).toSection x) d)
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v0) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
        tensorCovDerivAt (I := I) (M := M) g 0 r W x v0) d := by
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [TensorMultilinear.tensor0S_curry_toModel_apply (I := I) (M := M)
    (T := (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from
      (covGrad (I := I) (M := M) g 0 r W).toSection x) d) (v0 := v0) (vs := m)]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g 0 r W x d (Fin.cons v0 m)]
  simp only [Fin.cons_zero, Matrix.vecTail]
  rw [show (Fin.cons v0 m ∘ Fin.succ) = m from funext (fun j => by simp [Fin.cons_succ])]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensor0S_curry_covGrad_operatorFieldApplication_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensor0S_curry_covGrad_operatorFieldApplication_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensor0S_curry_covGrad_operatorFieldApplication_eq ``Submission.DifferentialGeometry.Analysis.Spectral.tensor0S_curry_covGrad_operatorFieldApplication_eq

omit [CompleteSpace E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_operatorFieldApply_eq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    covGrad (I := I) (M := M) g 0 s (operatorFieldApply (I := I) (M := M) g r s Φ W) =
      operatorFieldApply (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) W +
        operatorFieldApply (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s Φ)
          (covGrad (I := I) (M := M) g 0 r W) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((operatorFieldApply (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) W
    +
        operatorFieldApply (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s Φ)
          (covGrad (I := I) (M := M) g 0 r W)).toSection x) =
      (operatorFieldApply (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ)
        W).toSection x +
        (operatorFieldApply (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s Φ)
          (covGrad (I := I) (M := M) g 0 r W)).toSection x from rfl]
  apply ContinuousLinearMap.ext
  intro d
  rw [add_apply]
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  beta_reduce
  rw [Tensor0SSpace.toModel_add, add_apply]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g 0 s
    (operatorFieldApply (I := I) (M := M) g r s Φ W) x d v]
  rw [operatorFieldApplication_toSection (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) W x,
    ContinuousLinearMap.comp_apply,
    covGrad_toSection_apply_eval (I := I) (M := M) g r s Φ x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) d) v]
  have hT2val : Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (operatorFieldApply (I := I) (M := M) g (r + 1) (s + 1)
            (slotExtend (I := I) (M := M) g r s Φ)
            (covGrad (I := I) (M := M) g 0 r W)).toSection x) d) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
            tensorCovDerivAt (I := I) (M := M) g 0 r W x (v 0)) d))
        (Matrix.vecTail v) := by
    rw [operatorFieldApplication_toSection (I := I) (M := M) g (r + 1) (s + 1) (slotExtend (I := I) (M := M) g r s Φ)
        (covGrad (I := I) (M := M) g 0 r W) x, ContinuousLinearMap.comp_apply,
      slotExtend_toSection (I := I) (M := M) g r s Φ x]
    rw [show v = Fin.cons (v 0) (Matrix.vecTail v) from (Fin.cons_self_tail v).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) r s x
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + 1) I x from
        (covGrad (I := I) (M := M) g 0 r W).toSection x) d) (v 0) (Matrix.vecTail v)]
    rw [tensor0S_curry_covGrad_operatorFieldApplication_eq (I := I) (M := M) g r W x d (v 0)]
    simp only [Fin.cons_zero, Matrix.vecTail]
    rw [show (Fin.cons (v 0) (v ∘ Fin.succ) ∘ Fin.succ) = v ∘ Fin.succ from
      funext (fun j => by simp [Fin.cons_succ])]
  rw [hT2val]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorCovDerivAt (I := I) (M := M) g 0 s (operatorFieldApply (I := I) (M := M) g r s Φ W) x
          (v 0)) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g r s Φ x (v 0)).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x) +
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
            tensorCovDerivAt (I := I) (M := M) g 0 r W x (v 0)) from
    tensorCovDerivAt_operatorFieldApplication_eq (I := I) (M := M) g r s Φ W x (v 0)]
  rw [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Tensor0SSpace.toModel_add, add_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.covGrad_operatorFieldApply_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.covGrad_operatorFieldApply_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.covGrad_operatorFieldApply_eq ``Submission.DifferentialGeometry.Analysis.Spectral.covGrad_operatorFieldApply_eq

end Spectral
end Analysis
end DifferentialGeometry

namespace DifferentialGeometry.Integral.Connection

open _root_.Submission.DifferentialGeometry.TensorMultilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

def slotExtendPointwise (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) :
    Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace (r + 1) I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s x).symm
          (A.comp ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x) D))
      map_add' := fun D₁ D₂ => by
        rw [map_add (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x),
          ContinuousLinearMap.comp_add, map_add
            (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s x).symm]
      map_smul' := fun c D => by
        rw [map_smul (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x),
          ContinuousLinearMap.comp_smul, map_smul
            (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s x).symm]
        rfl }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.slotExtendPointwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.slotExtendPointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.slotExtendPointwise ``Submission.DifferentialGeometry.Integral.Connection.slotExtendPointwise

abbrev slotExtendFib (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) :
    Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x :=
  slotExtendPointwise r s x A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.slotExtendFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.slotExtendFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.slotExtendFib ``Submission.DifferentialGeometry.Integral.Connection.slotExtendFib

@[simp] lemma slotExtendFib_apply (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x)
    (D : Tensor0SSpace (r + 1) I x) :
    slotExtendPointwise (I := I) (M := M) r s x A D =
      (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        (A.comp ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x) D)) := by
  rw [slotExtendPointwise, LinearMap.coe_toContinuousLinearMap']
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.slotExtendFib_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.slotExtendFib_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.slotExtendFib_apply ``Submission.DifferentialGeometry.Integral.Connection.slotExtendFib_apply

lemma slotExtendFib_apply_eval (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x)
    (D : Tensor0SSpace (r + 1) I x) (v0 : E) (vs : Fin s → E) :
    Tensor0SSpace.toModel
        (slotExtendPointwise (I := I) (M := M) r s x A D) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        (A ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x) D
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v0))) vs := by
  rw [← TensorMultilinear.tensor0S_curry_toModel_apply (I := I) (M := M) (n := s)
    (slotExtendPointwise (I := I) (M := M) r s x A D) v0 vs]
  have hcurry : tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s x
      (slotExtendPointwise (I := I) (M := M) r s x A D) =
      A.comp ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x) D) := by
    rw [slotExtendFib_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [hcurry]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.slotExtendFib_apply_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.slotExtendFib_apply_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.slotExtendFib_apply_eval ``Submission.DifferentialGeometry.Integral.Connection.slotExtendFib_apply_eval

alias covGrad_operatorFieldApplication_eq :=
  DifferentialGeometry.Analysis.Spectral.covGrad_operatorFieldApply_eq

end DifferentialGeometry.Integral.Connection

end
