import Submission.DifferentialGeometry.Geometry.Neck.NormalizedDatum
import Submission.DifferentialGeometry.Geometry.Metric.CylinderAxial
import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtype
import Submission.DifferentialGeometry.Geometry.Metric.RoundCylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Topology.Manifold
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

private theorem orientation_image_le (δ σ : ℝ) (hσ : σ ^ 2 = 1) :
    cylinderAxialImage (I := 𝓡 2) 0 σ hσ (bufferedCylinder δ) ≤ bufferedCylinder δ := by
  rintro q ⟨p, hp, rfl⟩
  change -δ⁻¹ - 1 < 0 + σ * p.2 ∧ 0 + σ * p.2 < δ⁻¹ + 1
  change -δ⁻¹ - 1 < p.2 ∧ p.2 < δ⁻¹ + 1 at hp
  rcases sq_eq_one_iff.mp hσ with rfl | rfl
  · simpa using hp
  · constructor <;> linarith [hp.1, hp.2]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.orientation_image_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.orientation_image_le target :: scope.openDecls } }

private def orientationMap (δ σ : ℝ) (hσ : σ ^ 2 = 1) :
    bufferedCylinder δ → bufferedCylinder δ :=
  Opens.inclusion (orientation_image_le δ σ hσ) ∘
    cylinderAxialRestrict (I := 𝓡 2) 0 σ hσ (bufferedCylinder δ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.orientationMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.orientationMap target :: scope.openDecls } }

private theorem orientationMap_val (δ σ : ℝ) (hσ : σ ^ 2 = 1) (q : bufferedCylinder δ) :
    (orientationMap δ σ hσ q).val = (q.val.1, σ * q.val.2) := by
  change (q.val.1, 0 + σ * q.val.2) = _
  rw [zero_add]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.orientationMap_val
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.orientationMap_val target :: scope.openDecls } }

private theorem orientationMap_involutive (δ σ : ℝ) (hσ : σ ^ 2 = 1) :
    Involutive (orientationMap δ σ hσ) := by
  intro q
  apply Subtype.ext
  rw [orientationMap_val, orientationMap_val]
  refine Prod.ext (by rfl) ?_
  change σ * (σ * q.val.2) = q.val.2
  calc
    _ = σ ^ 2 * q.val.2 := by ring
    _ = q.val.2 := by rw [hσ, one_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.orientationMap_involutive
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.orientationMap_involutive target :: scope.openDecls } }

private theorem orientationMap_smooth (δ σ : ℝ) (hσ : σ ^ 2 = 1) :
    ContMDiff IC IC ∞ (orientationMap δ σ hσ) :=
  (contMDiff_inclusion (orientation_image_le δ σ hσ)).comp
    (cylinderAxialRestrict (I := 𝓡 2) 0 σ hσ (bufferedCylinder δ)).contMDiff

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.orientationMap_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.orientationMap_smooth target :: scope.openDecls } }

def bufferedCylinderOrientation (δ σ : ℝ) (hσ : σ ^ 2 = 1) :
    bufferedCylinder δ ≃ₘ⟮IC, IC⟯ bufferedCylinder δ where
  toFun := orientationMap δ σ hσ
  invFun := orientationMap δ σ hσ
  left_inv := orientationMap_involutive δ σ hσ
  right_inv := orientationMap_involutive δ σ hσ
  contMDiff_toFun := orientationMap_smooth δ σ hσ
  contMDiff_invFun := orientationMap_smooth δ σ hσ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.bufferedCylinderOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.bufferedCylinderOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.bufferedCylinderOrientation ``Submission.DifferentialGeometry.Geometry.Neck.bufferedCylinderOrientation

@[simp] theorem bufferedCylinderOrientation_apply (δ σ : ℝ) (hσ : σ ^ 2 = 1)
    (q : bufferedCylinder δ) :
    (bufferedCylinderOrientation δ σ hσ q).val = (q.val.1, σ * q.val.2) :=
  orientationMap_val δ σ hσ q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.bufferedCylinderOrientation_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.bufferedCylinderOrientation_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.bufferedCylinderOrientation_apply ``Submission.DifferentialGeometry.Geometry.Neck.bufferedCylinderOrientation_apply

theorem bufferedCylinderOrientation_mfderiv (δ σ : ℝ) (hσ : σ ^ 2 = 1)
    (q : bufferedCylinder δ) (v : TangentSpace IC q) :
    mfderiv IC IC (bufferedCylinderOrientation δ σ hσ) q v = (v.1, σ * v.2) := by
  have hinc := (contMDiff_inclusion (I := IC) (n := ∞)
    (orientation_image_le δ σ hσ)).mdifferentiable (by simp)
  have hax := (cylinderAxialRestrict (I := 𝓡 2) 0 σ hσ (bufferedCylinder δ)).contMDiff
    |>.mdifferentiable (by simp)
  change mfderiv IC IC (orientationMap δ σ hσ) q v = _
  rw [orientationMap, mfderiv_comp q (hinc _) (hax _), mfderiv_opens_incl]
  change mfderiv IC IC (cylinderAxialRestrict (I := 𝓡 2) 0 σ hσ (bufferedCylinder δ)) q v = _
  exact cylinderAxialRestrict_mfderiv 0 σ hσ (bufferedCylinder δ) q v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.bufferedCylinderOrientation_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.bufferedCylinderOrientation_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.bufferedCylinderOrientation_mfderiv ``Submission.DifferentialGeometry.Geometry.Neck.bufferedCylinderOrientation_mfderiv

@[simp] theorem bufferedCylinderOrientation_center (δ σ : ℝ) (hσ : σ ^ 2 = 1) (hδ : 0 < δ) :
    bufferedCylinderOrientation δ σ hσ (cylinderCenter δ hδ) = cylinderCenter δ hδ := by
  apply Subtype.ext
  rw [bufferedCylinderOrientation_apply]
  change (spherePoint, σ * 0) = (spherePoint, 0)
  rw [_root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.bufferedCylinderOrientation_center then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.bufferedCylinderOrientation_center"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.bufferedCylinderOrientation_center ``Submission.DifferentialGeometry.Geometry.Neck.bufferedCylinderOrientation_center

theorem image_bufferedCylinderOrientation_controlledCylinder (δ σ : ℝ) (hσ : σ ^ 2 = 1) :
    bufferedCylinderOrientation δ σ hσ '' controlledCylinder δ = controlledCylinder δ := by
  have hm : ∀ q ∈ controlledCylinder δ, bufferedCylinderOrientation δ σ hσ q ∈ controlledCylinder δ := by
    intro q hq
    change (bufferedCylinderOrientation δ σ hσ q).val.2 ∈ _root_.Set.Icc (-δ⁻¹) δ⁻¹
    rw [bufferedCylinderOrientation_apply]
    change -δ⁻¹ ≤ σ * q.val.2 ∧ σ * q.val.2 ≤ δ⁻¹
    change -δ⁻¹ ≤ q.val.2 ∧ q.val.2 ≤ δ⁻¹ at hq
    rcases sq_eq_one_iff.mp hσ with rfl | rfl
    · simpa using hq
    · constructor <;> linarith [hq.1, hq.2]
  apply Subset.antisymm
  · rintro q ⟨p, hp, rfl⟩
    exact hm p hp
  · intro q hq
    exact ⟨bufferedCylinderOrientation δ σ hσ q, hm q hq, orientationMap_involutive δ σ hσ q⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.image_bufferedCylinderOrientation_controlledCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.image_bufferedCylinderOrientation_controlledCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.image_bufferedCylinderOrientation_controlledCylinder ``Submission.DifferentialGeometry.Geometry.Neck.image_bufferedCylinderOrientation_controlledCylinder

theorem pullback_referenceMetric_bufferedCylinderOrientation (δ σ : ℝ) (hσ : σ ^ 2 = 1) :
    Diffeomorph.pullbackMetric (referenceMetric δ) (bufferedCylinderOrientation δ σ hσ) =
      referenceMetric δ := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetric_inner]
  change (roundCylinderMetric (E := E3) (n := 2)).inner
    (bufferedCylinderOrientation δ σ hσ x).val
    (mfderiv IC IC (bufferedCylinderOrientation δ σ hσ) x v)
    (mfderiv IC IC (bufferedCylinderOrientation δ σ hσ) x w) =
    (roundCylinderMetric (E := E3) (n := 2)).inner x.val v w
  rw [bufferedCylinderOrientation_mfderiv, bufferedCylinderOrientation_mfderiv]
  erw [roundCylinderMetric_inner, roundCylinderMetric_inner]
  rw [bufferedCylinderOrientation_apply]
  change 2 * _ + (σ * v.2) * (σ * w.2) = 2 * _ + v.2 * w.2
  congr 1
  calc
    _ = σ ^ 2 * (v.2 * w.2) := by ring
    _ = v.2 * w.2 := by rw [hσ, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.pullback_referenceMetric_bufferedCylinderOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.pullback_referenceMetric_bufferedCylinderOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.pullback_referenceMetric_bufferedCylinderOrientation ``Submission.DifferentialGeometry.Geometry.Neck.pullback_referenceMetric_bufferedCylinderOrientation

theorem metricDerivENormSupOn_bufferedCylinderOrientation (δ σ : ℝ) (hσ : σ ^ 2 = 1)
    (H HInf : SmoothRiemannianMetric IC (bufferedCylinder δ)) (p : ℕ) :
    metricDerivENormSupOn (controlledCylinder δ) p
      (Diffeomorph.pullbackMetric H (bufferedCylinderOrientation δ σ hσ))
      (Diffeomorph.pullbackMetric HInf (bufferedCylinderOrientation δ σ hσ)) (referenceMetric δ) =
    metricDerivENormSupOn (controlledCylinder δ) p H HInf (referenceMetric δ) := by
  have hn : ∀ j q, metricDerivNorm j
      (Diffeomorph.pullbackMetric H (bufferedCylinderOrientation δ σ hσ))
      (Diffeomorph.pullbackMetric HInf (bufferedCylinderOrientation δ σ hσ)) (referenceMetric δ) q =
      metricDerivNorm j H HInf (referenceMetric δ) (bufferedCylinderOrientation δ σ hσ q) := by
    intro j q
    simpa only [pullback_referenceMetric_bufferedCylinderOrientation] using
      metricDerivNorm_pullback H HInf (referenceMetric δ) (bufferedCylinderOrientation δ σ hσ) j q
  have he : metricDerivENormSupOn (controlledCylinder δ) p
      (Diffeomorph.pullbackMetric H (bufferedCylinderOrientation δ σ hσ))
      (Diffeomorph.pullbackMetric HInf (bufferedCylinderOrientation δ σ hσ)) (referenceMetric δ) =
    metricDerivENormSupOn (bufferedCylinderOrientation δ σ hσ '' controlledCylinder δ) p
      H HInf (referenceMetric δ) := by
    simp only [metricDerivENormSupOn, hn, iSup_image]
  rw [image_bufferedCylinderOrientation_controlledCylinder] at he
  exact he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.metricDerivENormSupOn_bufferedCylinderOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.metricDerivENormSupOn_bufferedCylinderOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.metricDerivENormSupOn_bufferedCylinderOrientation ``Submission.DifferentialGeometry.Geometry.Neck.metricDerivENormSupOn_bufferedCylinderOrientation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

namespace normalizedDatum

variable {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

def oriented (d : normalizedDatum g x₀ δ k) : normalizedDatum g x₀ δ k := by
  let f := bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq
  let φ := d.map ∘ f
  have hs : ContMDiff IC I ∞ φ := d.smooth.comp f.contMDiff
  have hi : _root_.Function.Injective φ := d.injective.comp f.injective
  have hm : ∀ x, _root_.Function.Injective (mfderiv IC I φ x) := by
    intro x
    rw [show φ = d.map ∘ f from rfl,
      mfderiv_comp x (d.smooth.mdifferentiable (by simp) _) (f.contMDiff.mdifferentiable (by simp) _)]
    apply (d.immersion _).comp
    intro v w hvw
    change mfderiv IC IC f x v = mfderiv IC IC f x w at hvw
    change mfderiv IC IC (bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq) x v =
      mfderiv IC IC (bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq) x w at hvw
    rw [bufferedCylinderOrientation_mfderiv, bufferedCylinderOrientation_mfderiv] at hvw
    have hσ : d.retainedSign ≠ 0 := by
      intro hz
      have h := d.retainedSign_sq
      rw [hz] at h
      norm_num at h
    have hh := congrArg (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => p.1) hvw
    have hz := congrArg (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => p.2) hvw
    exact Prod.ext hh (mul_left_cancel₀ hσ hz)
  have hloc := isLocalDiffeomorph_of_injective_mfderiv φ hs hm (by
    rw [show Module.finrank ℝ E = 3 from Fact.out]
    simp)
  have he : pullbackMetricOfInjectiveLocalDiffeomorph
      (scaleMetric (metricScalarAt g x₀) d.scalar_pos g) φ hloc hi =
      Diffeomorph.pullbackMetric d.normalizedMetric f := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner, scaleMetric_inner,
      Diffeomorph.pullbackMetric_inner, d.normalizedMetric_inner]
    rw [show φ = d.map ∘ f from rfl,
      mfderiv_comp x (d.smooth.mdifferentiable (by simp) _) (f.contMDiff.mdifferentiable (by simp) _)]
    rfl
  refine
    { precision_pos := d.precision_pos
      precision_lt_one := d.precision_lt_one
      map := φ
      smooth := hs
      injective := hi
      immersion := hm
      center_eq := ?_
      scalar_pos := d.scalar_pos
      retainedSide := _root_.Bool.true
      error_lt := ?_ }
  · change d.map (bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq
      (cylinderCenter δ d.precision_pos)) = x₀
    rw [bufferedCylinderOrientation_center]
    exact d.center_eq
  · change metricDerivENormSupOn (controlledCylinder δ) k
      (pullbackMetricOfInjectiveLocalDiffeomorph
        (scaleMetric (metricScalarAt g x₀) d.scalar_pos g) φ hloc hi)
      (referenceMetric δ) (referenceMetric δ) < ENNReal.ofReal δ
    rw [he]
    have hn := metricDerivENormSupOn_bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq
      d.normalizedMetric (referenceMetric δ) k
    rw [pullback_referenceMetric_bufferedCylinderOrientation] at hn
    exact hn.trans_lt d.normalizedMetric_error_lt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented

theorem oriented_map (d : normalizedDatum g x₀ δ k) (q : bufferedCylinder δ) :
    d.oriented.map q = d.map (bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq q) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_map ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_map

@[simp] theorem oriented_retainedSide (d : normalizedDatum g x₀ δ k) :
    d.oriented.retainedSide = true := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_retainedSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_retainedSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_retainedSide ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_retainedSide

theorem oriented_map_mfderiv (d : normalizedDatum g x₀ δ k) (q : bufferedCylinder δ)
    (v : TangentSpace IC q) :
    mfderiv IC I d.oriented.map q v =
      mfderiv IC I d.map (bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq q)
        (v.1, d.retainedSign * v.2) := by
  change mfderiv IC I
    (d.map ∘ bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq) q v = _
  rw [mfderiv_comp q (d.smooth.mdifferentiable (by simp) _)
    ((bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq).contMDiff.mdifferentiable (by simp) _)]
  change mfderiv IC I d.map _
    (mfderiv IC IC (bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq) q v) = _
  rw [bufferedCylinderOrientation_mfderiv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_map_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_map_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_map_mfderiv ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_map_mfderiv

theorem oriented_normalizedMetric (d : normalizedDatum g x₀ δ k) :
    d.oriented.normalizedMetric = Diffeomorph.pullbackMetric d.normalizedMetric
      (bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq) := by
  apply SmoothRiemannianMetric.ext_inner
  intro q v w
  rw [normalizedMetric_inner, Diffeomorph.pullbackMetric_inner, normalizedMetric_inner]
  change metricScalarAt g x₀ *
    g.inner (d.map (bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq q))
      (mfderiv IC I (d.map ∘ bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq) q v)
      (mfderiv IC I (d.map ∘ bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq) q w) = _
  rw [mfderiv_comp q (d.smooth.mdifferentiable (by simp) _)
    ((bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq).contMDiff.mdifferentiable (by simp) _)]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_normalizedMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_normalizedMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_normalizedMetric ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_normalizedMetric

theorem oriented_normalizedMetric_error_eq (d : normalizedDatum g x₀ δ k) (p : ℕ) :
    metricDerivENormSupOn (controlledCylinder δ) p d.oriented.normalizedMetric
      (referenceMetric δ) (referenceMetric δ) =
    metricDerivENormSupOn (controlledCylinder δ) p d.normalizedMetric
      (referenceMetric δ) (referenceMetric δ) := by
  rw [oriented_normalizedMetric]
  have h := metricDerivENormSupOn_bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq
    d.normalizedMetric (referenceMetric δ) p
  rwa [pullback_referenceMetric_bufferedCylinderOrientation] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_normalizedMetric_error_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_normalizedMetric_error_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_normalizedMetric_error_eq ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_normalizedMetric_error_eq

theorem range_oriented_map (d : normalizedDatum g x₀ δ k) : _root_.Set.range d.oriented.map = _root_.Set.range d.map := by
  change _root_.Set.range (d.map ∘ bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq) = _
  exact (bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq).surjective.range_comp d.map

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.range_oriented_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.range_oriented_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.range_oriented_map ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.range_oriented_map

theorem image_oriented_map_controlledCylinder (d : normalizedDatum g x₀ δ k) :
    d.oriented.map '' controlledCylinder δ = d.map '' controlledCylinder δ := by
  change (d.map ∘ bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq) '' controlledCylinder δ = _
  rw [_root_.Set.image_comp, image_bufferedCylinderOrientation_controlledCylinder]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.image_oriented_map_controlledCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.image_oriented_map_controlledCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.image_oriented_map_controlledCylinder ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.image_oriented_map_controlledCylinder

theorem oriented_old_retained_height (d : normalizedDatum g x₀ δ k) (q : bufferedCylinder δ) :
    d.retainedSign * (bufferedCylinderOrientation δ d.retainedSign d.retainedSign_sq q).val.2 = q.val.2 := by
  rw [bufferedCylinderOrientation_apply]
  change d.retainedSign * (d.retainedSign * q.val.2) = q.val.2
  calc
    _ = d.retainedSign ^ 2 * q.val.2 := by ring
    _ = q.val.2 := by rw [d.retainedSign_sq, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_old_retained_height then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_old_retained_height"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_old_retained_height ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_old_retained_height

theorem oriented_map_of_retainedSide_true (d : normalizedDatum g x₀ δ k)
    (hside : d.retainedSide = _root_.Bool.true) : d.oriented.map = d.map := by
  funext q
  rw [oriented_map]
  congr 1
  apply Subtype.ext
  rw [bufferedCylinderOrientation_apply]
  simp [retainedSign, hside]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_map_of_retainedSide_true then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_map_of_retainedSide_true"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_map_of_retainedSide_true ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_map_of_retainedSide_true

theorem oriented_map_of_retainedSide_false (d : normalizedDatum g x₀ δ k)
    (hside : d.retainedSide = _root_.Bool.false) (q : bufferedCylinder δ) :
    d.oriented.map q = d.map (bufferedCylinderOrientation δ (-1) (by norm_num) q) := by
  rw [oriented_map]
  congr 1
  apply Subtype.ext
  simp only [bufferedCylinderOrientation_apply, retainedSign, hside, Bool.false_eq_true, ↓reduceIte]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_map_of_retainedSide_false then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_map_of_retainedSide_false"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_map_of_retainedSide_false ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.oriented_map_of_retainedSide_false

end normalizedDatum
end DifferentialGeometry.Geometry.Neck
