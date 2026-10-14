import Submission.DifferentialGeometry.Geometry.Neck.NormalizedDatum
import Submission.DifferentialGeometry.Geometry.Metric.CylinderRotation
import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtype

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff

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

def openCylinder (L : ℝ) : _root_.TopologicalSpace.Opens (S2 × ℝ) :=
  ⟨{q | q.2 ∈ _root_.Set.Ioo (-L) L}, isOpen_Ioo.preimage continuous_snd⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.openCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.openCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.openCylinder ``Submission.DifferentialGeometry.Geometry.Neck.openCylinder

theorem roundCylinderImage_bufferedCylinder_le (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ)
    {d B L : ℝ} (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) :
    roundCylinderImage (n := 2) e z₀ (bufferedCylinder d) ≤ openCylinder L := by
  rintro q ⟨z, hz, rfl⟩
  rw [roundCylinderDiffeomorph_apply]
  change -L < z₀ + z.2 ∧ z₀ + z.2 < L
  change -d⁻¹ - 1 < z.2 ∧ z.2 < d⁻¹ + 1 at hz
  constructor <;> linarith [hz.1, hz.2, neg_abs_le z₀, le_abs_self z₀]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.roundCylinderImage_bufferedCylinder_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.roundCylinderImage_bufferedCylinder_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.roundCylinderImage_bufferedCylinder_le ``Submission.DifferentialGeometry.Geometry.Neck.roundCylinderImage_bufferedCylinder_le

def pointwiseCylinderMap (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B L : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) : bufferedCylinder d → openCylinder L :=
  Opens.inclusion (roundCylinderImage_bufferedCylinder_le e z₀ hfit hBL) ∘
    roundCylinderRestrict (n := 2) e z₀ (bufferedCylinder d)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.pointwiseCylinderMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.pointwiseCylinderMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.pointwiseCylinderMap ``Submission.DifferentialGeometry.Geometry.Neck.pointwiseCylinderMap

theorem pointwiseCylinderMap_val (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B L : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) (q : bufferedCylinder d) :
    (pointwiseCylinderMap e z₀ hfit hBL q : S2 × ℝ) =
      (sphereDiffeo (n := 2) e q.val.1, z₀ + q.val.2) :=
  roundCylinderRestrict_apply e z₀ (bufferedCylinder d) q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.pointwiseCylinderMap_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.pointwiseCylinderMap_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.pointwiseCylinderMap_val ``Submission.DifferentialGeometry.Geometry.Neck.pointwiseCylinderMap_val

theorem pointwiseCylinderMap_height_mem_Ioo (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ)
    {d B L : ℝ} (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L)
    (q : bufferedCylinder d) :
    (pointwiseCylinderMap e z₀ hfit hBL q).val.2 ∈ _root_.Set.Ioo (-B) B := by
  rw [pointwiseCylinderMap_val]
  have hq := q.property
  change -d⁻¹ - 1 < q.val.2 ∧ q.val.2 < d⁻¹ + 1 at hq
  change -B < z₀ + q.val.2 ∧ z₀ + q.val.2 < B
  constructor <;> linarith [hq.1, hq.2, neg_abs_le z₀, le_abs_self z₀]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.pointwiseCylinderMap_height_mem_Ioo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.pointwiseCylinderMap_height_mem_Ioo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.pointwiseCylinderMap_height_mem_Ioo ``Submission.DifferentialGeometry.Geometry.Neck.pointwiseCylinderMap_height_mem_Ioo

theorem contMDiff_pointwiseCylinderMap (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B L : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) :
    ContMDiff IC IC ∞ (pointwiseCylinderMap e z₀ hfit hBL) :=
  (contMDiff_inclusion (roundCylinderImage_bufferedCylinder_le e z₀ hfit hBL)).comp
    (roundCylinderRestrict (n := 2) e z₀ (bufferedCylinder d)).contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.contMDiff_pointwiseCylinderMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.contMDiff_pointwiseCylinderMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.contMDiff_pointwiseCylinderMap ``Submission.DifferentialGeometry.Geometry.Neck.contMDiff_pointwiseCylinderMap

theorem injective_pointwiseCylinderMap (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B L : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) :
    Injective (pointwiseCylinderMap e z₀ hfit hBL) := by
  intro x y hxy
  apply (roundCylinderRestrict (n := 2) e z₀ (bufferedCylinder d)).injective
  apply Subtype.ext
  exact congrArg (fun q : openCylinder L => q.val) hxy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.injective_pointwiseCylinderMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.injective_pointwiseCylinderMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.injective_pointwiseCylinderMap ``Submission.DifferentialGeometry.Geometry.Neck.injective_pointwiseCylinderMap

theorem range_pointwiseCylinderMap (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B L : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) :
    _root_.Set.range (pointwiseCylinderMap e z₀ hfit hBL) =
      {q : openCylinder L | q.val ∈ roundCylinderImage (n := 2) e z₀ (bufferedCylinder d)} := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact (roundCylinderRestrict (n := 2) e z₀ (bufferedCylinder d) x).property
  · intro hq
    let a := roundCylinderRestrict (n := 2) e z₀ (bufferedCylinder d)
    refine ⟨a.symm ⟨q.val, hq⟩, ?_⟩
    apply Subtype.ext
    change (a (a.symm ⟨q.val, hq⟩)).val = q.val
    rw [a.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.range_pointwiseCylinderMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.range_pointwiseCylinderMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.range_pointwiseCylinderMap ``Submission.DifferentialGeometry.Geometry.Neck.range_pointwiseCylinderMap

theorem pointwiseCylinderMap_mfderiv (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B L : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) (q : bufferedCylinder d)
    (v : TangentSpace IC q) :
    mfderiv IC IC (pointwiseCylinderMap e z₀ hfit hBL) q v =
      (mfderiv (𝓡 2) (𝓡 2) (sphereDiffeo (n := 2) e) q.val.1 v.1, v.2) := by
  have hinc := (contMDiff_inclusion (I := IC) (n := ∞)
    (roundCylinderImage_bufferedCylinder_le e z₀ hfit hBL)).mdifferentiable (by simp)
  have hax := (roundCylinderRestrict (n := 2) e z₀ (bufferedCylinder d)).contMDiff
    |>.mdifferentiable (by simp)
  rw [pointwiseCylinderMap, mfderiv_comp q (hinc _) (hax _), mfderiv_opens_incl]
  change mfderiv IC IC (roundCylinderRestrict (n := 2) e z₀ (bufferedCylinder d)) q v = _
  exact roundCylinderRestrict_mfderiv e z₀ (bufferedCylinder d) q v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.pointwiseCylinderMap_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.pointwiseCylinderMap_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.pointwiseCylinderMap_mfderiv ``Submission.DifferentialGeometry.Geometry.Neck.pointwiseCylinderMap_mfderiv

theorem image_pointwiseCylinderMap_controlledCylinder_subset (e : E3 ≃ₗᵢ[ℝ] E3)
    (z₀ : ℝ) {d B L : ℝ} (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) :
    pointwiseCylinderMap e z₀ hfit hBL '' controlledCylinder d ⊆
      {q : openCylinder L | q.val.2 ∈ _root_.Set.Icc (-B) B} := by
  rintro q ⟨z, hz, rfl⟩
  change -B ≤ (pointwiseCylinderMap e z₀ hfit hBL z).val.2 ∧
    (pointwiseCylinderMap e z₀ hfit hBL z).val.2 ≤ B
  rw [pointwiseCylinderMap_val]
  change -d⁻¹ ≤ z.val.2 ∧ z.val.2 ≤ d⁻¹ at hz
  constructor <;> linarith [hz.1, hz.2, neg_abs_le z₀, le_abs_self z₀]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.image_pointwiseCylinderMap_controlledCylinder_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.image_pointwiseCylinderMap_controlledCylinder_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.image_pointwiseCylinderMap_controlledCylinder_subset ``Submission.DifferentialGeometry.Geometry.Neck.image_pointwiseCylinderMap_controlledCylinder_subset

theorem point_mem_openCylinder_of_fit (y : S2) (z₀ : ℝ) {d B L : ℝ}
    (hd : 0 < d) (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) :
    (y, z₀) ∈ openCylinder L := by
  change -L < z₀ ∧ z₀ < L
  have hi := inv_pos.mpr hd
  constructor <;> linarith [neg_abs_le z₀, le_abs_self z₀]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.point_mem_openCylinder_of_fit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.point_mem_openCylinder_of_fit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.point_mem_openCylinder_of_fit ``Submission.DifferentialGeometry.Geometry.Neck.point_mem_openCylinder_of_fit

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

def pointwiseChart {L : ℝ} (Φ : openCylinder L → M) (e : E3 ≃ₗᵢ[ℝ] E3)
    (z₀ : ℝ) {d B : ℝ} (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) :
    bufferedCylinder d → M := Φ ∘ pointwiseCylinderMap e z₀ hfit hBL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.pointwiseChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.pointwiseChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.pointwiseChart ``Submission.DifferentialGeometry.Geometry.Neck.pointwiseChart

omit [TopologicalSpace M] in
theorem pointwiseChart_apply {L : ℝ} (Φ : openCylinder L → M) (e : E3 ≃ₗᵢ[ℝ] E3)
    (z₀ : ℝ) {d B : ℝ} (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L)
    (q : bufferedCylinder d) :
    pointwiseChart Φ e z₀ hfit hBL q = Φ
      ⟨(sphereDiffeo (n := 2) e q.val.1, z₀ + q.val.2), by
        rw [← pointwiseCylinderMap_val e z₀ hfit hBL q]
        exact (pointwiseCylinderMap e z₀ hfit hBL q).property⟩ := by
  apply congrArg Φ
  apply Subtype.ext
  exact pointwiseCylinderMap_val e z₀ hfit hBL q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.pointwiseChart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.pointwiseChart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.pointwiseChart_apply ``Submission.DifferentialGeometry.Geometry.Neck.pointwiseChart_apply

theorem contMDiff_pointwiseChart {L : ℝ} (Φ : openCylinder L → M)
    (hΦ : ContMDiff IC I ∞ Φ) (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) :
    ContMDiff IC I ∞ (pointwiseChart Φ e z₀ hfit hBL) :=
  hΦ.comp (contMDiff_pointwiseCylinderMap e z₀ hfit hBL)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.contMDiff_pointwiseChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.contMDiff_pointwiseChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.contMDiff_pointwiseChart ``Submission.DifferentialGeometry.Geometry.Neck.contMDiff_pointwiseChart

omit [TopologicalSpace M] in
theorem injective_pointwiseChart {L : ℝ} (Φ : openCylinder L → M)
    (hΦ : _root_.Function.Injective Φ) (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) :
    Injective (pointwiseChart Φ e z₀ hfit hBL) :=
  hΦ.comp (injective_pointwiseCylinderMap e z₀ hfit hBL)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.injective_pointwiseChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.injective_pointwiseChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.injective_pointwiseChart ``Submission.DifferentialGeometry.Geometry.Neck.injective_pointwiseChart

theorem immersion_pointwiseChart {L : ℝ} (Φ : openCylinder L → M)
    (hΦ : ContMDiff IC I ∞ Φ) (hm : ∀ q, _root_.Function.Injective (mfderiv IC I Φ q))
    (e : E3 ≃ₗᵢ[ℝ] E3) (z₀ : ℝ) {d B : ℝ}
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) (q : bufferedCylinder d) :
    Injective (mfderiv IC I (pointwiseChart Φ e z₀ hfit hBL) q) := by
  have hd := hΦ.mdifferentiable (by simp)
  have hc := (contMDiff_pointwiseCylinderMap e z₀ hfit hBL).mdifferentiable (by simp)
  rw [pointwiseChart, mfderiv_comp q (hd _) (hc _)]
  apply (hm _).comp
  intro v w hvw
  have hslots := (pointwiseCylinderMap_mfderiv e z₀ hfit hBL q v).symm.trans
    (hvw.trans (pointwiseCylinderMap_mfderiv e z₀ hfit hBL q w))
  have hfst := congrArg (fun u : EuclideanSpace ℝ (Fin 2) × ℝ => u.1) hslots
  have hsnd := congrArg (fun u : EuclideanSpace ℝ (Fin 2) × ℝ => u.2) hslots
  have hinj := ((sphereDiffeo (n := 2) e).toOpenPartialHomeomorph_mdifferentiable
    (by simp)).mfderiv_injective (x := q.val.1) (_root_.Set.mem_univ _)
  exact Prod.ext (hinj hfst) hsnd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.immersion_pointwiseChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.immersion_pointwiseChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.immersion_pointwiseChart ``Submission.DifferentialGeometry.Geometry.Neck.immersion_pointwiseChart

omit [TopologicalSpace M] in
theorem pointwiseChart_center {L : ℝ} (Φ : openCylinder L → M)
    (e : E3 ≃ₗᵢ[ℝ] E3) (yₚ : S2) (he : sphereDiffeo (n := 2) e spherePoint = yₚ)
    (z₀ : ℝ) {d B : ℝ} (hd : 0 < d)
    (hfit : |z₀| + d⁻¹ + 1 ≤ B) (hBL : B < L) :
    pointwiseChart Φ e z₀ hfit hBL (cylinderCenter d hd) =
      Φ ⟨(yₚ, z₀), point_mem_openCylinder_of_fit yₚ z₀ hd hfit hBL⟩ := by
  apply congrArg Φ
  apply Subtype.ext
  rw [pointwiseCylinderMap_val]
  simp only [cylinderCenter, he, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.pointwiseChart_center then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.pointwiseChart_center"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.pointwiseChart_center ``Submission.DifferentialGeometry.Geometry.Neck.pointwiseChart_center

end DifferentialGeometry.Geometry.Neck
