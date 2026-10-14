import Submission.DifferentialGeometry.Topology.Homeomorph.NormShift
import Submission.DifferentialGeometry.Topology.Manifold.SectorRounding
import Mathlib.Analysis.InnerProductSpace.PiL2

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace Homeomorph
open _root_.Homeomorph

open _root_.Homeomorph in
private noncomputable def planeCoordinates : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

run_cmd do
  let target := ``Submission.Homeomorph.planeCoordinates
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Homeomorph.planeCoordinates target :: scope.openDecls } }

open _root_.Homeomorph in
private noncomputable def diagonal : EuclideanSpace ℝ (Fin 2) :=
  planeCoordinates.symm ((1 : ℝ) / 2, (1 : ℝ) / 2)

run_cmd do
  let target := ``Submission.Homeomorph.diagonal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Homeomorph.diagonal target :: scope.openDecls } }

open _root_.Homeomorph in
private theorem norm_diagonal_lt : ‖diagonal‖ < 1 := by
  have h : ‖diagonal‖ ^ 2 = (1 : ℝ) / 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [Fin.sum_univ_two, diagonal, planeCoordinates]
  nlinarith [norm_nonneg diagonal]

run_cmd do
  let target := ``Submission.Homeomorph.norm_diagonal_lt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Homeomorph.norm_diagonal_lt target :: scope.openDecls } }

open _root_.Homeomorph in
private theorem norm_planeCoordinates_symm_sq (p : ℝ × ℝ) :
    ‖planeCoordinates.symm p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two]
  rfl

run_cmd do
  let target := ``Submission.Homeomorph.norm_planeCoordinates_symm_sq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Homeomorph.norm_planeCoordinates_symm_sq target :: scope.openDecls } }

open _root_.Homeomorph in
noncomputable def smoothAbsCorner {ε : ℝ} (hε : 0 < ε) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  planeCoordinates.symm.toHomeomorph.trans
    ((smoothAbsNormShift hε diagonal norm_diagonal_lt).trans planeCoordinates.toHomeomorph)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.smoothAbsCorner then
    throwError "Refusing to shadow existing declaration Homeomorph.smoothAbsCorner"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.smoothAbsCorner ``Submission.Homeomorph.smoothAbsCorner

open _root_.Homeomorph in
private theorem smoothAbsCorner_apply_norm {ε : ℝ} (hε : 0 < ε) (p : ℝ × ℝ) :
    smoothAbsCorner hε p =
      (p.1 + (Real.smoothAbs ε ‖planeCoordinates.symm p‖ - ‖planeCoordinates.symm p‖) / 2,
       p.2 + (Real.smoothAbs ε ‖planeCoordinates.symm p‖ - ‖planeCoordinates.symm p‖) / 2) := by
  change planeCoordinates (planeCoordinates.symm p +
    (Real.smoothAbs ε ‖planeCoordinates.symm p‖ - ‖planeCoordinates.symm p‖) • diagonal) = _
  rw [map_add, map_smul, planeCoordinates.apply_symm_apply]
  change (p.1 + _ * (1 / 2), p.2 + _ * (1 / 2)) = _
  simp only [div_eq_mul_inv, one_mul]

run_cmd do
  let target := ``Submission.Homeomorph.smoothAbsCorner_apply_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Homeomorph.smoothAbsCorner_apply_norm target :: scope.openDecls } }

open _root_.Homeomorph in
@[simp] theorem smoothAbsCorner_apply {ε : ℝ} (hε : 0 < ε) (p : ℝ × ℝ) :
    smoothAbsCorner hε p =
      (p.1 + (Real.smoothAbs ε (Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) -
        Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) / 2,
       p.2 + (Real.smoothAbs ε (Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) -
        Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) / 2) := by
  rw [smoothAbsCorner_apply_norm, ← norm_planeCoordinates_symm_sq,
    Real.sqrt_sq (norm_nonneg _)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.smoothAbsCorner_apply then
    throwError "Refusing to shadow existing declaration Homeomorph.smoothAbsCorner_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.smoothAbsCorner_apply ``Submission.Homeomorph.smoothAbsCorner_apply

open _root_.Homeomorph in
theorem smoothAbsCorner_sub {ε : ℝ} (hε : 0 < ε) (p : ℝ × ℝ) :
    (smoothAbsCorner hε p).1 - (smoothAbsCorner hε p).2 = p.1 - p.2 := by
  rw [smoothAbsCorner_apply_norm]
  dsimp
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.smoothAbsCorner_sub then
    throwError "Refusing to shadow existing declaration Homeomorph.smoothAbsCorner_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.smoothAbsCorner_sub ``Submission.Homeomorph.smoothAbsCorner_sub

open _root_.Homeomorph in
private theorem smoothAbsCorner_sum_mem {ε : ℝ} (hε : 0 < ε) (p : ℝ × ℝ) :
    (smoothAbsCorner hε p).1 + (smoothAbsCorner hε p).2 ∈ _root_.Set.Icc (p.1 + p.2) (p.1 + p.2 + 2 * ε) := by
  have h := Real.smoothAbs.sub_abs_mem_Icc hε ‖planeCoordinates.symm p‖
  rw [abs_of_nonneg (norm_nonneg _)] at h
  rw [smoothAbsCorner_apply_norm]
  constructor <;> dsimp <;> linarith [h.1, h.2]

run_cmd do
  let target := ``Submission.Homeomorph.smoothAbsCorner_sum_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Homeomorph.smoothAbsCorner_sum_mem target :: scope.openDecls } }

open _root_.Homeomorph in
private theorem strictMono_smoothAbsCorner_sum {ε : ℝ} (hε : 0 < ε) (d : ℝ) :
    StrictMono (fun s : ℝ =>
      (smoothAbsCorner hε ((d + s) / 2, (s - d) / 2)).1 +
      (smoothAbsCorner hε ((d + s) / 2, (s - d) / 2)).2) := by
  let q : ℝ → ℝ × ℝ := fun s => ((d + s) / 2, (s - d) / 2)
  let F := fun s : ℝ => (smoothAbsCorner hε (q s)).1 + (smoothAbsCorner hε (q s)).2
  have hq : Continuous q := by dsimp [q]; fun_prop
  have hF : Continuous F := ((smoothAbsCorner hε).continuous.comp hq).fst.add
    ((smoothAbsCorner hε).continuous.comp hq).snd
  have hFi : Function.Injective F := by
    intro s t heq
    have hsub : (smoothAbsCorner hε (q s)).1 - (smoothAbsCorner hε (q s)).2 =
        (smoothAbsCorner hε (q t)).1 - (smoothAbsCorner hε (q t)).2 := by
      rw [smoothAbsCorner_sub, smoothAbsCorner_sub]
      dsimp [q]
      ring
    have heq' : smoothAbsCorner hε (q s) = smoothAbsCorner hε (q t) := by
      apply Prod.ext <;> dsimp [F] at heq <;> linarith
    have he := congrArg Prod.fst ((smoothAbsCorner hε).injective heq')
    dsimp [q] at he
    linarith
  rcases hF.strictMono_of_inj hFi with hm | hm
  · exact hm
  · have hh := hm (show (0 : ℝ) < 2 * ε + 1 by linarith)
    have hzero := (smoothAbsCorner_sum_mem hε (q 0)).2
    have hbig := (smoothAbsCorner_sum_mem hε (q (2 * ε + 1))).1
    dsimp [F, q] at hh hzero hbig
    linarith

run_cmd do
  let target := ``Submission.Homeomorph.strictMono_smoothAbsCorner_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Homeomorph.strictMono_smoothAbsCorner_sum target :: scope.openDecls } }

open _root_.Homeomorph in
theorem smoothAbsCorner_eq_smoothAbsQuadrant {ε : ℝ} (hε : 0 < ε)
    (p : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}) (hp : p.val.1 = 0 ∨ p.val.2 = 0) :
    smoothAbsCorner hε p.val = (smoothAbsQuadrant hε p).val := by
  have hn : ‖planeCoordinates.symm p.val‖ = p.val.1 + p.val.2 := by
    have hs := norm_planeCoordinates_symm_sq p.val
    rcases hp with hp | hp <;> rw [hp] at hs ⊢ <;>
      nlinarith [norm_nonneg (planeCoordinates.symm p.val), p.property.1, p.property.2]
  rw [smoothAbsCorner_apply_norm, hn, smoothAbsQuadrant_apply]
  ext <;> dsimp <;> ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.smoothAbsCorner_eq_smoothAbsQuadrant then
    throwError "Refusing to shadow existing declaration Homeomorph.smoothAbsCorner_eq_smoothAbsQuadrant"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.smoothAbsCorner_eq_smoothAbsQuadrant ``Submission.Homeomorph.smoothAbsCorner_eq_smoothAbsQuadrant

open _root_.Homeomorph in
private theorem smoothAbsCorner_boundary_sum {ε : ℝ} (hε : 0 < ε) (d : ℝ) :
    (smoothAbsCorner hε ((d + |d|) / 2, (|d| - d) / 2)).1 +
    (smoothAbsCorner hε ((d + |d|) / 2, (|d| - d) / 2)).2 = Real.smoothAbs ε d := by
  have hq : 0 ≤ (d + |d|) / 2 ∧ 0 ≤ (|d| - d) / 2 := by
    constructor <;> linarith [neg_abs_le d, le_abs_self d]
  let p : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} := ⟨((d + |d|) / 2, (|d| - d) / 2), hq⟩
  have hp : p.val.1 = 0 ∨ p.val.2 = 0 := by
    rcases le_total 0 d with hd | hd
    · right; simp [p, abs_of_nonneg hd]
    · left; simp [p, abs_of_nonpos hd]
  change (smoothAbsCorner hε p.val).1 + (smoothAbsCorner hε p.val).2 = _
  rw [smoothAbsCorner_eq_smoothAbsQuadrant hε p hp, smoothAbsQuadrant_sum]
  have hs : p.val.1 + p.val.2 = |d| := by dsimp [p]; ring
  rw [hs, Real.smoothAbs.abs hε.ne']

run_cmd do
  let target := ``Submission.Homeomorph.smoothAbsCorner_boundary_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Homeomorph.smoothAbsCorner_boundary_sum target :: scope.openDecls } }

open _root_.Homeomorph in
theorem smoothAbsCorner_mem_quadrant_iff {ε : ℝ} (hε : 0 < ε) (p : ℝ × ℝ) :
    Real.smoothAbs ε ((smoothAbsCorner hε p).1 - (smoothAbsCorner hε p).2) ≤
      (smoothAbsCorner hε p).1 + (smoothAbsCorner hε p).2 ↔ 0 ≤ p.1 ∧ 0 ≤ p.2 := by
  have hm := (strictMono_smoothAbsCorner_sum hε (p.1 - p.2)).le_iff_le
    (a := |p.1 - p.2|) (b := p.1 + p.2)
  rw [smoothAbsCorner_boundary_sum] at hm
  have hp : ((p.1 - p.2 + (p.1 + p.2)) / 2, (p.1 + p.2 - (p.1 - p.2)) / 2) = p := by
    ext <;> dsimp <;> ring
  rw [hp] at hm
  rw [smoothAbsCorner_sub, hm, abs_le]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.smoothAbsCorner_mem_quadrant_iff then
    throwError "Refusing to shadow existing declaration Homeomorph.smoothAbsCorner_mem_quadrant_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.smoothAbsCorner_mem_quadrant_iff ``Submission.Homeomorph.smoothAbsCorner_mem_quadrant_iff

open _root_.Homeomorph in
theorem smoothAbsCorner_mem_complementary_quadrant_iff {ε : ℝ} (hε : 0 < ε) (p : ℝ × ℝ) :
    (smoothAbsCorner hε p).1 + (smoothAbsCorner hε p).2 ≤
      Real.smoothAbs ε ((smoothAbsCorner hε p).1 - (smoothAbsCorner hε p).2) ↔ p.1 ≤ 0 ∨ p.2 ≤ 0 := by
  have hm := (strictMono_smoothAbsCorner_sum hε (p.1 - p.2)).le_iff_le
    (a := p.1 + p.2) (b := |p.1 - p.2|)
  rw [smoothAbsCorner_boundary_sum] at hm
  have hp : ((p.1 - p.2 + (p.1 + p.2)) / 2, (p.1 + p.2 - (p.1 - p.2)) / 2) = p := by
    ext <;> dsimp <;> ring
  rw [hp] at hm
  rw [smoothAbsCorner_sub, hm, le_abs]
  constructor
  · rintro (h | h)
    · right; linarith
    · left; linarith
  · rintro (h | h)
    · right; linarith
    · left; linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.smoothAbsCorner_mem_complementary_quadrant_iff then
    throwError "Refusing to shadow existing declaration Homeomorph.smoothAbsCorner_mem_complementary_quadrant_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.smoothAbsCorner_mem_complementary_quadrant_iff ``Submission.Homeomorph.smoothAbsCorner_mem_complementary_quadrant_iff


open _root_.Homeomorph in
theorem smoothAbsCorner_apply_eq_self {ε : ℝ} (hε : 0 < ε) {p : ℝ × ℝ}
    (hp : ε ^ 2 ≤ p.1 ^ 2 + p.2 ^ 2) : smoothAbsCorner hε p = p := by
  have hn : ε ≤ ‖planeCoordinates.symm p‖ := by
    have hs := norm_planeCoordinates_symm_sq p
    nlinarith [norm_nonneg (planeCoordinates.symm p)]
  change planeCoordinates (smoothAbsNormShift hε diagonal norm_diagonal_lt
    (planeCoordinates.symm p)) = p
  rw [smoothAbsNormShift_apply_eq_self hε diagonal norm_diagonal_lt hn,
    planeCoordinates.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.smoothAbsCorner_apply_eq_self then
    throwError "Refusing to shadow existing declaration Homeomorph.smoothAbsCorner_apply_eq_self"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.smoothAbsCorner_apply_eq_self ``Submission.Homeomorph.smoothAbsCorner_apply_eq_self

open _root_.Homeomorph in
theorem smoothAbsCorner_eqOn_compl {ε : ℝ} (hε : 0 < ε) :
    _root_.Set.EqOn (smoothAbsCorner hε) id (Metric.closedBall (0 : ℝ × ℝ) ε)ᶜ ∧
      EqOn (smoothAbsCorner hε).symm id (Metric.closedBall (0 : ℝ × ℝ) ε)ᶜ := by
  have hfix : _root_.Set.EqOn (smoothAbsCorner hε) id (Metric.closedBall (0 : ℝ × ℝ) ε)ᶜ := by
    intro p hp
    apply smoothAbsCorner_apply_eq_self hε
    by_contra hn
    apply hp
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
    have hs : p.1 ^ 2 + p.2 ^ 2 < ε ^ 2 := lt_of_not_ge hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_le, abs_le]
    constructor <;> constructor <;> nlinarith [sq_nonneg p.1, sq_nonneg p.2]
  refine ⟨hfix, ?_⟩
  intro p hp
  exact (congrArg (smoothAbsCorner hε).symm (hfix hp)).symm.trans
    ((smoothAbsCorner hε).symm_apply_apply p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.smoothAbsCorner_eqOn_compl then
    throwError "Refusing to shadow existing declaration Homeomorph.smoothAbsCorner_eqOn_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.smoothAbsCorner_eqOn_compl ``Submission.Homeomorph.smoothAbsCorner_eqOn_compl

open _root_.Homeomorph in
theorem smoothAbsCorner_image_quadrant {ε : ℝ} (hε : 0 < ε) :
    smoothAbsCorner hε '' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} =
      {p | Real.smoothAbs ε (p.1 - p.2) ≤ p.1 + p.2} := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (smoothAbsCorner_mem_quadrant_iff hε q).mpr hq
  · intro hp
    refine ⟨(smoothAbsCorner hε).symm p, ?_, (smoothAbsCorner hε).apply_symm_apply p⟩
    apply (smoothAbsCorner_mem_quadrant_iff hε _).mp
    simpa only [(smoothAbsCorner hε).apply_symm_apply, _root_.Set.mem_ofPred_eq] using hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.smoothAbsCorner_image_quadrant then
    throwError "Refusing to shadow existing declaration Homeomorph.smoothAbsCorner_image_quadrant"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.smoothAbsCorner_image_quadrant ``Submission.Homeomorph.smoothAbsCorner_image_quadrant

open _root_.Homeomorph in
theorem smoothAbsCorner_image_complementary_quadrant {ε : ℝ} (hε : 0 < ε) :
    smoothAbsCorner hε '' {p : ℝ × ℝ | p.1 ≤ 0 ∨ p.2 ≤ 0} =
      {p | p.1 + p.2 ≤ Real.smoothAbs ε (p.1 - p.2)} := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (smoothAbsCorner_mem_complementary_quadrant_iff hε q).mpr hq
  · intro hp
    refine ⟨(smoothAbsCorner hε).symm p, ?_, (smoothAbsCorner hε).apply_symm_apply p⟩
    apply (smoothAbsCorner_mem_complementary_quadrant_iff hε _).mp
    simpa only [(smoothAbsCorner hε).apply_symm_apply, _root_.Set.mem_ofPred_eq] using hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.smoothAbsCorner_image_complementary_quadrant then
    throwError "Refusing to shadow existing declaration Homeomorph.smoothAbsCorner_image_complementary_quadrant"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.smoothAbsCorner_image_complementary_quadrant ``Submission.Homeomorph.smoothAbsCorner_image_complementary_quadrant

open _root_.Homeomorph in
theorem smoothAbsCorner_image_boundary {ε : ℝ} (hε : 0 < ε) :
    smoothAbsCorner hε '' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ (p.1 = 0 ∨ p.2 = 0)} =
      {p | Real.smoothAbs ε (p.1 - p.2) = p.1 + p.2} := by
  have hraw : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ (p.1 = 0 ∨ p.2 = 0)} =
      {p | 0 ≤ p.1 ∧ 0 ≤ p.2} ∩ {p | p.1 ≤ 0 ∨ p.2 ≤ 0} := by
    ext p
    constructor
    · rintro ⟨hu, hv, hp | hp⟩
      · exact ⟨⟨hu, hv⟩, Or.inl hp.le⟩
      · exact ⟨⟨hu, hv⟩, Or.inr hp.le⟩
    · rintro ⟨⟨hu, hv⟩, hp | hp⟩
      · exact ⟨hu, hv, Or.inl (le_antisymm hp hu)⟩
      · exact ⟨hu, hv, Or.inr (le_antisymm hp hv)⟩
  rw [hraw, Set.image_inter (smoothAbsCorner hε).injective,
    smoothAbsCorner_image_quadrant, smoothAbsCorner_image_complementary_quadrant]
  ext p
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.smoothAbsCorner_image_boundary then
    throwError "Refusing to shadow existing declaration Homeomorph.smoothAbsCorner_image_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.smoothAbsCorner_image_boundary ``Submission.Homeomorph.smoothAbsCorner_image_boundary

open _root_.Homeomorph in
theorem isLocalDiffeomorphAt_smoothAbsCorner {ε : ℝ} (hε : 0 < ε)
    {p : ℝ × ℝ} (hp : p ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (smoothAbsCorner hε) p := by
  have hp' : planeCoordinates.symm p ≠ 0 := by
    intro h
    apply hp
    simpa only [map_zero, planeCoordinates.apply_symm_apply] using congrArg planeCoordinates h
  exact ((planeCoordinates.symm.toDiffeomorph.isLocalDiffeomorph p).comp _ _
    (isLocalDiffeomorphAt_smoothAbsNormShift hε diagonal norm_diagonal_lt hp')).comp _ _
    (planeCoordinates.toDiffeomorph.isLocalDiffeomorph _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.isLocalDiffeomorphAt_smoothAbsCorner then
    throwError "Refusing to shadow existing declaration Homeomorph.isLocalDiffeomorphAt_smoothAbsCorner"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.isLocalDiffeomorphAt_smoothAbsCorner ``Submission.Homeomorph.isLocalDiffeomorphAt_smoothAbsCorner

end Homeomorph
