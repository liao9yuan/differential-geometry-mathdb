import Submission.DifferentialGeometry.Topology.Attachment.Union
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.Manifold.Attachment

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.S2 target :: scope.openDecls } }
private abbrev Cap (L : ℝ) := {x : E3 // ‖x‖ ≤ L}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.Cap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.Cap target :: scope.openDecls } }
private abbrev Retained (B : ℝ) := S2 × _root_.Set.Ico (0 : ℝ) B

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.Retained
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.Retained target :: scope.openDecls } }
private abbrev Ball (L B : ℝ) := {x : E3 // ‖x‖ < L + B}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.Ball
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.Ball target :: scope.openDecls } }
private abbrev Shell (L B : ℝ) := {x : Ball L B // L ≤ ‖x.val‖}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.Shell
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.Shell target :: scope.openDecls } }

def radialCapBoundary {L : ℝ} (hL : 0 < L) : S2 → Cap L :=
  fun y => ⟨L • (y : E3), by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL,
      mem_sphere_zero_iff_norm.mp y.property, mul_one]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCapBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCapBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCapBoundary ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCapBoundary

def retainedBoundary {B : ℝ} (hB : 0 < B) : S2 → Retained B :=
  fun y => (y, ⟨0, ⟨le_rfl, hB⟩⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.retainedBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.retainedBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.retainedBoundary ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.retainedBoundary

private def retainedRadial {L B : ℝ} (q : Retained B) : E3 :=
  (L + q.2.val) • (q.1 : E3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.retainedRadial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.retainedRadial target :: scope.openDecls } }

private theorem retainedRadial_norm {L B : ℝ} (hL : 0 < L) (q : Retained B) :
    ‖retainedRadial (L := L) q‖ = L + q.2.val := by
  change ‖(L + q.2.val) • (q.1 : E3)‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (add_pos_of_pos_of_nonneg hL q.2.property.1),
    mem_sphere_zero_iff_norm.mp q.1.property, mul_one]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.retainedRadial_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.retainedRadial_norm target :: scope.openDecls } }

private def retainedToShell {L B : ℝ} (hL : 0 < L) (q : Retained B) : Shell L B :=
  ⟨⟨retainedRadial (L := L) q, by
    rw [retainedRadial_norm hL]
    linarith [q.2.property.2]⟩, by
    rw [retainedRadial_norm hL]
    exact le_add_of_nonneg_right q.2.property.1⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.retainedToShell
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.retainedToShell target :: scope.openDecls } }

private def shellPunctured {L B : ℝ} (hL : 0 < L) (x : Shell L B) : ({0}ᶜ : Set E3) :=
  ⟨x.val.val, by
    simpa only [_root_.Set.mem_compl_iff, _root_.Set.mem_singleton_iff] using
      norm_pos_iff.mp (hL.trans_le x.property)⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.shellPunctured
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.shellPunctured target :: scope.openDecls } }

private def shellToRetained {L B : ℝ} (hL : 0 < L) (x : Shell L B) : Retained B :=
  ((homeomorphUnitSphereProd E3 (shellPunctured hL x)).1,
    ⟨‖x.val.val‖ - L, ⟨sub_nonneg.mpr x.property, by linarith [x.val.property]⟩⟩)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.shellToRetained
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.shellToRetained target :: scope.openDecls } }

def retainedCylinderHomeomorphShell {L B : ℝ} (hL : 0 < L) :
    Retained B ≃ₜ Shell L B where
  toFun := retainedToShell hL
  invFun := shellToRetained hL
  left_inv q := by
    apply Prod.ext
    · change (homeomorphUnitSphereProd E3
        ((homeomorphUnitSphereProd E3).symm
          (q.1, ⟨L + q.2.val, add_pos_of_pos_of_nonneg hL q.2.property.1⟩))).1 = q.1
      rw [Homeomorph.apply_symm_apply]
    · apply Subtype.ext
      change ‖retainedRadial (L := L) q‖ - L = q.2.val
      rw [retainedRadial_norm hL]
      ring
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change (L + (‖x.val.val‖ - L)) •
      ((homeomorphUnitSphereProd E3 (shellPunctured hL x)).1 : E3) = x.val.val
    rw [show L + (‖x.val.val‖ - L) = ‖x.val.val‖ by ring]
    have h := congrArg (fun y : ({0}ᶜ : Set E3) => y.val)
      ((homeomorphUnitSphereProd E3).symm_apply_apply
        (shellPunctured hL x))
    simpa only [homeomorphUnitSphereProd_symm_apply_coe,
      homeomorphUnitSphereProd_apply_snd_coe, shellPunctured] using h
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (continuous_const.add (continuous_subtype_val.comp continuous_snd)).smul
      (continuous_subtype_val.comp continuous_fst)
  continuous_invFun := by
    apply Continuous.prodMk
    · exact continuous_fst.comp ((homeomorphUnitSphereProd E3).continuous.comp
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _))
    · exact ((continuous_norm.comp
        (continuous_subtype_val.comp continuous_subtype_val)).sub continuous_const).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.retainedCylinderHomeomorphShell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.retainedCylinderHomeomorphShell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.retainedCylinderHomeomorphShell ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.retainedCylinderHomeomorphShell

theorem retainedCylinderHomeomorphShell_apply {L B : ℝ} (hL : 0 < L)
    (q : Retained B) :
    ((retainedCylinderHomeomorphShell hL q).val : E3) =
      (L + q.2.val) • (q.1 : E3) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.retainedCylinderHomeomorphShell_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.retainedCylinderHomeomorphShell_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.retainedCylinderHomeomorphShell_apply ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.retainedCylinderHomeomorphShell_apply

theorem retainedCylinderHomeomorphShell_symm_snd {L B : ℝ} (hL : 0 < L)
    (x : Shell L B) :
    ((retainedCylinderHomeomorphShell hL).symm x).2.val = ‖x.val.val‖ - L := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.retainedCylinderHomeomorphShell_symm_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.retainedCylinderHomeomorphShell_symm_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.retainedCylinderHomeomorphShell_symm_snd ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.retainedCylinderHomeomorphShell_symm_snd

private def capInclusion {L B : ℝ} (hB : 0 < B) : Cap L → Ball L B :=
  fun x => ⟨x.val, by linarith [x.property]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.capInclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.capInclusion target :: scope.openDecls } }

private theorem capInclusion_injective {L B : ℝ} (hB : 0 < B) :
    Injective (capInclusion (L := L) hB) := by
  intro x y h
  exact Subtype.ext (congrArg (fun z : Ball L B => z.val) h)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.capInclusion_injective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.capInclusion_injective target :: scope.openDecls } }

private theorem capInclusion_continuous {L B : ℝ} (hB : 0 < B) :
    Continuous (capInclusion (L := L) hB) :=
  continuous_subtype_val.subtype_mk _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.capInclusion_continuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.capInclusion_continuous target :: scope.openDecls } }

private theorem shell_isClosed (L B : ℝ) :
    IsClosed {x : Ball L B | L ≤ ‖x.val‖} :=
  isClosed_le continuous_const (continuous_norm.comp continuous_subtype_val)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.shell_isClosed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.shell_isClosed target :: scope.openDecls } }

private theorem cap_isCompact (L : ℝ) : IsCompact {x : E3 | ‖x‖ ≤ L} := by
  have he : {x : E3 | ‖x‖ ≤ L} = Metric.closedBall (0 : E3) L := by
    ext x
    simp only [_root_.Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
  rw [he]
  exact _root_.ProperSpace.isCompact_closedBall 0 L

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.cap_isCompact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.cap_isCompact target :: scope.openDecls } }

private theorem capInclusion_boundary {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (x : Cap L) (hx : L ≤ ‖(capInclusion hB x).val‖) :
    x ∈ _root_.Set.range (radialCapBoundary hL) := by
  have hxnorm : ‖x.val‖ = L := le_antisymm x.property hx
  let p : ({0}ᶜ : Set E3) :=
    ⟨x.val, by simpa only [_root_.Set.mem_compl_iff, _root_.Set.mem_singleton_iff] using
      norm_pos_iff.mp (by rw [hxnorm]; exact hL)⟩
  refine ⟨(homeomorphUnitSphereProd E3 p).1, ?_⟩
  apply Subtype.ext
  change L • ((homeomorphUnitSphereProd E3 p).1 : E3) = x.val
  have h := congrArg (fun y : ({0}ᶜ : Set E3) => y.val)
    ((homeomorphUnitSphereProd E3).symm_apply_apply p)
  simpa only [homeomorphUnitSphereProd_symm_apply_coe,
    homeomorphUnitSphereProd_apply_snd_coe, p, hxnorm] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.capInclusion_boundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.capInclusion_boundary target :: scope.openDecls } }

private theorem shell_union_range_capInclusion {L B : ℝ} (hB : 0 < B) :
    {x : Ball L B | L ≤ ‖x.val‖} ∪ _root_.Set.range (capInclusion (L := L) hB) = univ := by
  ext x
  constructor
  · intro _
    exact _root_.Set.mem_univ x
  · intro _
    by_cases hx : L ≤ ‖x.val‖
    · exact Or.inl hx
    · exact Or.inr ⟨⟨x.val, (lt_of_not_ge hx).le⟩, Subtype.ext rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.shell_union_range_capInclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.shell_union_range_capInclusion target :: scope.openDecls } }

private theorem retainedBoundary_capInclusion {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (y : S2) :
    (retainedCylinderHomeomorphShell hL (retainedBoundary hB y)).val =
      capInclusion hB (radialCapBoundary hL y) := by
  apply Subtype.ext
  change (L + 0) • (y : E3) = L • (y : E3)
  rw [add_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.retainedBoundary_capInclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.retainedBoundary_capInclusion target :: scope.openDecls } }

def radialCapAttachmentHomeomorph {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    AdjunctionSpace (radialCapBoundary hL) (retainedBoundary hB) ≃ₜ
      {x : E3 // ‖x‖ < L + B} := by
  letI : CompactSpace (Cap L) := isCompact_iff_compactSpace.mp (cap_isCompact L)
  let H := retainedCylinderHomeomorphShell (B := B) hL
  let i := radialCapBoundary hL
  let φ := retainedBoundary hB
  let c := capInclusion (L := L) hB
  let Q := adjunctionHomeomorphUnionImage i (H ∘ φ) c
    (retainedBoundary_capInclusion hL hB)
    (capInclusion_injective hB) (capInclusion_continuous hB)
    (capInclusion_boundary hL hB) (shell_isClosed L B)
  exact ((adjunctionHomeoOfLowerEquiv i φ H).symm.trans Q).trans
    ((Homeomorph.setCongr (shell_union_range_capInclusion (L := L) hB)).trans
      (Homeomorph.Set.univ (Ball L B)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentHomeomorph ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentHomeomorph

theorem radialCapAttachmentHomeomorph_cap {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (x : Cap L) :
    (radialCapAttachmentHomeomorph hL hB
      (adjunctionCell (radialCapBoundary hL) (retainedBoundary hB) x) : E3) = x.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentHomeomorph_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentHomeomorph_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentHomeomorph_cap ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentHomeomorph_cap

theorem radialCapAttachmentHomeomorph_retained {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (q : Retained B) :
    (radialCapAttachmentHomeomorph hL hB
      (adjunctionLower (i := radialCapBoundary hL) (retainedBoundary hB) q) : E3) =
      (L + q.2.val) • (q.1 : E3) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentHomeomorph_retained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentHomeomorph_retained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentHomeomorph_retained ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCapAttachmentHomeomorph_retained

end DifferentialGeometry.Topology.Manifold.Attachment
