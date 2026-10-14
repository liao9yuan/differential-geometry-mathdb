import Submission.DifferentialGeometry.Analysis.Schauder.Holder.Space

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.BigOperators _root_.NNReal

namespace DifferentialGeometry.Analysis.Schauder

section BoundedHolder

variable {X F : Type*} [MetricSpace X]
  [NormedAddCommGroup F] [NormedSpace Real F]

def BoundedHolderSpace (alpha : NNReal) : Type _ :=
  ↑(boundedHolderSubmodule (X := X) (F := F) alpha)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.BoundedHolderSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.BoundedHolderSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.BoundedHolderSpace ``Submission.DifferentialGeometry.Analysis.Schauder.BoundedHolderSpace

instance _root_.Submission.DifferentialGeometry.Analysis.Schauder.instAddCommGroupBoundedHolderSpace (alpha : NNReal) :
    AddCommGroup (BoundedHolderSpace (X := X) (F := F) alpha) :=
  inferInstanceAs (AddCommGroup
    ↑(boundedHolderSubmodule (X := X) (F := F) alpha))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.instAddCommGroupBoundedHolderSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.instAddCommGroupBoundedHolderSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.instAddCommGroupBoundedHolderSpace ``Submission.DifferentialGeometry.Analysis.Schauder.instAddCommGroupBoundedHolderSpace

instance _root_.Submission.DifferentialGeometry.Analysis.Schauder.instModuleRealBoundedHolderSpace (alpha : NNReal) :
    Module Real (BoundedHolderSpace (X := X) (F := F) alpha) :=
  inferInstanceAs (Module Real
    ↑(boundedHolderSubmodule (X := X) (F := F) alpha))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.instModuleRealBoundedHolderSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.instModuleRealBoundedHolderSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.instModuleRealBoundedHolderSpace ``Submission.DifferentialGeometry.Analysis.Schauder.instModuleRealBoundedHolderSpace

def boundedHolderSpaceFun {alpha : NNReal}
    (f : BoundedHolderSpace (X := X) (F := F) alpha) : X → F :=
  f.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.boundedHolderSpaceFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.boundedHolderSpaceFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.boundedHolderSpaceFun ``Submission.DifferentialGeometry.Analysis.Schauder.boundedHolderSpaceFun

instance _root_.Submission.DifferentialGeometry.Analysis.Schauder.instCoeFunBoundedHolderSpaceForall {alpha : NNReal} :
    CoeFun (BoundedHolderSpace (X := X) (F := F) alpha)
      (fun _ ↦ X → F) where
  coe := boundedHolderSpaceFun

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.instCoeFunBoundedHolderSpaceForall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.instCoeFunBoundedHolderSpaceForall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.instCoeFunBoundedHolderSpaceForall ``Submission.DifferentialGeometry.Analysis.Schauder.instCoeFunBoundedHolderSpaceForall

@[simp]
theorem boundedHolderSpace_zero_apply {alpha : NNReal} (x : X) :
    (0 : BoundedHolderSpace (X := X) (F := F) alpha) x = 0 :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_zero_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_zero_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_zero_apply ``Submission.DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_zero_apply

@[simp]
theorem boundedHolderSpace_add_apply {alpha : NNReal}
    (f g : BoundedHolderSpace (X := X) (F := F) alpha) (x : X) :
    (f + g) x = f x + g x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_add_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_add_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_add_apply ``Submission.DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_add_apply

@[simp]
theorem boundedHolderSpace_neg_apply {alpha : NNReal}
    (f : BoundedHolderSpace (X := X) (F := F) alpha) (x : X) :
    (-f) x = -f x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_neg_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_neg_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_neg_apply ``Submission.DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_neg_apply

@[simp]
theorem boundedHolderSpace_sub_apply {alpha : NNReal}
    (f g : BoundedHolderSpace (X := X) (F := F) alpha) (x : X) :
    (f - g) x = f x - g x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_sub_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_sub_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_sub_apply ``Submission.DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_sub_apply

@[simp]
theorem boundedHolderSpace_sum_apply {ι : Type*} {alpha : NNReal}
    (s : Finset ι)
    (f : ι → BoundedHolderSpace (X := X) (F := F) alpha) (x : X) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_sum_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_sum_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_sum_apply ``Submission.DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_sum_apply

theorem boundedHolderSpace_isBoundedHolder {alpha : NNReal}
    (f : BoundedHolderSpace (X := X) (F := F) alpha) :
    IsBoundedHolder alpha f :=
  f.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_isBoundedHolder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_isBoundedHolder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_isBoundedHolder ``Submission.DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_isBoundedHolder

@[ext]
theorem boundedHolderSpace_ext {alpha : NNReal}
    {f g : BoundedHolderSpace (X := X) (F := F) alpha}
    (h : ∀ x, f x = g x) : f = g := by
  apply Subtype.ext
  funext x
  exact h x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_ext then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_ext"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_ext ``Submission.DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_ext

instance _root_.Submission.DifferentialGeometry.Analysis.Schauder.instNormBoundedHolderSpace (alpha : NNReal) :
    Norm (BoundedHolderSpace (X := X) (F := F) alpha) where
  norm f := (eHolderGauge alpha f).toReal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.instNormBoundedHolderSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.instNormBoundedHolderSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.instNormBoundedHolderSpace ``Submission.DifferentialGeometry.Analysis.Schauder.instNormBoundedHolderSpace

theorem boundedHolderSpace_normedSpaceCore (alpha : NNReal) :
    NormedSpace.Core Real
      (BoundedHolderSpace (X := X) (F := F) alpha) where
  norm_nonneg _ := ENNReal.toReal_nonneg
  norm_smul c f := by
    change (eHolderGauge alpha (c • boundedHolderSpaceFun f)).toReal =
      ‖c‖ * (eHolderGauge alpha (boundedHolderSpaceFun f)).toReal
    rw [eHolderGauge_smul, ENNReal.toReal_mul]
    rfl
  norm_triangle f g := by
    change (eHolderGauge alpha
      (boundedHolderSpaceFun f + boundedHolderSpaceFun g)).toReal ≤
        (eHolderGauge alpha (boundedHolderSpaceFun f)).toReal +
          (eHolderGauge alpha (boundedHolderSpaceFun g)).toReal
    have hle := eHolderGauge_add_le alpha
      (boundedHolderSpaceFun f) (boundedHolderSpaceFun g)
    have hfinite : eHolderGauge alpha (boundedHolderSpaceFun f) +
        eHolderGauge alpha (boundedHolderSpaceFun g) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨f.2, g.2⟩
    have hreal := ENNReal.toReal_mono hfinite hle
    exact hreal.trans_eq (ENNReal.toReal_add f.2 g.2)
  norm_eq_zero_iff f := by
    constructor
    · intro hnorm
      have hgauge : eHolderGauge alpha (boundedHolderSpaceFun f) = 0 :=
        (ENNReal.toReal_eq_zero_iff _).mp hnorm |>.resolve_right f.2
      apply Subtype.ext
      funext x
      apply norm_eq_zero.mp
      have hx := norm_le_eSupNormOn Set.univ
        (boundedHolderSpaceFun f) x (Set.mem_univ x)
      have hsup : eSupNormOn Set.univ (boundedHolderSpaceFun f) ≤
          eHolderGauge alpha (boundedHolderSpaceFun f) := by
        unfold eHolderGauge
        exact le_add_right le_rfl
      have hzero : ENNReal.ofReal ‖boundedHolderSpaceFun f x‖ = 0 := by
        exact nonpos_iff_eq_zero.mp (by simpa only [hgauge] using hx.trans hsup)
      exact le_antisymm (ENNReal.ofReal_eq_zero.mp hzero) (norm_nonneg _)
    · intro hf
      rw [hf]
      change (eHolderGauge alpha (0 : X → F)).toReal = 0
      simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_normedSpaceCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_normedSpaceCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_normedSpaceCore ``Submission.DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_normedSpaceCore

instance _root_.Submission.DifferentialGeometry.Analysis.Schauder.instNormedAddCommGroupBoundedHolderSpace (alpha : NNReal) :
    NormedAddCommGroup
      (BoundedHolderSpace (X := X) (F := F) alpha) :=
  NormedAddCommGroup.ofCore
    (boundedHolderSpace_normedSpaceCore (X := X) (F := F) alpha)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.instNormedAddCommGroupBoundedHolderSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.instNormedAddCommGroupBoundedHolderSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.instNormedAddCommGroupBoundedHolderSpace ``Submission.DifferentialGeometry.Analysis.Schauder.instNormedAddCommGroupBoundedHolderSpace

instance _root_.Submission.DifferentialGeometry.Analysis.Schauder.instNormedSpaceRealBoundedHolderSpace (alpha : NNReal) :
    NormedSpace Real
      (BoundedHolderSpace (X := X) (F := F) alpha) :=
  NormedSpace.ofCore
    (boundedHolderSpace_normedSpaceCore (X := X) (F := F) alpha)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.instNormedSpaceRealBoundedHolderSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.instNormedSpaceRealBoundedHolderSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.instNormedSpaceRealBoundedHolderSpace ``Submission.DifferentialGeometry.Analysis.Schauder.instNormedSpaceRealBoundedHolderSpace

theorem norm_boundedHolderSpace_eq {alpha : NNReal}
    (f : BoundedHolderSpace (X := X) (F := F) alpha) :
    ‖f‖ = (eHolderGauge alpha (boundedHolderSpaceFun f)).toReal :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.norm_boundedHolderSpace_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.norm_boundedHolderSpace_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.norm_boundedHolderSpace_eq ``Submission.DifferentialGeometry.Analysis.Schauder.norm_boundedHolderSpace_eq

theorem eHolderGauge_eq_ofReal_norm {alpha : NNReal}
    (f : BoundedHolderSpace (X := X) (F := F) alpha) :
    eHolderGauge alpha (boundedHolderSpaceFun f) = ENNReal.ofReal ‖f‖ := by
  rw [norm_boundedHolderSpace_eq]
  exact (ENNReal.ofReal_toReal f.2).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.eHolderGauge_eq_ofReal_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.eHolderGauge_eq_ofReal_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.eHolderGauge_eq_ofReal_norm ``Submission.DifferentialGeometry.Analysis.Schauder.eHolderGauge_eq_ofReal_norm

theorem norm_boundedHolderSpace_apply_le {alpha : NNReal}
    (f : BoundedHolderSpace (X := X) (F := F) alpha) (x : X) :
    ‖f x‖ ≤ ‖f‖ := by
  have hx := norm_le_eSupNormOn Set.univ
    (boundedHolderSpaceFun f) x (Set.mem_univ x)
  have hsup : eSupNormOn Set.univ (boundedHolderSpaceFun f) ≤
      eHolderGauge alpha (boundedHolderSpaceFun f) := by
    unfold eHolderGauge
    exact le_add_right le_rfl
  have hreal := ENNReal.toReal_mono f.2 (hx.trans hsup)
  rw [ENNReal.toReal_ofReal (norm_nonneg _)] at hreal
  change ‖boundedHolderSpaceFun f x‖ ≤
    (eHolderGauge alpha (boundedHolderSpaceFun f)).toReal at hreal
  rw [norm_boundedHolderSpace_eq]
  exact hreal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.norm_boundedHolderSpace_apply_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.norm_boundedHolderSpace_apply_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.norm_boundedHolderSpace_apply_le ``Submission.DifferentialGeometry.Analysis.Schauder.norm_boundedHolderSpace_apply_le

theorem boundedHolderSpace_holderWith {alpha : NNReal}
    (f : BoundedHolderSpace (X := X) (F := F) alpha) :
    HolderWith ‖f‖₊ alpha (boundedHolderSpaceFun f) := by
  have hle : (nnHolderNorm alpha (boundedHolderSpaceFun f) : ENNReal) ≤
      (‖f‖₊ : ENNReal) := by
    calc
      (nnHolderNorm alpha (boundedHolderSpaceFun f) : ENNReal) ≤
          eHolderNorm alpha (boundedHolderSpaceFun f) :=
        coe_nnHolderNorm_le_eHolderNorm
      _ ≤ eHolderGauge alpha (boundedHolderSpaceFun f) := by
        unfold eHolderGauge
        exact le_add_left le_rfl
      _ = (‖f‖₊ : ENNReal) := by
        rw [eHolderGauge_eq_ofReal_norm]
        simp only [ofReal_norm, enorm_eq_nnnorm]
  exact f.2.memHolder.holderWith.mono (ENNReal.coe_le_coe.mp hle)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_holderWith then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_holderWith"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_holderWith ``Submission.DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_holderWith

def boundedHolderSpaceHolderConst {alpha : NNReal}
    (f : BoundedHolderSpace (X := X) (F := F) alpha) : NNReal :=
  nnHolderNorm alpha (boundedHolderSpaceFun f)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.boundedHolderSpaceHolderConst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.boundedHolderSpaceHolderConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.boundedHolderSpaceHolderConst ``Submission.DifferentialGeometry.Analysis.Schauder.boundedHolderSpaceHolderConst

theorem boundedHolderSpace_holderWith_holderConst {alpha : NNReal}
    (f : BoundedHolderSpace (X := X) (F := F) alpha) :
    HolderWith (boundedHolderSpaceHolderConst f) alpha
      (boundedHolderSpaceFun f) :=
  f.2.memHolder.holderWith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_holderWith_holderConst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_holderWith_holderConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_holderWith_holderConst ``Submission.DifferentialGeometry.Analysis.Schauder.boundedHolderSpace_holderWith_holderConst

def boundedHolderSpaceOscillationAt {alpha : NNReal}
    (f : BoundedHolderSpace (X := X) (F := F) alpha) (x0 : X) : NNReal :=
  (eSupNormOn Set.univ fun x ↦ f x0 - f x).toNNReal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.boundedHolderSpaceOscillationAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.boundedHolderSpaceOscillationAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.boundedHolderSpaceOscillationAt ``Submission.DifferentialGeometry.Analysis.Schauder.boundedHolderSpaceOscillationAt

private theorem eSupNormOn_sub_at_ne_top {alpha : NNReal}
    (f : BoundedHolderSpace (X := X) (F := F) alpha) (x0 : X) :
    eSupNormOn Set.univ (fun x ↦ f x0 - f x) ≠ ⊤ := by
  have hle : eSupNormOn Set.univ (fun x ↦ f x0 - f x) ≤
      ((2 * ‖f‖₊ : NNReal) : ENNReal) := by
    rw [eSupNormOn_le]
    intro x _hx
    rw [ENNReal.ofReal_le_coe]
    calc
      ‖f x0 - f x‖ ≤ ‖f x0‖ + ‖f x‖ := norm_sub_le _ _
      _ ≤ ‖f‖ + ‖f‖ :=
        add_le_add (norm_boundedHolderSpace_apply_le f x0)
          (norm_boundedHolderSpace_apply_le f x)
      _ = ((2 * ‖f‖₊ : NNReal) : Real) := by
        simp only [NNReal.coe_mul, NNReal.coe_ofNat, coe_nnnorm]
        ring
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top hle

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Schauder.eSupNormOn_sub_at_ne_top
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Schauder.eSupNormOn_sub_at_ne_top target :: scope.openDecls } }

theorem norm_sub_le_boundedHolderSpaceOscillationAt {alpha : NNReal}
    (f : BoundedHolderSpace (X := X) (F := F) alpha) (x0 x : X) :
    ‖f x0 - f x‖ ≤ boundedHolderSpaceOscillationAt f x0 := by
  rw [← ENNReal.ofReal_le_coe]
  calc
    ENNReal.ofReal ‖f x0 - f x‖ ≤
        eSupNormOn Set.univ (fun y ↦ f x0 - f y) :=
      norm_le_eSupNormOn Set.univ (fun y ↦ f x0 - f y) x
        (Set.mem_univ x)
    _ = (boundedHolderSpaceOscillationAt f x0 : ENNReal) := by
      exact (ENNReal.coe_toNNReal (eSupNormOn_sub_at_ne_top f x0)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.norm_sub_le_boundedHolderSpaceOscillationAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.norm_sub_le_boundedHolderSpaceOscillationAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.norm_sub_le_boundedHolderSpaceOscillationAt ``Submission.DifferentialGeometry.Analysis.Schauder.norm_sub_le_boundedHolderSpaceOscillationAt

end BoundedHolder

section ParabolicHolder

variable {V F : Type*} [MetricSpace V]
  [NormedAddCommGroup F] [NormedSpace Real F]

abbrev ParabolicHolderSpace (alpha : NNReal) : Type _ :=
  BoundedHolderSpace (X := ParabolicPoint V) (F := F) alpha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.ParabolicHolderSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.ParabolicHolderSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.ParabolicHolderSpace ``Submission.DifferentialGeometry.Analysis.Schauder.ParabolicHolderSpace

end ParabolicHolder

section Elliptic

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

def ContDiffHolderSpace (k : Nat) (alpha : NNReal) : Type _ :=
  ↑(boundedContDiffHolderOnSubmodule (V := V) (F := F)
    k alpha Set.univ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.ContDiffHolderSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.ContDiffHolderSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.ContDiffHolderSpace ``Submission.DifferentialGeometry.Analysis.Schauder.ContDiffHolderSpace

instance _root_.Submission.DifferentialGeometry.Analysis.Schauder.instAddCommGroupContDiffHolderSpace (k : Nat) (alpha : NNReal) :
    AddCommGroup (ContDiffHolderSpace (V := V) (F := F) k alpha) :=
  inferInstanceAs (AddCommGroup
    ↑(boundedContDiffHolderOnSubmodule (V := V) (F := F)
      k alpha Set.univ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.instAddCommGroupContDiffHolderSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.instAddCommGroupContDiffHolderSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.instAddCommGroupContDiffHolderSpace ``Submission.DifferentialGeometry.Analysis.Schauder.instAddCommGroupContDiffHolderSpace

instance _root_.Submission.DifferentialGeometry.Analysis.Schauder.instModuleRealContDiffHolderSpace (k : Nat) (alpha : NNReal) :
    Module Real (ContDiffHolderSpace (V := V) (F := F) k alpha) :=
  inferInstanceAs (Module Real
    ↑(boundedContDiffHolderOnSubmodule (V := V) (F := F)
      k alpha Set.univ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.instModuleRealContDiffHolderSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.instModuleRealContDiffHolderSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.instModuleRealContDiffHolderSpace ``Submission.DifferentialGeometry.Analysis.Schauder.instModuleRealContDiffHolderSpace

def contDiffHolderSpaceFun {k : Nat} {alpha : NNReal}
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) : V → F :=
  f.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.contDiffHolderSpaceFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.contDiffHolderSpaceFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.contDiffHolderSpaceFun ``Submission.DifferentialGeometry.Analysis.Schauder.contDiffHolderSpaceFun

instance _root_.Submission.DifferentialGeometry.Analysis.Schauder.instCoeFunContDiffHolderSpaceForall {k : Nat} {alpha : NNReal} :
    CoeFun (ContDiffHolderSpace (V := V) (F := F) k alpha)
      (fun _ ↦ V → F) where
  coe := contDiffHolderSpaceFun

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.instCoeFunContDiffHolderSpaceForall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.instCoeFunContDiffHolderSpaceForall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.instCoeFunContDiffHolderSpaceForall ``Submission.DifferentialGeometry.Analysis.Schauder.instCoeFunContDiffHolderSpaceForall

@[simp]
theorem contDiffHolderSpace_zero_apply {k : Nat} {alpha : NNReal} (x : V) :
    (0 : ContDiffHolderSpace (V := V) (F := F) k alpha) x = 0 :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_zero_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_zero_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_zero_apply ``Submission.DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_zero_apply

@[simp]
theorem contDiffHolderSpace_add_apply {k : Nat} {alpha : NNReal}
    (f g : ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    (f + g) x = f x + g x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_add_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_add_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_add_apply ``Submission.DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_add_apply

@[simp]
theorem contDiffHolderSpace_neg_apply {k : Nat} {alpha : NNReal}
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    (-f) x = -f x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_neg_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_neg_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_neg_apply ``Submission.DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_neg_apply

@[simp]
theorem contDiffHolderSpace_sub_apply {k : Nat} {alpha : NNReal}
    (f g : ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    (f - g) x = f x - g x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_sub_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_sub_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_sub_apply ``Submission.DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_sub_apply

@[simp]
theorem contDiffHolderSpace_sum_apply {ι : Type*} {k : Nat} {alpha : NNReal}
    (s : Finset ι)
    (f : ι → ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_sum_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_sum_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_sum_apply ``Submission.DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_sum_apply

theorem contDiffHolderSpace_isBoundedContDiffHolderOn
    {k : Nat} {alpha : NNReal}
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) :
    IsBoundedContDiffHolderOn k alpha Set.univ f :=
  f.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_isBoundedContDiffHolderOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_isBoundedContDiffHolderOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_isBoundedContDiffHolderOn ``Submission.DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_isBoundedContDiffHolderOn

@[ext]
theorem contDiffHolderSpace_ext {k : Nat} {alpha : NNReal}
    {f g : ContDiffHolderSpace (V := V) (F := F) k alpha}
    (h : ∀ x, f x = g x) : f = g := by
  apply Subtype.ext
  funext x
  exact h x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_ext then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_ext"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_ext ``Submission.DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_ext

instance _root_.Submission.DifferentialGeometry.Analysis.Schauder.instNormContDiffHolderSpace (k : Nat) (alpha : NNReal) :
    Norm (ContDiffHolderSpace (V := V) (F := F) k alpha) where
  norm f := (eContDiffHolderGaugeOn k alpha Set.univ f).toReal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.instNormContDiffHolderSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.instNormContDiffHolderSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.instNormContDiffHolderSpace ``Submission.DifferentialGeometry.Analysis.Schauder.instNormContDiffHolderSpace

theorem contDiffHolderSpace_normedSpaceCore (k : Nat) (alpha : NNReal) :
    NormedSpace.Core Real
      (ContDiffHolderSpace (V := V) (F := F) k alpha) where
  norm_nonneg _ := ENNReal.toReal_nonneg
  norm_smul c f := by
    change (eContDiffHolderGaugeOn k alpha Set.univ
      (c • contDiffHolderSpaceFun f)).toReal =
        ‖c‖ * (eContDiffHolderGaugeOn k alpha Set.univ
          (contDiffHolderSpaceFun f)).toReal
    rw [eContDiffHolderGaugeOn_smul k alpha Set.univ
      (contDiffHolderSpaceFun f) c f.2.1.1, ENNReal.toReal_mul]
    rfl
  norm_triangle f g := by
    change (eContDiffHolderGaugeOn k alpha Set.univ
      (contDiffHolderSpaceFun f + contDiffHolderSpaceFun g)).toReal ≤
        (eContDiffHolderGaugeOn k alpha Set.univ
          (contDiffHolderSpaceFun f)).toReal +
        (eContDiffHolderGaugeOn k alpha Set.univ
          (contDiffHolderSpaceFun g)).toReal
    have hle := eContDiffHolderGaugeOn_add_le k alpha Set.univ
      (contDiffHolderSpaceFun f) (contDiffHolderSpaceFun g)
      f.2.1.1 g.2.1.1
    have hfinite :
        eContDiffHolderGaugeOn k alpha Set.univ (contDiffHolderSpaceFun f) +
          eContDiffHolderGaugeOn k alpha Set.univ (contDiffHolderSpaceFun g) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨f.2.2, g.2.2⟩
    have hreal := ENNReal.toReal_mono hfinite hle
    exact hreal.trans_eq (ENNReal.toReal_add f.2.2 g.2.2)
  norm_eq_zero_iff f := by
    constructor
    · intro hnorm
      have hgauge :
          eContDiffHolderGaugeOn k alpha Set.univ
            (contDiffHolderSpaceFun f) = 0 :=
        (ENNReal.toReal_eq_zero_iff _).mp hnorm |>.resolve_right f.2.2
      apply Subtype.ext
      funext x
      apply norm_eq_zero.mp
      have hx := spatialJet_le_eContDiffHolderGaugeOn k alpha Set.univ
        (contDiffHolderSpaceFun f) (j := 0) (Nat.zero_le k) x (Set.mem_univ x)
      rw [hgauge] at hx
      have hzero :
          ‖iteratedFDeriv Real 0 (contDiffHolderSpaceFun f) x‖ = 0 := by
        apply le_antisymm
        · exact ENNReal.ofReal_eq_zero.mp (nonpos_iff_eq_zero.mp hx)
        · exact norm_nonneg _
      change ‖contDiffHolderSpaceFun f x‖ = 0
      simpa only [norm_iteratedFDeriv_zero] using hzero
    · intro hf
      rw [hf]
      change (eContDiffHolderGaugeOn k alpha Set.univ (0 : V → F)).toReal = 0
      simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_normedSpaceCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_normedSpaceCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_normedSpaceCore ``Submission.DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_normedSpaceCore

instance _root_.Submission.DifferentialGeometry.Analysis.Schauder.instNormedAddCommGroupContDiffHolderSpace (k : Nat) (alpha : NNReal) :
    NormedAddCommGroup
      (ContDiffHolderSpace (V := V) (F := F) k alpha) :=
  NormedAddCommGroup.ofCore
    (contDiffHolderSpace_normedSpaceCore (V := V) (F := F) k alpha)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.instNormedAddCommGroupContDiffHolderSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.instNormedAddCommGroupContDiffHolderSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.instNormedAddCommGroupContDiffHolderSpace ``Submission.DifferentialGeometry.Analysis.Schauder.instNormedAddCommGroupContDiffHolderSpace

instance _root_.Submission.DifferentialGeometry.Analysis.Schauder.instNormedSpaceRealContDiffHolderSpace (k : Nat) (alpha : NNReal) :
    NormedSpace Real
      (ContDiffHolderSpace (V := V) (F := F) k alpha) :=
  NormedSpace.ofCore
    (contDiffHolderSpace_normedSpaceCore (V := V) (F := F) k alpha)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.instNormedSpaceRealContDiffHolderSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.instNormedSpaceRealContDiffHolderSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.instNormedSpaceRealContDiffHolderSpace ``Submission.DifferentialGeometry.Analysis.Schauder.instNormedSpaceRealContDiffHolderSpace

theorem norm_contDiffHolderSpace_eq {k : Nat} {alpha : NNReal}
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) :
    ‖f‖ = (eContDiffHolderGaugeOn k alpha Set.univ
      (contDiffHolderSpaceFun f)).toReal :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.norm_contDiffHolderSpace_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.norm_contDiffHolderSpace_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.norm_contDiffHolderSpace_eq ``Submission.DifferentialGeometry.Analysis.Schauder.norm_contDiffHolderSpace_eq

theorem eContDiffHolderGaugeOn_eq_ofReal_norm {k : Nat} {alpha : NNReal}
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) :
    eContDiffHolderGaugeOn k alpha Set.univ (contDiffHolderSpaceFun f) =
      ENNReal.ofReal ‖f‖ := by
  rw [norm_contDiffHolderSpace_eq]
  exact (ENNReal.ofReal_toReal f.2.2).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.eContDiffHolderGaugeOn_eq_ofReal_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.eContDiffHolderGaugeOn_eq_ofReal_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.eContDiffHolderGaugeOn_eq_ofReal_norm ``Submission.DifferentialGeometry.Analysis.Schauder.eContDiffHolderGaugeOn_eq_ofReal_norm

theorem contDiffHolderSpace_iteratedFDeriv_norm_le
    {k : Nat} {alpha : NNReal}
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha)
    {j : Nat} (hj : j ≤ k) (x : V) :
    ‖iteratedFDeriv Real j (contDiffHolderSpaceFun f) x‖ ≤ ‖f‖ := by
  have hle := spatialJet_le_eContDiffHolderGaugeOn k alpha Set.univ
    (contDiffHolderSpaceFun f) (j := j) hj x (Set.mem_univ x)
  have hreal := ENNReal.toReal_mono f.2.2 hle
  rw [ENNReal.toReal_ofReal (norm_nonneg _)] at hreal
  change ‖iteratedFDeriv Real j (contDiffHolderSpaceFun f) x‖ ≤
    (eContDiffHolderGaugeOn k alpha Set.univ (contDiffHolderSpaceFun f)).toReal at hreal
  rw [norm_contDiffHolderSpace_eq]
  exact hreal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_iteratedFDeriv_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_iteratedFDeriv_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_iteratedFDeriv_norm_le ``Submission.DifferentialGeometry.Analysis.Schauder.contDiffHolderSpace_iteratedFDeriv_norm_le

theorem norm_contDiffHolderSpace_apply_le {k : Nat} {alpha : NNReal}
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    ‖f x‖ ≤ ‖f‖ := by
  simpa only [norm_iteratedFDeriv_zero] using
    contDiffHolderSpace_iteratedFDeriv_norm_le f (Nat.zero_le k) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.norm_contDiffHolderSpace_apply_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.norm_contDiffHolderSpace_apply_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.norm_contDiffHolderSpace_apply_le ``Submission.DifferentialGeometry.Analysis.Schauder.norm_contDiffHolderSpace_apply_le

end Elliptic

section Parabolic

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

def ParabolicC2HolderSpace (alpha : NNReal) : Type _ :=
  ↑(boundedParabolicC2HolderOnSubmodule (V := V) (F := F)
    alpha Set.univ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.ParabolicC2HolderSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.ParabolicC2HolderSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.ParabolicC2HolderSpace ``Submission.DifferentialGeometry.Analysis.Schauder.ParabolicC2HolderSpace

instance _root_.Submission.DifferentialGeometry.Analysis.Schauder.instAddCommGroupParabolicC2HolderSpace (alpha : NNReal) :
    AddCommGroup (ParabolicC2HolderSpace (V := V) (F := F) alpha) :=
  inferInstanceAs (AddCommGroup
    ↑(boundedParabolicC2HolderOnSubmodule (V := V) (F := F)
      alpha Set.univ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.instAddCommGroupParabolicC2HolderSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.instAddCommGroupParabolicC2HolderSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.instAddCommGroupParabolicC2HolderSpace ``Submission.DifferentialGeometry.Analysis.Schauder.instAddCommGroupParabolicC2HolderSpace

instance _root_.Submission.DifferentialGeometry.Analysis.Schauder.instModuleRealParabolicC2HolderSpace (alpha : NNReal) :
    Module Real (ParabolicC2HolderSpace (V := V) (F := F) alpha) :=
  inferInstanceAs (Module Real
    ↑(boundedParabolicC2HolderOnSubmodule (V := V) (F := F)
      alpha Set.univ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.instModuleRealParabolicC2HolderSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.instModuleRealParabolicC2HolderSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.instModuleRealParabolicC2HolderSpace ``Submission.DifferentialGeometry.Analysis.Schauder.instModuleRealParabolicC2HolderSpace

def parabolicC2HolderSpaceFun {alpha : NNReal}
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha) :
    Real → V → F :=
  u.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpaceFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpaceFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpaceFun ``Submission.DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpaceFun

instance _root_.Submission.DifferentialGeometry.Analysis.Schauder.instCoeFunParabolicC2HolderSpaceForallRealForall {alpha : NNReal} :
    CoeFun (ParabolicC2HolderSpace (V := V) (F := F) alpha)
      (fun _ ↦ Real → V → F) where
  coe := parabolicC2HolderSpaceFun

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.instCoeFunParabolicC2HolderSpaceForallRealForall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.instCoeFunParabolicC2HolderSpaceForallRealForall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.instCoeFunParabolicC2HolderSpaceForallRealForall ``Submission.DifferentialGeometry.Analysis.Schauder.instCoeFunParabolicC2HolderSpaceForallRealForall

@[simp]
theorem parabolicC2HolderSpace_zero_apply {alpha : NNReal}
    (t : Real) (x : V) :
    (0 : ParabolicC2HolderSpace (V := V) (F := F) alpha) t x = 0 :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_zero_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_zero_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_zero_apply ``Submission.DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_zero_apply

@[simp]
theorem parabolicC2HolderSpace_add_apply {alpha : NNReal}
    (u v : ParabolicC2HolderSpace (V := V) (F := F) alpha)
    (t : Real) (x : V) :
    (u + v) t x = u t x + v t x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_add_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_add_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_add_apply ``Submission.DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_add_apply

@[simp]
theorem parabolicC2HolderSpace_neg_apply {alpha : NNReal}
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha)
    (t : Real) (x : V) :
    (-u) t x = -u t x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_neg_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_neg_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_neg_apply ``Submission.DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_neg_apply

@[simp]
theorem parabolicC2HolderSpace_sub_apply {alpha : NNReal}
    (u v : ParabolicC2HolderSpace (V := V) (F := F) alpha)
    (t : Real) (x : V) :
    (u - v) t x = u t x - v t x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_sub_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_sub_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_sub_apply ``Submission.DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_sub_apply

@[simp]
theorem parabolicC2HolderSpace_sum_apply
    {ι : Type*} {alpha : NNReal} (s : Finset ι)
    (u : ι → ParabolicC2HolderSpace (V := V) (F := F) alpha)
    (t : Real) (x : V) :
    (∑ i ∈ s, u i) t x = ∑ i ∈ s, u i t x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_sum_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_sum_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_sum_apply ``Submission.DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_sum_apply

theorem parabolicC2HolderSpace_isBoundedParabolicC2HolderOn
    {alpha : NNReal}
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha) :
    IsBoundedParabolicC2HolderOn alpha Set.univ u :=
  u.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_isBoundedParabolicC2HolderOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_isBoundedParabolicC2HolderOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_isBoundedParabolicC2HolderOn ``Submission.DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_isBoundedParabolicC2HolderOn

@[ext]
theorem parabolicC2HolderSpace_ext {alpha : NNReal}
    {u v : ParabolicC2HolderSpace (V := V) (F := F) alpha}
    (h : ∀ t x, u t x = v t x) : u = v := by
  apply Subtype.ext
  funext t x
  exact h t x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_ext then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_ext"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_ext ``Submission.DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_ext

instance _root_.Submission.DifferentialGeometry.Analysis.Schauder.instNormParabolicC2HolderSpace (alpha : NNReal) :
    Norm (ParabolicC2HolderSpace (V := V) (F := F) alpha) where
  norm u := (eParabolicC2HolderGaugeOn alpha Set.univ u).toReal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.instNormParabolicC2HolderSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.instNormParabolicC2HolderSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.instNormParabolicC2HolderSpace ``Submission.DifferentialGeometry.Analysis.Schauder.instNormParabolicC2HolderSpace

theorem parabolicC2HolderSpace_normedSpaceCore (alpha : NNReal) :
    NormedSpace.Core Real
      (ParabolicC2HolderSpace (V := V) (F := F) alpha) where
  norm_nonneg _ := ENNReal.toReal_nonneg
  norm_smul c u := by
    change (eParabolicC2HolderGaugeOn alpha Set.univ
      (c • parabolicC2HolderSpaceFun u)).toReal =
        ‖c‖ * (eParabolicC2HolderGaugeOn alpha Set.univ
          (parabolicC2HolderSpaceFun u)).toReal
    rw [eParabolicC2HolderGaugeOn_smul alpha Set.univ
      (parabolicC2HolderSpaceFun u) c u.2.1.1, ENNReal.toReal_mul]
    rfl
  norm_triangle u v := by
    change (eParabolicC2HolderGaugeOn alpha Set.univ
      (parabolicC2HolderSpaceFun u + parabolicC2HolderSpaceFun v)).toReal ≤
        (eParabolicC2HolderGaugeOn alpha Set.univ
          (parabolicC2HolderSpaceFun u)).toReal +
        (eParabolicC2HolderGaugeOn alpha Set.univ
          (parabolicC2HolderSpaceFun v)).toReal
    have hle := eParabolicC2HolderGaugeOn_add_le alpha Set.univ
      (parabolicC2HolderSpaceFun u) (parabolicC2HolderSpaceFun v)
      u.2.1.1 v.2.1.1
    have hfinite :
        eParabolicC2HolderGaugeOn alpha Set.univ (parabolicC2HolderSpaceFun u) +
          eParabolicC2HolderGaugeOn alpha Set.univ
            (parabolicC2HolderSpaceFun v) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨u.2.2, v.2.2⟩
    have hreal := ENNReal.toReal_mono hfinite hle
    exact hreal.trans_eq (ENNReal.toReal_add u.2.2 v.2.2)
  norm_eq_zero_iff u := by
    constructor
    · intro hnorm
      have hgauge :
          eParabolicC2HolderGaugeOn alpha Set.univ
            (parabolicC2HolderSpaceFun u) = 0 :=
        (ENNReal.toReal_eq_zero_iff _).mp hnorm |>.resolve_right u.2.2
      apply Subtype.ext
      funext t x
      apply norm_eq_zero.mp
      have hjet := parabolicSpatialJet_le alpha Set.univ
        (parabolicC2HolderSpaceFun u) (j := 0) (by omega)
        (parabolicPoint t x) (Set.mem_univ _)
      rw [hgauge] at hjet
      have hzero :
          ‖parabolicSpatialJet 0 (parabolicC2HolderSpaceFun u)
            (parabolicPoint t x)‖ = 0 := by
        apply le_antisymm
        · exact ENNReal.ofReal_eq_zero.mp (nonpos_iff_eq_zero.mp hjet)
        · exact norm_nonneg _
      change ‖parabolicC2HolderSpaceFun u t x‖ = 0
      simpa only [parabolicSpatialJet, parabolicPoint_time,
        parabolicPoint_space, norm_iteratedFDeriv_zero] using hzero
    · intro hu
      rw [hu]
      change (eParabolicC2HolderGaugeOn alpha Set.univ
        (0 : Real → V → F)).toReal = 0
      simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_normedSpaceCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_normedSpaceCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_normedSpaceCore ``Submission.DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_normedSpaceCore

instance _root_.Submission.DifferentialGeometry.Analysis.Schauder.instNormedAddCommGroupParabolicC2HolderSpace (alpha : NNReal) :
    NormedAddCommGroup
      (ParabolicC2HolderSpace (V := V) (F := F) alpha) :=
  NormedAddCommGroup.ofCore
    (parabolicC2HolderSpace_normedSpaceCore (V := V) (F := F) alpha)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.instNormedAddCommGroupParabolicC2HolderSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.instNormedAddCommGroupParabolicC2HolderSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.instNormedAddCommGroupParabolicC2HolderSpace ``Submission.DifferentialGeometry.Analysis.Schauder.instNormedAddCommGroupParabolicC2HolderSpace

instance _root_.Submission.DifferentialGeometry.Analysis.Schauder.instNormedSpaceRealParabolicC2HolderSpace (alpha : NNReal) :
    NormedSpace Real
      (ParabolicC2HolderSpace (V := V) (F := F) alpha) :=
  NormedSpace.ofCore
    (parabolicC2HolderSpace_normedSpaceCore (V := V) (F := F) alpha)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.instNormedSpaceRealParabolicC2HolderSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.instNormedSpaceRealParabolicC2HolderSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.instNormedSpaceRealParabolicC2HolderSpace ``Submission.DifferentialGeometry.Analysis.Schauder.instNormedSpaceRealParabolicC2HolderSpace

theorem norm_parabolicC2HolderSpace_eq {alpha : NNReal}
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha) :
    ‖u‖ = (eParabolicC2HolderGaugeOn alpha Set.univ
      (parabolicC2HolderSpaceFun u)).toReal :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.norm_parabolicC2HolderSpace_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.norm_parabolicC2HolderSpace_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.norm_parabolicC2HolderSpace_eq ``Submission.DifferentialGeometry.Analysis.Schauder.norm_parabolicC2HolderSpace_eq

theorem eParabolicC2HolderGaugeOn_eq_ofReal_norm {alpha : NNReal}
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha) :
    eParabolicC2HolderGaugeOn alpha Set.univ
      (parabolicC2HolderSpaceFun u) = ENNReal.ofReal ‖u‖ := by
  rw [norm_parabolicC2HolderSpace_eq]
  exact (ENNReal.ofReal_toReal u.2.2).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.eParabolicC2HolderGaugeOn_eq_ofReal_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.eParabolicC2HolderGaugeOn_eq_ofReal_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.eParabolicC2HolderGaugeOn_eq_ofReal_norm ``Submission.DifferentialGeometry.Analysis.Schauder.eParabolicC2HolderGaugeOn_eq_ofReal_norm

theorem parabolicC2HolderSpace_spatialJet_norm_le {alpha : NNReal}
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha)
    {j : Nat} (hj : j ≤ 2) (p : ParabolicPoint V) :
    ‖parabolicSpatialJet j (parabolicC2HolderSpaceFun u) p‖ ≤ ‖u‖ := by
  have hle := parabolicSpatialJet_le alpha Set.univ
    (parabolicC2HolderSpaceFun u) (j := j) (by omega) p (Set.mem_univ _)
  have hreal := ENNReal.toReal_mono u.2.2 hle
  rw [ENNReal.toReal_ofReal (norm_nonneg _)] at hreal
  change ‖parabolicSpatialJet j (parabolicC2HolderSpaceFun u) p‖ ≤
    (eParabolicC2HolderGaugeOn alpha Set.univ (parabolicC2HolderSpaceFun u)).toReal at hreal
  rw [norm_parabolicC2HolderSpace_eq]
  exact hreal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_spatialJet_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_spatialJet_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_spatialJet_norm_le ``Submission.DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_spatialJet_norm_le

theorem parabolicC2HolderSpace_timeDerivative_norm_le {alpha : NNReal}
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha)
    (p : ParabolicPoint V) :
    ‖parabolicTimeDerivative (parabolicC2HolderSpaceFun u) p‖ ≤ ‖u‖ := by
  have hle := parabolicTimeDerivative_le alpha Set.univ
    (parabolicC2HolderSpaceFun u) p (Set.mem_univ _)
  have hreal := ENNReal.toReal_mono u.2.2 hle
  rw [ENNReal.toReal_ofReal (norm_nonneg _)] at hreal
  change ‖parabolicTimeDerivative (parabolicC2HolderSpaceFun u) p‖ ≤
    (eParabolicC2HolderGaugeOn alpha Set.univ (parabolicC2HolderSpaceFun u)).toReal at hreal
  rw [norm_parabolicC2HolderSpace_eq]
  exact hreal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_timeDerivative_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_timeDerivative_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_timeDerivative_norm_le ``Submission.DifferentialGeometry.Analysis.Schauder.parabolicC2HolderSpace_timeDerivative_norm_le

theorem norm_parabolicC2HolderSpace_apply_le {alpha : NNReal}
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha)
    (t : Real) (x : V) :
    ‖u t x‖ ≤ ‖u‖ := by
  simpa only [parabolicSpatialJet, parabolicPoint_time,
    parabolicPoint_space, norm_iteratedFDeriv_zero] using
      parabolicC2HolderSpace_spatialJet_norm_le u (j := 0) (by omega)
        (parabolicPoint t x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.norm_parabolicC2HolderSpace_apply_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.norm_parabolicC2HolderSpace_apply_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.norm_parabolicC2HolderSpace_apply_le ``Submission.DifferentialGeometry.Analysis.Schauder.norm_parabolicC2HolderSpace_apply_le

end Parabolic

end DifferentialGeometry.Analysis.Schauder
