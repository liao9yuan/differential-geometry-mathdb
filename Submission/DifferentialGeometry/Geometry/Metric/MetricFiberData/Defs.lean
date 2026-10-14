import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Tensor0SBundle

noncomputable section

structure MetricFiberData (V : Type*) [AddCommGroup V] [Module Real V]
    [FiniteDimensional Real V] where
  flat : V ≃ₗ[Real] Module.Dual Real V
  symm : forall v w : V, flat v w = flat w v
  nonneg : forall v : V, 0 <= flat v v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData

namespace MetricFiberData

variable {V : Type*} [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]

omit [FiniteDimensional ℝ V] in
private theorem dual_finrank_eq :
    Module.finrank Real V = Module.finrank Real (Module.Dual Real V) :=
  Subspace.dual_finrank_eq.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.dual_finrank_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor0SBundle.MetricFiberData.dual_finrank_eq target :: scope.openDecls } }

def ofFlat
    (flat : V →ₗ[Real] Module.Dual Real V)
    (hinj : Function.Injective flat)
    (hsymm : forall v w : V, flat v w = flat w v)
    (hnonneg : forall v : V, 0 <= flat v v) :
    MetricFiberData V where
  flat := LinearMap.linearEquivOfInjective flat hinj dual_finrank_eq
  symm := hsymm
  nonneg := hnonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.ofFlat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.ofFlat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.ofFlat ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.ofFlat

def inner (D : MetricFiberData V) (v w : V) : Real :=
  D.flat v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner

def sharp (D : MetricFiberData V) : Module.Dual Real V ≃ₗ[Real] V :=
  D.flat.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.sharp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.sharp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.sharp ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.sharp

@[simp] theorem inner_apply (D : MetricFiberData V) (v w : V) :
    D.inner v w = D.flat v w := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner_apply ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner_apply

theorem inner_comm (D : MetricFiberData V) (v w : V) :
    D.inner v w = D.inner w v := by
  exact D.symm v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner_comm ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner_comm

theorem inner_nonneg (D : MetricFiberData V) (v : V) :
    0 <= D.inner v v := by
  exact D.nonneg v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner_nonneg ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner_nonneg

theorem inner_self_eq_zero_iff (D : MetricFiberData V) (v : V) :
    D.inner v v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    have hvw : forall w : V, D.inner v w = 0 := by
      intro w
      by_contra hne
      let a := D.inner v w
      let b := D.inner w w
      let t := -((b + 1) / (2 * a))
      have ha : a ≠ 0 := hne
      have hquad : 0 <= D.inner (w + t • v) (w + t • v) :=
        D.inner_nonneg (w + t • v)
      have hcalc : D.inner (w + t • v) (w + t • v) = -1 := by
        have hexpand :
            D.inner (w + t • v) (w + t • v) =
              b + 2 * t * a + t * t * D.inner v v := by
          unfold inner a b
          simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
            smul_eq_mul]
          rw [D.symm w v]
          simp [inner]
          ring_nf
        rw [hexpand, hv]
        unfold t b a
        field_simp [ha]
        ring
      linarith
    have hflat : D.flat v = 0 := by
      ext w
      exact hvw w
    exact D.flat.injective (by simpa using hflat)
  · intro hv
    simp [hv, inner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner_self_eq_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner_self_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner_self_eq_zero_iff ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner_self_eq_zero_iff

theorem inner_pos_of_ne_zero (D : MetricFiberData V) {v : V} (hv : v ≠ 0) :
    0 < D.inner v v := by
  have hnonneg := D.inner_nonneg v
  have hne : D.inner v v ≠ 0 := by
    intro hzero
    exact hv ((D.inner_self_eq_zero_iff v).1 hzero)
  exact lt_of_le_of_ne' hnonneg hne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner_pos_of_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner_pos_of_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner_pos_of_ne_zero ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.inner_pos_of_ne_zero

@[reducible] def toCore (D : MetricFiberData V) : InnerProductSpace.Core Real V where
  inner := fun v w => D.inner v w
  conj_inner_symm := by
    intro x y
    exact D.symm y x
  re_inner_nonneg := by
    intro x
    simpa using D.inner_nonneg x
  add_left := by
    intro x y z
    simp [MetricFiberData.inner, map_add]
  smul_left := by
    intro x y r
    simp [MetricFiberData.inner, smul_eq_mul]
  definite := by
    intro x hx
    exact (D.inner_self_eq_zero_iff x).1 (by simpa using hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.toCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.toCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.toCore ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.toCore

theorem toCore_inner (D : MetricFiberData V) (v w : V) :
    letI : InnerProductSpace.Core Real V := D.toCore
    letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup
    letI : InnerProductSpace Real V :=
      @InnerProductSpace.ofCore Real V _ _ _ D.toCore.toCore
    Inner.inner Real v w = D.inner v w := by
  change D.toCore.inner v w = D.inner v w
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.toCore_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.toCore_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.toCore_inner ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.toCore_inner

def orthogonal (D : MetricFiberData V) (W : Submodule Real V) : Submodule Real V :=
  LinearMap.BilinForm.orthogonal D.flat.toLinearMap W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.orthogonal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.orthogonal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.orthogonal ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.orthogonal

@[simp] theorem mem_orthogonal
    (D : MetricFiberData V) (W : Submodule Real V) (v : V) :
    v ∈ D.orthogonal W ↔ ∀ w ∈ W, D.inner w v = 0 :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.mem_orthogonal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.mem_orthogonal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.mem_orthogonal ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.mem_orthogonal

def IsSymmetric (D : MetricFiberData V) (A : V →ₗ[Real] V) : Prop :=
  ∀ v w, D.inner (A v) w = D.inner v (A w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.IsSymmetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.IsSymmetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.IsSymmetric ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.IsSymmetric

theorem trace_pos_of_isSymmetric_of_nonneg_of_ne_zero
    (D : MetricFiberData V) (A : V →ₗ[Real] V)
    (hAsymm : D.IsSymmetric A)
    (hAnonneg : ∀ v : V, 0 ≤ D.inner (A v) v)
    (hAne : A ≠ 0) :
    0 < LinearMap.trace Real V A := by
  let addV : AddCommGroup V := inferInstance
  let modV : Module Real V := inferInstance
  let _ : InnerProductSpace.Core Real V := D.toCore
  let _ : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real V _ addV modV D.toCore
  let _ : AddCommGroup V := addV
  let _ : Module Real V := modV
  let _ : InnerProductSpace Real V :=
    @InnerProductSpace.ofCore Real V _ _ _ D.toCore.toCore
  have hApos : A.IsPositive := by
    rw [LinearMap.isPositive_iff]
    constructor
    · intro x y
      rw [MetricFiberData.toCore_inner D, MetricFiberData.toCore_inner D]
      exact hAsymm x y
    · intro x
      rw [MetricFiberData.toCore_inner D]
      exact hAnonneg x
  let B : OrthonormalBasis (Fin (Module.finrank Real V)) Real V :=
    stdOrthonormalBasis Real V
  let mat : Matrix (Fin (Module.finrank Real V)) (Fin (Module.finrank Real V)) Real :=
    LinearMap.toMatrix B.toBasis B.toBasis A
  have hmat : mat.PosSemidef := by
    dsimp [mat]
    exact (LinearMap.posSemidef_toMatrix_iff B).mpr hApos
  have hmat_ne : mat ≠ 0 := by
    intro hzero
    apply hAne
    apply (LinearMap.toMatrix B.toBasis B.toBasis).injective
    simpa [mat] using hzero
  have htrace_nonneg : 0 ≤ mat.trace := hmat.trace_nonneg
  have htrace_ne : mat.trace ≠ 0 := by
    intro hzero
    exact hmat_ne (hmat.trace_eq_zero_iff.mp hzero)
  have htrace_pos : 0 < mat.trace := lt_of_le_of_ne' htrace_nonneg htrace_ne
  rw [LinearMap.trace_eq_matrix_trace Real B.toBasis A]
  exact htrace_pos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.trace_pos_of_isSymmetric_of_nonneg_of_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.trace_pos_of_isSymmetric_of_nonneg_of_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.trace_pos_of_isSymmetric_of_nonneg_of_ne_zero ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.trace_pos_of_isSymmetric_of_nonneg_of_ne_zero

theorem IsSymmetric.range_eq_orthogonal_ker
    {D : MetricFiberData V} {A : V →ₗ[Real] V} (hA : D.IsSymmetric A) :
    A.range = D.orthogonal A.ker := by
  let addV : AddCommGroup V := inferInstance
  let modV : Module Real V := inferInstance
  let : InnerProductSpace.Core Real V := D.toCore
  let : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real V _ addV modV D.toCore
  let : AddCommGroup V := addV
  let : Module Real V := modV
  let : InnerProductSpace Real V :=
    @InnerProductSpace.ofCore Real V _ _ _ D.toCore.toCore
  have hInner (v w : V) : (Inner.inner Real v w : Real) = D.inner v w := by
    exact D.toCore_inner v w
  have hSymmetric : A.IsSymmetric := by
    intro v w
    change D.inner (A v) w = D.inner v (A w)
    exact hA v w
  have hOrthogonal : D.orthogonal A.ker = Submodule.orthogonal A.ker := by
    ext v
    simp only [mem_orthogonal, Submodule.mem_orthogonal]
    constructor
    · intro hv w hw
      rw [hInner]
      exact hv w hw
    · intro hv w hw
      rw [← hInner]
      exact hv w hw
  rw [hOrthogonal, ← hSymmetric.orthogonal_range]
  exact A.range.orthogonal_orthogonal.symm

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.IsSymmetric
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.IsSymmetric.range_eq_orthogonal_ker then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.IsSymmetric.range_eq_orthogonal_ker"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.IsSymmetric.range_eq_orthogonal_ker ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.IsSymmetric.range_eq_orthogonal_ker

variable {W : Type*} [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]

theorem map_orthogonal_of_inner_eq
    (DV : MetricFiberData V) (DW : MetricFiberData W)
    (e : V ≃ₗ[Real] W)
    (hinner : ∀ v w, DW.inner (e v) (e w) = DV.inner v w)
    (K : Submodule Real V) :
    Submodule.map e.toLinearMap (DV.orthogonal K) =
      DW.orthogonal (Submodule.map e.toLinearMap K) := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [mem_orthogonal]
    rintro _ ⟨u, hu, rfl⟩
    change DW.inner (e u) (e v) = 0
    rw [hinner]
    exact (mem_orthogonal DV K v).mp hv u hu
  · intro hw
    refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    change e.symm w ∈ DV.orthogonal K
    rw [mem_orthogonal]
    intro u hu
    have hw' := (mem_orthogonal DW (Submodule.map e.toLinearMap K) w).mp hw
      (e u) ⟨u, hu, rfl⟩
    calc
      DV.inner u (e.symm w) = DW.inner (e u) (e (e.symm w)) :=
        (hinner u (e.symm w)).symm
      _ = DW.inner (e u) w := by rw [e.apply_symm_apply]
      _ = 0 := hw'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.map_orthogonal_of_inner_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.map_orthogonal_of_inner_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.map_orthogonal_of_inner_eq ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.map_orthogonal_of_inner_eq

noncomputable def submoduleProjection
    (D : MetricFiberData V) (W : Submodule Real V) : V →ₗ[Real] W := by
  let addV : AddCommGroup V := inferInstance
  let modV : Module Real V := inferInstance
  letI : InnerProductSpace.Core Real V := D.toCore
  letI : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real V _ addV modV D.toCore
  letI : AddCommGroup V := addV
  letI : Module Real V := modV
  letI : InnerProductSpace Real V :=
    @InnerProductSpace.ofCore Real V _ _ _ D.toCore.toCore
  exact W.orthogonalProjectionOnto.toLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.submoduleProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.submoduleProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.submoduleProjection ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.submoduleProjection

theorem submoduleProjection_inner
    (D : MetricFiberData V) (W : Submodule Real V) (v : V) (w : W) :
    D.inner (submoduleProjection D W v : V) w = D.inner v w := by
  let addV : AddCommGroup V := inferInstance
  let modV : Module Real V := inferInstance
  let : InnerProductSpace.Core Real V := D.toCore
  let : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real V _ addV modV D.toCore
  let : AddCommGroup V := addV
  let : Module Real V := modV
  let : InnerProductSpace Real V :=
    @InnerProductSpace.ofCore Real V _ _ _ D.toCore.toCore
  change Inner.inner Real (W.orthogonalProjectionOnto v : V) w = Inner.inner Real v w
  exact W.inner_orthogonalProjectionOnto_eq_of_mem_right w v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.submoduleProjection_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.submoduleProjection_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.submoduleProjection_inner ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.submoduleProjection_inner

@[simp]
theorem submoduleProjection_eq_self
    (D : MetricFiberData V) (W : Submodule Real V) (v : V) (hv : v ∈ W) :
    submoduleProjection D W v = ⟨v, hv⟩ := by
  let addV : AddCommGroup V := inferInstance
  let modV : Module Real V := inferInstance
  let : InnerProductSpace.Core Real V := D.toCore
  let : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real V _ addV modV D.toCore
  let : AddCommGroup V := addV
  let : Module Real V := modV
  let : InnerProductSpace Real V :=
    @InnerProductSpace.ofCore Real V _ _ _ D.toCore.toCore
  let w : W := ⟨v, hv⟩
  simpa [submoduleProjection, w] using W.orthogonalProjectionOnto_mem_subspace_eq_self w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.submoduleProjection_eq_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.submoduleProjection_eq_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.submoduleProjection_eq_self ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.submoduleProjection_eq_self

theorem submoduleProjection_inner_self_le
    (D : MetricFiberData V) (W : Submodule Real V) (v : V) :
    D.inner (submoduleProjection D W v : V) (submoduleProjection D W v : V) ≤
      D.inner v v := by
  let addV : AddCommGroup V := inferInstance
  let modV : Module Real V := inferInstance
  let : InnerProductSpace.Core Real V := D.toCore
  let : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real V _ addV modV D.toCore
  let : AddCommGroup V := addV
  let : Module Real V := modV
  let : InnerProductSpace Real V :=
    @InnerProductSpace.ofCore Real V _ _ _ D.toCore.toCore
  change Inner.inner Real (W.orthogonalProjectionOnto v : V) (W.orthogonalProjectionOnto v : V) ≤
    Inner.inner Real v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have hnorm : ‖(W.orthogonalProjectionOnto v : V)‖ ≤ ‖v‖ := by
    simpa using W.norm_orthogonalProjectionOnto_apply_le v
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.submoduleProjection_inner_self_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.submoduleProjection_inner_self_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.submoduleProjection_inner_self_le ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.submoduleProjection_inner_self_le

theorem exists_metric_linearEquiv
    (DV : MetricFiberData V) (DW : MetricFiberData W)
    (hfin : Module.finrank ℝ V = Module.finrank ℝ W) :
    ∃ e : V ≃ₗ[ℝ] W, ∀ v w, DW.inner (e v) (e w) = DV.inner v w := by
  let addV : AddCommGroup V := inferInstance
  let modV : Module Real V := inferInstance
  let addW : AddCommGroup W := inferInstance
  let modW : Module Real W := inferInstance
  let : InnerProductSpace.Core Real V := DV.toCore
  let : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real V _ addV modV DV.toCore
  let : AddCommGroup V := addV
  let : Module Real V := modV
  let : InnerProductSpace Real V :=
    @InnerProductSpace.ofCore Real V _ _ _ DV.toCore.toCore
  let : InnerProductSpace.Core Real W := DW.toCore
  let : NormedAddCommGroup W :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real W _ addW modW DW.toCore
  let : AddCommGroup W := addW
  let : Module Real W := modW
  let : InnerProductSpace Real W :=
    @InnerProductSpace.ofCore Real W _ _ _ DW.toCore.toCore
  let bV := stdOrthonormalBasis Real V
  let bW := stdOrthonormalBasis Real W
  let e : V ≃ₗᵢ[Real] W := bV.equiv bW (finCongr hfin)
  refine ⟨e.toLinearEquiv, ?_⟩
  intro v w
  change Inner.inner Real (e v) (e w) = Inner.inner Real v w
  exact e.inner_map_map v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.exists_metric_linearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.exists_metric_linearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.exists_metric_linearEquiv ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.exists_metric_linearEquiv

section MetricEquiv

variable {V' W' : Type*}
  [NormedAddCommGroup V'] [NormedSpace Real V'] [FiniteDimensional Real V']
  [NormedAddCommGroup W'] [NormedSpace Real W'] [FiniteDimensional Real W']

theorem exists_metric_cle
    (DV : MetricFiberData V') (DW : MetricFiberData W')
    (hfin : Module.finrank Real V' = Module.finrank Real W') :
    ∃ e : V' ≃L[Real] W',
      ∀ v w, DW.inner (e v) (e w) = DV.inner v w := by
  classical
  obtain ⟨e, he⟩ := exists_metric_linearEquiv DV DW hfin
  exact ⟨e.toContinuousLinearEquiv, he⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.exists_metric_cle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.exists_metric_cle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.exists_metric_cle ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.exists_metric_cle

end MetricEquiv

def adjoint (DV : MetricFiberData V) (DW : MetricFiberData W)
    (A : V →ₗ[Real] W) : W →ₗ[Real] V :=
  DV.flat.symm.toLinearMap.comp
    (A.dualMap.comp DW.flat.toLinearMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.adjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.adjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.adjoint ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.adjoint

theorem adjoint_inner
    (DV : MetricFiberData V) (DW : MetricFiberData W)
    (A : V →ₗ[Real] W) (y : W) (x : V) :
    DV.inner (adjoint DV DW A y) x = DW.inner y (A x) := by
  unfold inner adjoint
  change
    DV.flat (DV.flat.symm
        ((A.dualMap.comp DW.flat.toLinearMap) y)) x =
      DW.flat y (A x)
  rw [DV.flat.apply_symm_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.adjoint_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.adjoint_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.adjoint_inner ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.adjoint_inner

section InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

def ofInnerProductSpace : MetricFiberData F :=
  ofFlat
    { toFun := fun v => (innerSL ℝ v).toLinearMap
      map_add' := by
        intro v w
        ext z
        exact inner_add_left v w z
      map_smul' := by
        intro c v
        ext z
        exact real_inner_smul_left v z c }
    (by
      intro v w h
      apply ext_inner_right ℝ
      intro z
      exact congrArg (fun f : Module.Dual ℝ F => f z) h)
    (fun v w => (real_inner_comm v w).symm)
    (fun v => real_inner_self_nonneg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.ofInnerProductSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.ofInnerProductSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.ofInnerProductSpace ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.ofInnerProductSpace

@[simp] theorem ofInnerProductSpace_inner (v w : F) :
    (ofInnerProductSpace (F := F)).inner v w = Inner.inner ℝ v w := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.MetricFiberData.ofInnerProductSpace_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.MetricFiberData.ofInnerProductSpace_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.MetricFiberData.ofInnerProductSpace_inner ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.ofInnerProductSpace_inner

end InnerProductSpace

end MetricFiberData

end

end DifferentialGeometry.Tensor0SBundle
