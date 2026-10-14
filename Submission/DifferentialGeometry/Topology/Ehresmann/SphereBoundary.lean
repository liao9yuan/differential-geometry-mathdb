import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.Instances.Icc

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open scoped _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Topology.Ehresmann

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {HF : Type*} [TopologicalSpace HF]
variable {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
variable {IF : ModelWithCorners ℝ E HF}

def isotopyTrackDiffeomorph
    (A Ainv : Set.Icc (0 : ℝ) 1 → F → F)
    (hleft : ∀ t x, Ainv t (A t x) = x)
    (hright : ∀ t x, A t (Ainv t x) = x)
    (hA : ContMDiff (IF.prod (𝓡∂ 1)) IF
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun p : F × Set.Icc (0 : ℝ) 1 ↦ A p.2 p.1))
    (hAinv : ContMDiff (IF.prod (𝓡∂ 1)) IF
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun p : F × Set.Icc (0 : ℝ) 1 ↦ Ainv p.2 p.1)) :
    Diffeomorph (IF.prod (𝓡∂ 1)) (IF.prod (𝓡∂ 1))
      (F × Set.Icc (0 : ℝ) 1) (F × Set.Icc (0 : ℝ) 1)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) where
  toEquiv :=
    { toFun := fun p ↦ (A p.2 p.1, p.2)
      invFun := fun p ↦ (Ainv p.2 p.1, p.2)
      left_inv := by
        intro p
        exact Prod.ext (hleft p.2 p.1) rfl
      right_inv := by
        intro p
        exact Prod.ext (hright p.2 p.1) rfl }
  contMDiff_toFun :=
    hA.prodMk (contMDiff_snd (I := IF) (J := 𝓡∂ 1)
      (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)))
  contMDiff_invFun :=
    hAinv.prodMk (contMDiff_snd (I := IF) (J := 𝓡∂ 1)
      (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Ehresmann.isotopyTrackDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Ehresmann.isotopyTrackDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Ehresmann.isotopyTrackDiffeomorph ``Submission.DifferentialGeometry.Topology.Ehresmann.isotopyTrackDiffeomorph

@[simp]
theorem isotopyTrackDiffeomorph_apply
    (A Ainv : Set.Icc (0 : ℝ) 1 → F → F)
    (hleft : ∀ t x, Ainv t (A t x) = x)
    (hright : ∀ t x, A t (Ainv t x) = x)
    (hA : ContMDiff (IF.prod (𝓡∂ 1)) IF
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun p : F × Set.Icc (0 : ℝ) 1 ↦ A p.2 p.1))
    (hAinv : ContMDiff (IF.prod (𝓡∂ 1)) IF
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun p : F × Set.Icc (0 : ℝ) 1 ↦ Ainv p.2 p.1))
    (p : F × Set.Icc (0 : ℝ) 1) :
    isotopyTrackDiffeomorph A Ainv hleft hright hA hAinv p = (A p.2 p.1, p.2) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Ehresmann.isotopyTrackDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Ehresmann.isotopyTrackDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Ehresmann.isotopyTrackDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.Ehresmann.isotopyTrackDiffeomorph_apply

@[simp]
theorem isotopyTrackDiffeomorph_symm_apply
    (A Ainv : Set.Icc (0 : ℝ) 1 → F → F)
    (hleft : ∀ t x, Ainv t (A t x) = x)
    (hright : ∀ t x, A t (Ainv t x) = x)
    (hA : ContMDiff (IF.prod (𝓡∂ 1)) IF
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun p : F × Set.Icc (0 : ℝ) 1 ↦ A p.2 p.1))
    (hAinv : ContMDiff (IF.prod (𝓡∂ 1)) IF
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun p : F × Set.Icc (0 : ℝ) 1 ↦ Ainv p.2 p.1))
    (p : F × Set.Icc (0 : ℝ) 1) :
    (isotopyTrackDiffeomorph A Ainv hleft hright hA hAinv).symm p =
      (Ainv p.2 p.1, p.2) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Ehresmann.isotopyTrackDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Ehresmann.isotopyTrackDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Ehresmann.isotopyTrackDiffeomorph_symm_apply ``Submission.DifferentialGeometry.Topology.Ehresmann.isotopyTrackDiffeomorph_symm_apply

def endpointCorrectedProduct
    {EW : Type*} [NormedAddCommGroup EW] [NormedSpace ℝ EW]
    {HW : Type*} [TopologicalSpace HW]
    {W : Type*} [TopologicalSpace W] [ChartedSpace HW W]
    {IW : ModelWithCorners ℝ EW HW}
    (Hprod : Diffeomorph (IF.prod (𝓡∂ 1)) IW
      (F × Set.Icc (0 : ℝ) 1) W (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    (A Ainv : Set.Icc (0 : ℝ) 1 → F → F)
    (hleft : ∀ t x, Ainv t (A t x) = x)
    (hright : ∀ t x, A t (Ainv t x) = x)
    (hA : ContMDiff (IF.prod (𝓡∂ 1)) IF
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun p : F × Set.Icc (0 : ℝ) 1 ↦ A p.2 p.1))
    (hAinv : ContMDiff (IF.prod (𝓡∂ 1)) IF
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun p : F × Set.Icc (0 : ℝ) 1 ↦ Ainv p.2 p.1)) :
    Diffeomorph (IF.prod (𝓡∂ 1)) IW (F × Set.Icc (0 : ℝ) 1) W
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) :=
  (isotopyTrackDiffeomorph A Ainv hleft hright hA hAinv).trans Hprod

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Ehresmann.endpointCorrectedProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Ehresmann.endpointCorrectedProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Ehresmann.endpointCorrectedProduct ``Submission.DifferentialGeometry.Topology.Ehresmann.endpointCorrectedProduct

theorem endpointCorrectedProduct_lower
    {EW : Type*} [NormedAddCommGroup EW] [NormedSpace ℝ EW]
    {HW : Type*} [TopologicalSpace HW]
    {W : Type*} [TopologicalSpace W] [ChartedSpace HW W]
    {IW : ModelWithCorners ℝ EW HW}
    (Hprod : Diffeomorph (IF.prod (𝓡∂ 1)) IW
      (F × Set.Icc (0 : ℝ) 1) W (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    (A Ainv : Set.Icc (0 : ℝ) 1 → F → F)
    (hleft : ∀ t x, Ainv t (A t x) = x)
    (hright : ∀ t x, A t (Ainv t x) = x)
    (hA : ContMDiff (IF.prod (𝓡∂ 1)) IF
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun p : F × Set.Icc (0 : ℝ) 1 ↦ A p.2 p.1))
    (hAinv : ContMDiff (IF.prod (𝓡∂ 1)) IF
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun p : F × Set.Icc (0 : ℝ) 1 ↦ Ainv p.2 p.1))
    (hzero : ∀ x, A ⟨0, by norm_num⟩ x = x)
    (x : F) :
    endpointCorrectedProduct Hprod A Ainv hleft hright hA hAinv
      (x, ⟨0, by norm_num⟩) = Hprod (x, ⟨0, by norm_num⟩) := by
  change Hprod (A ⟨0, by norm_num⟩ x, ⟨0, by norm_num⟩) = _
  rw [hzero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Ehresmann.endpointCorrectedProduct_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Ehresmann.endpointCorrectedProduct_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Ehresmann.endpointCorrectedProduct_lower ``Submission.DifferentialGeometry.Topology.Ehresmann.endpointCorrectedProduct_lower

theorem endpointCorrectedProduct_upper
    {EW : Type*} [NormedAddCommGroup EW] [NormedSpace ℝ EW]
    {HW : Type*} [TopologicalSpace HW]
    {W : Type*} [TopologicalSpace W] [ChartedSpace HW W]
    {IW : ModelWithCorners ℝ EW HW}
    (Hprod : Diffeomorph (IF.prod (𝓡∂ 1)) IW
      (F × Set.Icc (0 : ℝ) 1) W (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    (A Ainv : Set.Icc (0 : ℝ) 1 → F → F)
    (hleft : ∀ t x, Ainv t (A t x) = x)
    (hright : ∀ t x, A t (Ainv t x) = x)
    (hA : ContMDiff (IF.prod (𝓡∂ 1)) IF
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun p : F × Set.Icc (0 : ℝ) 1 ↦ A p.2 p.1))
    (hAinv : ContMDiff (IF.prod (𝓡∂ 1)) IF
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun p : F × Set.Icc (0 : ℝ) 1 ↦ Ainv p.2 p.1))
    (x : F) :
    endpointCorrectedProduct Hprod A Ainv hleft hright hA hAinv
      (x, ⟨1, by norm_num⟩) = Hprod (A ⟨1, by norm_num⟩ x, ⟨1, by norm_num⟩) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Ehresmann.endpointCorrectedProduct_upper then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Ehresmann.endpointCorrectedProduct_upper"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Ehresmann.endpointCorrectedProduct_upper ``Submission.DifferentialGeometry.Topology.Ehresmann.endpointCorrectedProduct_upper

theorem isotopyTrackDiffeomorph_identity :
    isotopyTrackDiffeomorph
      (fun (_ : Set.Icc (0 : ℝ) 1) (x : F) ↦ x)
      (fun (_ : Set.Icc (0 : ℝ) 1) (x : F) ↦ x)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (contMDiff_fst (I := IF) (J := 𝓡∂ 1)
        (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)))
      (contMDiff_fst (I := IF) (J := 𝓡∂ 1)
        (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))) =
    Diffeomorph.refl (IF.prod (𝓡∂ 1)) (F × Set.Icc (0 : ℝ) 1)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
  apply Diffeomorph.ext
  intro p
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Ehresmann.isotopyTrackDiffeomorph_identity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Ehresmann.isotopyTrackDiffeomorph_identity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Ehresmann.isotopyTrackDiffeomorph_identity ``Submission.DifferentialGeometry.Topology.Ehresmann.isotopyTrackDiffeomorph_identity

private def flattenParameter (t : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition (3 * t.1 - 1), Real.smoothTransition.nonneg _,
    Real.smoothTransition.le_one _⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Ehresmann.flattenParameter
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Ehresmann.flattenParameter target :: scope.openDecls } }

private theorem contMDiff_flattenParameter :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ flattenParameter := by
  have hreal : ContDiff ℝ ∞ (fun t : ℝ ↦ Real.smoothTransition (3 * t - 1)) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  have h : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞
      (fun t : Set.Icc (0 : ℝ) 1 ↦ Real.smoothTransition (3 * t.1 - 1)) :=
    hreal.contMDiff.comp contMDiff_subtypeVal_Icc
  apply contMDiff_iff_comp_subtypeVal_Icc.mpr
  exact ⟨h.continuous.subtype_mk _, h⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Ehresmann.contMDiff_flattenParameter
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Ehresmann.contMDiff_flattenParameter target :: scope.openDecls } }

private theorem flattenParameter_lower (t : Set.Icc (0 : ℝ) 1) (ht : t.1 ≤ 1 / 3) :
    flattenParameter t = ⟨0, by norm_num⟩ := by
  apply Subtype.ext
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Ehresmann.flattenParameter_lower
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Ehresmann.flattenParameter_lower target :: scope.openDecls } }

private theorem flattenParameter_upper (t : Set.Icc (0 : ℝ) 1) (ht : 2 / 3 ≤ t.1) :
    flattenParameter t = ⟨1, by norm_num⟩ := by
  apply Subtype.ext
  exact Real.smoothTransition.one_of_one_le (by linarith)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Ehresmann.flattenParameter_upper
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Ehresmann.flattenParameter_upper target :: scope.openDecls } }

theorem exists_endpoint_flat_corrected_product
    {EW : Type*} [NormedAddCommGroup EW] [NormedSpace ℝ EW]
    {HW : Type*} [TopologicalSpace HW]
    {W : Type*} [TopologicalSpace W] [ChartedSpace HW W]
    {IW : ModelWithCorners ℝ EW HW}
    (Hprod : Diffeomorph (IF.prod (𝓡∂ 1)) IW (F × Set.Icc (0 : ℝ) 1) W ∞)
    (A Ainv : Set.Icc (0 : ℝ) 1 → F → F)
    (hleft : ∀ t x, Ainv t (A t x) = x)
    (hright : ∀ t x, A t (Ainv t x) = x)
    (hA : ContMDiff (IF.prod (𝓡∂ 1)) IF ∞
      (fun p : F × Set.Icc (0 : ℝ) 1 ↦ A p.2 p.1))
    (hAinv : ContMDiff (IF.prod (𝓡∂ 1)) IF ∞
      (fun p : F × Set.Icc (0 : ℝ) 1 ↦ Ainv p.2 p.1))
    (hzero : ∀ x, A ⟨0, by norm_num⟩ x = x) :
    ∃ Ψ : Diffeomorph (IF.prod (𝓡∂ 1)) IW (F × Set.Icc (0 : ℝ) 1) W ∞,
      (∀ p, (Hprod.symm (Ψ p)).2 = p.2) ∧
      (∀ t : Set.Icc (0 : ℝ) 1, t.1 ≤ 1 / 3 → ∀ x, Ψ (x, t) = Hprod (x, t)) ∧
      ∀ t : Set.Icc (0 : ℝ) 1, 2 / 3 ≤ t.1 → ∀ x,
        Ψ (x, t) = Hprod (A ⟨1, by norm_num⟩ x, t) := by
  let B := fun t x ↦ A (flattenParameter t) x
  let Binv := fun t x ↦ Ainv (flattenParameter t) x
  have hB : ContMDiff (IF.prod (𝓡∂ 1)) IF ∞
      (fun p : F × Set.Icc (0 : ℝ) 1 ↦ B p.2 p.1) :=
    hA.comp (contMDiff_fst.prodMk (contMDiff_flattenParameter.comp contMDiff_snd))
  have hBinv : ContMDiff (IF.prod (𝓡∂ 1)) IF ∞
      (fun p : F × Set.Icc (0 : ℝ) 1 ↦ Binv p.2 p.1) :=
    hAinv.comp (contMDiff_fst.prodMk (contMDiff_flattenParameter.comp contMDiff_snd))
  let Ψ := endpointCorrectedProduct Hprod B Binv
    (fun t ↦ hleft (flattenParameter t)) (fun t ↦ hright (flattenParameter t)) hB hBinv
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · intro p
    change (Hprod.symm (Hprod (B p.2 p.1, p.2))).2 = p.2
    rw [Hprod.symm_apply_apply]
  · intro t ht x
    change Hprod (A (flattenParameter t) x, t) = Hprod (x, t)
    rw [flattenParameter_lower t ht, hzero]
  · intro t ht x
    change Hprod (A (flattenParameter t) x, t) = _
    rw [flattenParameter_upper t ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Ehresmann.exists_endpoint_flat_corrected_product then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Ehresmann.exists_endpoint_flat_corrected_product"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Ehresmann.exists_endpoint_flat_corrected_product ``Submission.DifferentialGeometry.Topology.Ehresmann.exists_endpoint_flat_corrected_product

end DifferentialGeometry.Topology.Ehresmann
