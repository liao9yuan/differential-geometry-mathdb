import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Multiplication
import Submission.DifferentialGeometry.Analysis.Integration.Lp.PiLp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1

variable {ι : Type*} [Fintype ι] {Z : ι → Type*}
  [∀ i, NormedAddCommGroup (Z i)] [∀ i, NormedSpace ℝ (Z i)] {T : ℝ}

private def piLpEquivAux
    (e : timeL2 (PiLp 2 Z) T ≃ₗᵢ[ℝ] PiLp 2 (fun i => timeL2 (Z i) T)) :
    timeH1 (PiLp 2 Z) T ≃ₗᵢ[ℝ] PiLp 2 (fun i => timeH1 (Z i) T) where
  toFun u := WithLp.toLp 2 (fun i => mk (u.initial i) (e u.deriv i))
  invFun v := mk (WithLp.toLp 2 (fun i => (v i).initial))
    (e.symm (WithLp.toLp 2 (fun i => (v i).deriv)))
  left_inv u := by
    apply ext
    · rfl
    · exact e.symm_apply_apply u.deriv
  right_inv v := by
    apply PiLp.ext
    intro i
    apply ext
    · rfl
    · change (e (e.symm (WithLp.toLp 2 (fun i => (v i).deriv)))) i = (v i).deriv
      rw [e.apply_symm_apply]
  map_add' u v := by
    apply PiLp.ext
    intro i
    apply ext
    · rfl
    · change e (u.deriv + v.deriv) i = (e u.deriv + e v.deriv) i
      rw [map_add]
  map_smul' c u := by
    apply PiLp.ext
    intro i
    apply ext
    · rfl
    · change e (c • u.deriv) i = (c • e u.deriv) i
      rw [map_smul]
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [norm_sq_eq]
    change (∑ i, (‖u.initial i‖ ^ 2 + ‖e u.deriv i‖ ^ 2)) =
      ‖u.initial‖ ^ 2 + ‖u.deriv‖ ^ 2
    rw [Finset.sum_add_distrib, ← PiLp.norm_sq_eq_of_L2, ← PiLp.norm_sq_eq_of_L2,
      e.norm_map]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquivAux
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquivAux target :: scope.openDecls } }

def piLpEquiv : timeH1 (PiLp 2 Z) T ≃ₗᵢ[ℝ] PiLp 2 (fun i => timeH1 (Z i) T) :=
  piLpEquivAux (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv

@[simp] theorem piLpEquiv_initial (u : timeH1 (PiLp 2 Z) T) (i : ι) :
    (piLpEquiv u i).initial = u.initial i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_initial ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_initial

@[simp] theorem piLpEquiv_deriv (u : timeH1 (PiLp 2 Z) T) (i : ι) :
    (piLpEquiv u i).deriv = Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) u.deriv i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_deriv ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_deriv

@[simp] theorem piLpEquiv_symm_initial (v : PiLp 2 (fun i => timeH1 (Z i) T)) :
    (piLpEquiv.symm v).initial = WithLp.toLp 2 (fun i => (v i).initial) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_symm_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_symm_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_symm_initial ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_symm_initial

@[simp] theorem piLpEquiv_symm_deriv (v : PiLp 2 (fun i => timeH1 (Z i) T)) :
    (piLpEquiv.symm v).deriv =
      (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).symm (WithLp.toLp 2 (fun i => (v i).deriv)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_symm_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_symm_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_symm_deriv ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_symm_deriv

theorem piLpEquiv_toFun [∀ i, CompleteSpace (Z i)]
    (u : timeH1 (PiLp 2 Z) T) (i : ι) {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) T) :
    (piLpEquiv u i).toFun t = u.toFun t i := by
  let L := PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) Z i
  obtain ⟨v, hv0, hvt, hvd⟩ := exists_timeH1_comp_clm L u
  have hinit : (piLpEquiv u i).initial = v.initial := by
    exact hv0.symm
  have hderiv : (piLpEquiv u i).deriv = v.deriv := by
    apply Lp.ext
    exact (Lp.piLpEquiv_apply (𝕜 := ℝ) (timeMeasure T) u.deriv i).trans hvd.symm
  rw [timeH1.ext hinit hderiv]
  exact hvt t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_toFun ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_toFun

theorem piLpEquiv_symm_toFun [∀ i, CompleteSpace (Z i)]
    (v : PiLp 2 (fun i => timeH1 (Z i) T)) {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) T) :
    (piLpEquiv.symm v).toFun t = WithLp.toLp 2 (fun i => (v i).toFun t) := by
  apply PiLp.ext
  intro i
  have h := piLpEquiv_toFun (piLpEquiv.symm v) i ht
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_symm_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_symm_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_symm_toFun ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_symm_toFun

theorem piLpEquiv_toFunL2 [∀ i, CompleteSpace (Z i)]
    (u : timeH1 (PiLp 2 Z) T) (i : ι) :
    (piLpEquiv u i).toFunL2 = Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) u.toFunL2 i := by
  apply Lp.ext
  filter_upwards [coeFn_ofContinuousOn (piLpEquiv u i).continuousOn_toFun,
    Lp.piLpEquiv_apply (𝕜 := ℝ) (timeMeasure T) u.toFunL2 i,
    coeFn_ofContinuousOn u.continuousOn_toFun,
    _root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with t h1 h2 h3 ht
  change (piLpEquiv u i).toFunL2 t = (piLpEquiv u i).toFun t at h1
  change u.toFunL2 t = u.toFun t at h3
  rw [h1, h2, h3]
  exact piLpEquiv_toFun u i ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_toFunL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_toFunL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_toFunL2 ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_toFunL2

theorem piLpEquiv_symm_toFunL2 [∀ i, CompleteSpace (Z i)]
    (v : PiLp 2 (fun i => timeH1 (Z i) T)) :
    (piLpEquiv.symm v).toFunL2 =
      (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).symm (WithLp.toLp 2 (fun i => (v i).toFunL2)) := by
  apply (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).injective
  apply PiLp.ext
  intro i
  rw [LinearIsometryEquiv.apply_symm_apply]
  have h := piLpEquiv_toFunL2 (piLpEquiv.symm v) i
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_symm_toFunL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_symm_toFunL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_symm_toFunL2 ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.piLpEquiv_symm_toFunL2

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1
