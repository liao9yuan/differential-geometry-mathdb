import Submission.DifferentialGeometry.Analysis.ODE.Gronwall.SecondOrder
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry

open _root_.Set
open scoped _root_.NNReal

namespace PhaseFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def phaseField (a : E × E → E) (z : E × E) : E × E :=
  (z.2, a z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PhaseFlow.phaseField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PhaseFlow.phaseField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PhaseFlow.phaseField ``Submission.DifferentialGeometry.PhaseFlow.phaseField


def freeEnd : (E × E) →L[ℝ] E :=
  ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PhaseFlow.freeEnd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PhaseFlow.freeEnd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PhaseFlow.freeEnd ``Submission.DifferentialGeometry.PhaseFlow.freeEnd


def freeDiag : (E × E) →L[ℝ] E × E :=
  (ContinuousLinearMap.fst ℝ E E).prod freeEnd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PhaseFlow.freeDiag then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PhaseFlow.freeDiag"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PhaseFlow.freeDiag ``Submission.DifferentialGeometry.PhaseFlow.freeDiag


def freeDiagCLE : (E × E) ≃L[ℝ] (E × E) :=
  ContinuousLinearEquiv.equivOfInverse freeDiag
    ((ContinuousLinearMap.fst ℝ E E).prod
      (ContinuousLinearMap.snd ℝ E E - ContinuousLinearMap.fst ℝ E E))
    (by intro z; simp [freeDiag, freeEnd])
    (by intro z; simp [freeDiag, freeEnd])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PhaseFlow.freeDiagCLE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PhaseFlow.freeDiagCLE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PhaseFlow.freeDiagCLE ``Submission.DifferentialGeometry.PhaseFlow.freeDiagCLE

@[simp]
theorem freeDiag_apply (z : E × E) : freeDiag z = (z.1, z.1 + z.2) := by
  simp [freeDiag, freeEnd]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PhaseFlow.freeDiag_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PhaseFlow.freeDiag_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PhaseFlow.freeDiag_apply ``Submission.DifferentialGeometry.PhaseFlow.freeDiag_apply

@[simp]
theorem freeDiagCLE_apply (z : E × E) : freeDiagCLE z = (z.1, z.1 + z.2) := by
  simp [freeDiagCLE, freeDiag, freeEnd]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PhaseFlow.freeDiagCLE_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PhaseFlow.freeDiagCLE_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PhaseFlow.freeDiagCLE_apply ``Submission.DifferentialGeometry.PhaseFlow.freeDiagCLE_apply

@[simp]
theorem freeDiagInv_apply (z : E × E) :
    (freeDiagCLE (E := E)).symm z = (z.1, z.2 - z.1) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PhaseFlow.freeDiagInv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PhaseFlow.freeDiagInv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PhaseFlow.freeDiagInv_apply ``Submission.DifferentialGeometry.PhaseFlow.freeDiagInv_apply


theorem freeDiagCLE_coe :
    (freeDiagCLE (E := E) : (E × E) →L[ℝ] (E × E)) = freeDiag := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PhaseFlow.freeDiagCLE_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PhaseFlow.freeDiagCLE_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PhaseFlow.freeDiagCLE_coe ``Submission.DifferentialGeometry.PhaseFlow.freeDiagCLE_coe

noncomputable def phaseErr (κ : ℝ≥0) : ℝ≥0 where
  val := (κ : ℝ) * Real.exp (1 + (κ : ℝ)) * (Real.exp 1 - 1)
  property := by
    exact mul_nonneg
      (mul_nonneg κ.coe_nonneg (Real.exp_pos _).le)
      (sub_nonneg.mpr (Real.one_le_exp zero_le_one))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PhaseFlow.phaseErr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PhaseFlow.phaseErr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PhaseFlow.phaseErr ``Submission.DifferentialGeometry.PhaseFlow.phaseErr

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem phaseErr_mono {κ κ' : ℝ≥0} (hle : κ ≤ κ') :
    phaseErr κ ≤ phaseErr κ' := by
  apply NNReal.coe_le_coe.mp
  have hle' : (κ : ℝ) ≤ (κ' : ℝ) := by exact_mod_cast hle
  have hexp : Real.exp (1 + (κ : ℝ)) ≤ Real.exp (1 + (κ' : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  dsimp only [phaseErr]
  refine mul_le_mul_of_nonneg_right ?_
    (sub_nonneg.mpr (Real.one_le_exp zero_le_one))
  calc
    (κ : ℝ) * Real.exp (1 + (κ : ℝ)) ≤
        (κ' : ℝ) * Real.exp (1 + (κ : ℝ)) :=
      mul_le_mul_of_nonneg_right hle' (Real.exp_pos _).le
    _ ≤ (κ' : ℝ) * Real.exp (1 + (κ' : ℝ)) :=
      mul_le_mul_of_nonneg_left hexp κ'.coe_nonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PhaseFlow.phaseErr_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PhaseFlow.phaseErr_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PhaseFlow.phaseErr_mono ``Submission.DifferentialGeometry.PhaseFlow.phaseErr_mono

omit [NormedSpace ℝ E] in
theorem phaseField_lip
    {a : E × E → E} {s : Set (E × E)} {κ : ℝ≥0}
    (ha : LipschitzOnWith κ a s) :
    LipschitzOnWith (_root_.Max.max 1 κ) (phaseField a) s := by
  change LipschitzOnWith (_root_.Max.max 1 κ) (fun x => (x.2, a x)) s
  exact LipschitzWith.prod_snd.lipschitzOnWith.prodMk ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PhaseFlow.phaseField_lip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PhaseFlow.phaseField_lip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PhaseFlow.phaseField_lip ``Submission.DifferentialGeometry.PhaseFlow.phaseField_lip

theorem phase_pos_res_le
    {a : E × E → E} {s : Set (E × E)} {κ : ℝ≥0}
    {Z W : ℝ → E × E}
    (ha : LipschitzOnWith κ a s)
    (hZc : ContinuousOn Z (_root_.Set.Icc 0 1))
    (hWc : ContinuousOn W (_root_.Set.Icc 0 1))
    (hZd : ∀ t ∈ _root_.Set.Ico 0 1,
      HasDerivWithinAt Z (phaseField a (Z t)) (_root_.Set.Ici t) t)
    (hWd : ∀ t ∈ _root_.Set.Ico 0 1,
      HasDerivWithinAt W (phaseField a (W t)) (_root_.Set.Ici t) t)
    (hZs : ∀ t ∈ _root_.Set.Ico 0 1, Z t ∈ s)
    (hWs : ∀ t ∈ _root_.Set.Ico 0 1, W t ∈ s) :
    ‖(Z 1).1 - (W 1).1 -
        ((Z 0).1 - (W 0).1 + ((Z 0).2 - (W 0).2))‖ ≤
      (phaseErr κ : ℝ) * _root_.Dist.dist (Z 0) (W 0) := by
  let K : ℝ≥0 := _root_.Max.max 1 κ
  have hphase_dist : ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1,
      dist (Z t) (W t) ≤ _root_.Dist.dist (Z 0) (W 0) * Real.exp ((K : ℝ) * (t - 0)) :=
    dist_le_of_trajectories_ODE_of_mem
      (v := fun _ => phaseField a) (s := fun _ => s) (K := K)
      (f := Z) (g := W) (a := 0) (b := 1)
      (δ := _root_.Dist.dist (Z 0) (W 0))
      (fun _ _ => phaseField_lip ha) hZc hZd hZs hWc hWd hWs le_rfl
  have hK_le : (K : ℝ) ≤ 1 + (κ : ℝ) := by
    dsimp [K]
    rw [NNReal.coe_max]
    apply max_le
    · calc
        ((1 : ℝ≥0) : ℝ) = 1 := rfl
        _ ≤ 1 + (κ : ℝ) := le_add_of_nonneg_right κ.coe_nonneg
    · calc
        (κ : ℝ) ≤ (κ : ℝ) + 1 := le_add_of_nonneg_right zero_le_one
        _ = 1 + (κ : ℝ) := add_comm _ _
  let eps : ℝ :=
    (κ : ℝ) * Real.exp (1 + (κ : ℝ)) * _root_.Dist.dist (Z 0) (W 0)
  have heps : 0 ≤ eps := by
    dsimp [eps]
    exact mul_nonneg
      (mul_nonneg κ.coe_nonneg (Real.exp_pos _).le)
      (dist_nonneg)
  have hacc : ∀ t ∈ _root_.Set.Ico (0 : ℝ) 1, ‖a (Z t) - a (W t)‖ ≤ eps := by
    intro t ht
    have htcc : t ∈ _root_.Set.Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    have hdist := hphase_dist t htcc
    have hKt : (K : ℝ) * (t - 0) ≤ 1 + (κ : ℝ) := by
      calc
        (K : ℝ) * (t - 0) ≤ (K : ℝ) * 1 := by
          apply mul_le_mul_of_nonneg_left
          · simpa only [sub_zero] using ht.2.le
          · exact K.coe_nonneg
        _ ≤ 1 + (κ : ℝ) := by simpa using hK_le
    have hexp : Real.exp ((K : ℝ) * (t - 0)) ≤
        Real.exp (1 + (κ : ℝ)) := Real.exp_le_exp.mpr hKt
    have hdist' : _root_.Dist.dist (Z t) (W t) ≤
        dist (Z 0) (W 0) * Real.exp (1 + (κ : ℝ)) := by
      exact hdist.trans (mul_le_mul_of_nonneg_left hexp dist_nonneg)
    calc
      ‖a (Z t) - a (W t)‖ = _root_.Dist.dist (a (Z t)) (a (W t)) := by
        rw [dist_eq_norm]
      _ ≤ (κ : ℝ) * _root_.Dist.dist (Z t) (W t) := ha.dist_le_mul _ (hZs t ht) _ (hWs t ht)
      _ ≤ (κ : ℝ) *
          (_root_.Dist.dist (Z 0) (W 0) * Real.exp (1 + (κ : ℝ))) :=
        mul_le_mul_of_nonneg_left hdist' κ.coe_nonneg
      _ = eps := by dsimp [eps]; ring
  let Y : ℝ → E := fun t => (Z t).1 - (W t).1
  let V : ℝ → E := fun t => (Z t).2 - (W t).2
  let A : ℝ → E := fun t => a (Z t) - a (W t)
  let R : ℝ → E := fun t => Y t - Y 0 - t • V 0
  let R' : ℝ → E := fun t => V t - V 0
  have hYc : ContinuousOn Y (_root_.Set.Icc (0 : ℝ) 1) := hZc.fst.sub hWc.fst
  have hVc : ContinuousOn V (_root_.Set.Icc (0 : ℝ) 1) := hZc.snd.sub hWc.snd
  have hYd : ∀ t ∈ _root_.Set.Ico (0 : ℝ) 1,
      HasDerivWithinAt Y (V t) (_root_.Set.Ici t) t := by
    intro t ht
    have hZfst : HasDerivWithinAt (fun x => (Z x).1) (Z t).2 (_root_.Set.Ici t) t := by
      simpa only [phaseField, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.toSpanSingleton_apply,
        one_smul] using
        ((hZd t ht).hasFDerivWithinAt.fst).hasDerivWithinAt
    have hWfst : HasDerivWithinAt (fun x => (W x).1) (W t).2 (_root_.Set.Ici t) t := by
      simpa only [phaseField, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.toSpanSingleton_apply,
        one_smul] using
        ((hWd t ht).hasFDerivWithinAt.fst).hasDerivWithinAt
    change HasDerivWithinAt ((fun x => (Z x).1) - fun x => (W x).1)
      ((Z t).2 - (W t).2) (_root_.Set.Ici t) t
    exact hZfst.sub hWfst
  have hVd : ∀ t ∈ _root_.Set.Ico (0 : ℝ) 1,
      HasDerivWithinAt V (A t) (_root_.Set.Ici t) t := by
    intro t ht
    have hZsnd : HasDerivWithinAt (fun x => (Z x).2) (a (Z t)) (_root_.Set.Ici t) t := by
      simpa only [phaseField, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_snd', ContinuousLinearMap.toSpanSingleton_apply,
        one_smul] using
        ((hZd t ht).hasFDerivWithinAt.snd).hasDerivWithinAt
    have hWsnd : HasDerivWithinAt (fun x => (W x).2) (a (W t)) (_root_.Set.Ici t) t := by
      simpa only [phaseField, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_snd', ContinuousLinearMap.toSpanSingleton_apply,
        one_smul] using
        ((hWd t ht).hasFDerivWithinAt.snd).hasDerivWithinAt
    change HasDerivWithinAt ((fun x => (Z x).2) - fun x => (W x).2)
      (a (Z t) - a (W t)) (_root_.Set.Ici t) t
    exact hZsnd.sub hWsnd
  have hlin : ∀ (t : ℝ) (u : Set ℝ),
      HasDerivWithinAt (fun x : ℝ => x • V 0) (V 0) u t := by
    intro t u
    simpa using (hasDerivWithinAt_id t u).smul_const (V 0)
  have hRc : ContinuousOn R (_root_.Set.Icc (0 : ℝ) 1) :=
    (hYc.sub continuousOn_const).sub
      ((continuous_id.smul continuous_const).continuousOn)
  have hR'c : ContinuousOn R' (_root_.Set.Icc (0 : ℝ) 1) := hVc.sub continuousOn_const
  have hRd : ∀ t ∈ _root_.Set.Ico (0 : ℝ) 1,
      HasDerivWithinAt R (R' t) (_root_.Set.Ici t) t := by
    intro t ht
    exact ((hYd t ht).sub_const (Y 0)).sub (hlin t (_root_.Set.Ici t))
  have hR'd : ∀ t ∈ _root_.Set.Ico (0 : ℝ) 1,
      HasDerivWithinAt R' (A t) (_root_.Set.Ici t) t := by
    intro t ht
    exact (hVd t ht).sub_const (V 0)
  have hbound : ∀ t ∈ _root_.Set.Ico (0 : ℝ) 1, ‖A t‖ ≤ 0 * ‖R t‖ + eps := by
    intro t ht
    simpa only [A, _root_.MulZeroClass.zero_mul, zero_add] using hacc t ht
  have hR0 : ‖R 0‖ ≤ 0 := by simp [R]
  have hR'0 : ‖R' 0‖ ≤ 0 := by simp [R']
  have hmain := norm_le_gronwall_secondOrder
    (Y := R) (Y' := R') (Y'' := A) (K := 0) (eps := eps)
    (δ := 0) (b := 1) le_rfl heps hRc hR'c hRd hR'd hbound hR0 hR'0
    1 ⟨zero_le_one, le_rfl⟩
  have hR1 : R 1 = (Z 1).1 - (W 1).1 -
      ((Z 0).1 - (W 0).1 + ((Z 0).2 - (W 0).2)) := by
    dsimp [R, Y, V]
    simp only [one_smul]
    abel
  rw [hR1] at hmain
  have hgb : gronwallBound 0 (_root_.Max.max (0 : ℝ) 1) eps 1 =
      (phaseErr κ : ℝ) * _root_.Dist.dist (Z 0) (W 0) := by
    rw [max_eq_right zero_le_one, gronwallBound_of_K_ne_0 one_ne_zero]
    simp only [_root_.MulZeroClass.zero_mul, zero_add, div_one, one_mul]
    rw [show (phaseErr κ : ℝ) =
      κ * Real.exp (1 + κ) * (Real.exp 1 - 1) from rfl]
    dsimp only [eps]
    ring
  rwa [hgb] at hmain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PhaseFlow.phase_pos_res_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PhaseFlow.phase_pos_res_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PhaseFlow.phase_pos_res_le ``Submission.DifferentialGeometry.PhaseFlow.phase_pos_res_le

theorem phase_pos_approx
    {a : E × E → E} {q u : Set (E × E)} {κ : ℝ≥0}
    {Φ : (E × E) → ℝ → E × E}
    (ha : LipschitzOnWith κ a q)
    (hinit : ∀ z ∈ u, Φ z 0 = z)
    (hcont : ∀ z ∈ u, ContinuousOn (Φ z) (_root_.Set.Icc 0 1))
    (hderiv : ∀ z ∈ u, ∀ t ∈ _root_.Set.Ico 0 1,
      HasDerivWithinAt (Φ z) (phaseField a (Φ z t)) (_root_.Set.Ici t) t)
    (hmem : ∀ z ∈ u, ∀ t ∈ _root_.Set.Ico 0 1, Φ z t ∈ q) :
    ApproximatesLinearOn (fun z => (Φ z 1).1) freeEnd u (phaseErr κ) := by
  intro x hx y hy
  have hres := phase_pos_res_le ha (hcont x hx) (hcont y hy)
    (hderiv x hx) (hderiv y hy) (hmem x hx) (hmem y hy)
  rw [hinit x hx, hinit y hy] at hres
  simpa only [freeEnd, add_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    Prod.fst_sub, Prod.snd_sub, dist_eq_norm] using hres

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PhaseFlow.phase_pos_approx then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PhaseFlow.phase_pos_approx"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PhaseFlow.phase_pos_approx ``Submission.DifferentialGeometry.PhaseFlow.phase_pos_approx

theorem phase_diag_approx
    {a : E × E → E} {q u : Set (E × E)} {κ : ℝ≥0}
    {Φ : (E × E) → ℝ → E × E}
    (ha : LipschitzOnWith κ a q)
    (hinit : ∀ z ∈ u, Φ z 0 = z)
    (hcont : ∀ z ∈ u, ContinuousOn (Φ z) (_root_.Set.Icc 0 1))
    (hderiv : ∀ z ∈ u, ∀ t ∈ _root_.Set.Ico 0 1,
      HasDerivWithinAt (Φ z) (phaseField a (Φ z t)) (_root_.Set.Ici t) t)
    (hmem : ∀ z ∈ u, ∀ t ∈ _root_.Set.Ico 0 1, Φ z t ∈ q) :
    ApproximatesLinearOn (fun z ↦ (z.1, (Φ z 1).1)) freeDiag u (phaseErr κ) := by
  intro x hx y hy
  have hpos := phase_pos_approx ha hinit hcont hderiv hmem x hx y hy
  simpa only [freeDiag_apply, freeEnd, add_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    Prod.fst_sub, Prod.snd_sub, Prod.norm_def, sub_self, norm_zero,
    max_eq_right (norm_nonneg _)] using hpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PhaseFlow.phase_diag_approx then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PhaseFlow.phase_diag_approx"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PhaseFlow.phase_diag_approx ``Submission.DifferentialGeometry.PhaseFlow.phase_diag_approx

end PhaseFlow

end DifferentialGeometry
