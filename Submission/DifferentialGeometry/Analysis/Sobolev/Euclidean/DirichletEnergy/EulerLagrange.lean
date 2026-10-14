import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.WeakLowerSemicontinuity
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter _root_.Submission.Filter _root_.Set
open scoped _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d] {Ω : Set (EuclideanSpace ℝ (Fin d))}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Y" => _root_.MeasureTheory.Lp E 2 (volume.restrict Ω)

omit [NeZero d] in
private theorem gradLpOfWitness_add_smul {u φ : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Ω)
    (hφ : DeGiorgi.MemW1pWitness 2 φ Ω) (t : ℝ) :
    DeGiorgi.gradLpOfWitness (hu.add (hφ.smul t)) =
      DeGiorgi.gradLpOfWitness hu + t • DeGiorgi.gradLpOfWitness hφ := by
  apply Lp.ext
  filter_upwards [(hu.add (hφ.smul t)).weakGrad_memLp.coeFn_toLp,
    hu.weakGrad_memLp.coeFn_toLp, hφ.weakGrad_memLp.coeFn_toLp,
    Lp.coeFn_add (DeGiorgi.gradLpOfWitness hu) (t • DeGiorgi.gradLpOfWitness hφ),
    Lp.coeFn_smul t (DeGiorgi.gradLpOfWitness hφ)] with x hx hu0 hφ0 ha hs
  rw [ha]
  simp only [Pi.add_apply]
  rw [hs]
  simp only [Pi.smul_apply]
  change (hu.add (hφ.smul t)).weakGrad_memLp.toLp _ x =
    hu.weakGrad_memLp.toLp _ x + t • hφ.weakGrad_memLp.toLp _ x
  rw [hx, hu0, hφ0]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.gradLpOfWitness_add_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.gradLpOfWitness_add_smul target :: scope.openDecls } }

omit [NeZero d] in
private theorem inner_eq_zero_of_norm_sq_min {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (U V : H)
    (hmin : ∀ t : ℝ, ‖U‖ ^ 2 ≤ ‖U + t • V‖ ^ 2) : _root_.Inner.inner ℝ U V = 0 := by
  let q (t : ℝ) := ‖U‖ ^ 2 + 2 * t * _root_.Inner.inner ℝ U V + t ^ 2 * ‖V‖ ^ 2
  have heq (t : ℝ) : ‖U + t • V‖ ^ 2 = q t := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs]
    dsimp only [q]
    nlinarith [sq_abs t]
  have hloc : IsLocalMin q 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa only [q, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero]
      using (hmin t).trans_eq (heq t)
  have hderiv : HasDerivAt q (2 * _root_.Inner.inner ℝ U V) 0 := by
    convert ((hasDerivAt_const (0 : ℝ) (‖U‖ ^ 2)).add
      (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (_root_.Inner.inner ℝ U V))).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (‖V‖ ^ 2)) using 1 <;> norm_num [q] <;> rfl
  have hz := hloc.hasDerivAt_eq_zero hderiv
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.inner_eq_zero_of_norm_sq_min
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.inner_eq_zero_of_norm_sq_min target :: scope.openDecls } }

theorem integral_inner_weakGrad_smoothGrad_eq_zero_of_minimizer
    (hΩ : IsOpen Ω) {u b : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Ω)
    (hu0 : DeGiorgi.MemW01p 2 (fun x => u x - b x) Ω)
    (hmin : ∀ (v : E → ℝ), DeGiorgi.MemW01p 2 (fun x => v x - b x) Ω →
      ∀ hv : DeGiorgi.MemW1pWitness 2 v Ω,
        (∫ x in Ω, ‖hu.weakGrad x‖ ^ 2) ≤ ∫ x in Ω, ‖hv.weakGrad x‖ ^ 2)
    {φ : E → ℝ} (hφ : DeGiorgi.IsSmoothTestOn Ω φ) :
    (∫ x in Ω, _root_.Inner.inner ℝ (hu.weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0 := by
  let hφw := DeGiorgi.smoothTestWitness hΩ hφ
  have hvariation (t : ℝ) : DeGiorgi.MemW01p 2
      (fun x => (u x + t * φ x) - b x) Ω := by
    have hv := hu0.add ((DeGiorgi.smoothTest_memH01 hΩ hφ).smul t)
    have heq : (fun x => (u x - b x) + t * φ x) =
        (fun x => (u x + t * φ x) - b x) := by funext x; ring
    exact heq ▸ hv
  have hnorm (t : ℝ) : ‖DeGiorgi.gradLpOfWitness hu‖ ^ 2 ≤
      ‖DeGiorgi.gradLpOfWitness hu + t • DeGiorgi.gradLpOfWitness hφw‖ ^ 2 := by
    rw [← gradLpOfWitness_add_smul, norm_gradLpOfWitness_sq_eq_integral,
      norm_gradLpOfWitness_sq_eq_integral]
    exact hmin _ (hvariation t) (hu.add (hφw.smul t))
  have hz := inner_eq_zero_of_norm_sq_min _ _ hnorm
  have heq : _root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness hu) (DeGiorgi.gradLpOfWitness hφw) =
      ∫ x in Ω, _root_.Inner.inner ℝ (hu.weakGrad x) (DeGiorgi.smoothGradField φ x) := by
    change (∫ x in Ω, _root_.Inner.inner ℝ (DeGiorgi.gradLpOfWitness hu x)
      (DeGiorgi.gradLpOfWitness hφw x)) = _
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hu.weakGrad_memLp.coeFn_toLp, hφw.weakGrad_memLp.coeFn_toLp]
      with x hx hφx
    change _root_.Inner.inner ℝ (hu.weakGrad_memLp.toLp _ x) (hφw.weakGrad_memLp.toLp _ x) = _
    rw [hx, hφx]
    rfl
  exact heq.symm.trans hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_inner_weakGrad_smoothGrad_eq_zero_of_minimizer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_inner_weakGrad_smoothGrad_eq_zero_of_minimizer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_inner_weakGrad_smoothGrad_eq_zero_of_minimizer ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_inner_weakGrad_smoothGrad_eq_zero_of_minimizer

theorem integral_inner_weakGrad_smoothGrad_eq_zero_of_dirichlet_minimizer
    {ι : Type*} [Fintype ι] (hΩ : IsOpen Ω)
    {u b : E → EuclideanSpace ℝ ι}
    (hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) Ω)
    (hu0 : ∀ i, DeGiorgi.MemW01p 2 (fun x => u x i - b x i) Ω)
    (hmin : ∀ (v : E → EuclideanSpace ℝ ι),
      (∀ i, DeGiorgi.MemW01p 2 (fun x => v x i - b x i) Ω) →
      ∀ hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω,
        (∑ i, ∫ x in Ω, ‖(hu i).weakGrad x‖ ^ 2) ≤
          ∑ i, ∫ x in Ω, ‖(hv i).weakGrad x‖ ^ 2)
    (i : ι) {φ : E → ℝ} (hφ : DeGiorgi.IsSmoothTestOn Ω φ) :
    (∫ x in Ω, _root_.Inner.inner ℝ ((hu i).weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0 := by
  classical
  apply integral_inner_weakGrad_smoothGrad_eq_zero_of_minimizer hΩ (hu i) (hu0 i) _ hφ
  intro v hv0 hv
  let w : E → EuclideanSpace ℝ ι :=
    fun x => WithLp.toLp 2 (Function.update (WithLp.ofLp (u x)) i (v x))
  have hw0 (j : ι) : DeGiorgi.MemW01p 2 (fun x => w x j - b x j) Ω := by
    by_cases hji : j = i
    · subst j
      simpa only [w, PiLp.toLp_apply, Function.update_self] using hv0
    · simpa only [w, PiLp.toLp_apply, Function.update_of_ne hji] using hu0 j
  let hw (j : ι) : DeGiorgi.MemW1pWitness 2 (fun x => w x j) Ω :=
    { memLp := by
        by_cases hji : j = i
        · subst j
          simpa only [w, PiLp.toLp_apply, Function.update_self] using hv.memLp
        · simpa only [w, PiLp.toLp_apply, Function.update_of_ne hji] using (hu j).memLp
      weakGrad := if j = i then hv.weakGrad else (hu j).weakGrad
      weakGrad_component_memLp := by
        intro k
        split
        · exact hv.weakGrad_component_memLp k
        · exact (hu j).weakGrad_component_memLp k
      isWeakGrad := by
        by_cases hji : j = i
        · subst j
          simpa only [if_pos rfl, if_true, w, PiLp.toLp_apply, Function.update_self]
            using hv.isWeakGrad
        · simpa only [if_neg hji, w, PiLp.toLp_apply, Function.update_of_ne hji]
            using (hu j).isWeakGrad }
  have hm := hmin w hw0 hw
  have heq (j : ι) : (∫ x in Ω, ‖(hw j).weakGrad x‖ ^ 2) =
      if j = i then ∫ x in Ω, ‖hv.weakGrad x‖ ^ 2
      else ∫ x in Ω, ‖(hu j).weakGrad x‖ ^ 2 := by
    by_cases hji : j = i <;> simp only [hw, hji, if_true, if_false]
  simp_rw [heq] at hm
  have hsum : (∑ j, if j = i then ∫ x in Ω, ‖hv.weakGrad x‖ ^ 2
      else ∫ x in Ω, ‖(hu j).weakGrad x‖ ^ 2) =
      (∫ x in Ω, ‖hv.weakGrad x‖ ^ 2) +
        ∑ j ∈ Finset.univ.erase i, ∫ x in Ω, ‖(hu j).weakGrad x‖ ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    · exact if_pos rfl
    · apply Finset.sum_congr rfl
      intro j hj
      rw [if_neg (Finset.mem_erase.mp hj).1]
  rw [hsum] at hm
  have hsumU := Finset.add_sum_erase Finset.univ
    (fun j => ∫ x in Ω, ‖(hu j).weakGrad x‖ ^ 2) (Finset.mem_univ i)
  rw [← hsumU] at hm
  exact (add_le_add_iff_right _).mp hm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_inner_weakGrad_smoothGrad_eq_zero_of_dirichlet_minimizer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_inner_weakGrad_smoothGrad_eq_zero_of_dirichlet_minimizer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_inner_weakGrad_smoothGrad_eq_zero_of_dirichlet_minimizer ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_inner_weakGrad_smoothGrad_eq_zero_of_dirichlet_minimizer

end DifferentialGeometry.Analysis.Sobolev.Euclidean
