import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import Mathlib.MeasureTheory.Function.LpSpace.Complete

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology
open scoped _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem eLpNorm_iterWeakPartial_le_wkpNorm
    {k : ℕ} (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E)
    (j₀ : ℕ) (hj₀ : j₀ ≤ k) (β₀ : Fin j₀ → Fin d) :
    eLpNorm (iterWeakPartial (d := d) p j₀ β₀ u Ω) p (volume.restrict Ω) ≤
      iteratedWeakSobolevNorm (d := d) k p u Ω := by
  classical
  unfold iteratedWeakSobolevNorm
  have h_inner :
      eLpNorm (iterWeakPartial (d := d) p j₀ β₀ u Ω) p (volume.restrict Ω) ≤
        ∑ β : Fin j₀ → Fin d,
          eLpNorm (iterWeakPartial (d := d) p j₀ β u Ω) p (volume.restrict Ω) :=
    Finset.single_le_sum
      (f := fun β : Fin j₀ → Fin d =>
        eLpNorm (iterWeakPartial (d := d) p j₀ β u Ω) p (volume.restrict Ω))
      (s := (Finset.univ : Finset (Fin j₀ → Fin d)))
      (fun _ _ => bot_le) (Finset.mem_univ _)
  have h_outer :
      (∑ β : Fin j₀ → Fin d,
        eLpNorm (iterWeakPartial (d := d) p j₀ β u Ω) p (volume.restrict Ω)) ≤
      ∑ j ∈ Finset.range (k + 1),
        ∑ β : Fin j → Fin d,
          eLpNorm (iterWeakPartial (d := d) p j β u Ω) p (volume.restrict Ω) := by
    refine Finset.single_le_sum
      (f := fun j : ℕ =>
        ∑ β : Fin j → Fin d,
          eLpNorm (iterWeakPartial (d := d) p j β u Ω) p (volume.restrict Ω))
      (s := Finset.range (k + 1))
      (fun _ _ => bot_le) ?_
    rw [Finset.mem_range]
    omega
  exact le_trans h_inner h_outer

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_iterWeakPartial_le_wkpNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_iterWeakPartial_le_wkpNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_iterWeakPartial_le_wkpNorm ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_iterWeakPartial_le_wkpNorm

theorem iterWeakPartial_cauchy_of_wkpNorm_cauchy
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u : ℕ → E → ℝ}
    (hu : ∀ n, MemWkp (d := d) k p (u n) Ω)
    {B : ℕ → ℝ≥0∞}
    (h_cau : ∀ N n m, N ≤ n → N ≤ m →
      iteratedWeakSobolevNorm (d := d) k p (fun x => u n x - u m x) Ω < B N)
    {j : ℕ} (hj : j ≤ k) (β : Fin j → Fin d) :
    ∀ N n m, N ≤ n → N ≤ m →
      _root_.MeasureTheory.eLpNorm
        (fun x => iterWeakPartial (d := d) p j β (u n) Ω x -
          iterWeakPartial (d := d) p j β (u m) Ω x)
        p (volume.restrict Ω) < B N := by
  intro N n m hn hm
  have h_bound := h_cau N n m hn hm
  have h_iter_le := eLpNorm_iterWeakPartial_le_wkpNorm
    (d := d) (k := k) (p := p)
    (u := fun x => u n x - u m x) (Ω := Ω) j hj β
  have h_uW : MemWkp (d := d) j p (u n) Ω := MemWkp.le_of_le hj (hu n)
  have h_vW : MemWkp (d := d) j p (u m) Ω := MemWkp.le_of_le hj (hu m)
  have h_iter_sub_ae :=
    iterWeakPartial_add_ae (d := d) hp hΩ β h_uW (MemWkp.neg (d := d) hp hΩ h_vW)
  have h_iter_neg_ae := iterWeakPartial_const_smul_ae
    (d := d) hp hΩ β h_vW (-1)
  have h_iter_sub : iterWeakPartial (d := d) p j β (fun x => u n x - u m x) Ω
      =ᵐ[volume.restrict Ω]
      (fun x => iterWeakPartial (d := d) p j β (u n) Ω x -
        iterWeakPartial (d := d) p j β (u m) Ω x) := by
    have h_eq_un_sub : (fun x => u n x - u m x) = (fun x => u n x + (-1) * u m x) := by
      funext x; ring
    rw [h_eq_un_sub]
    have h_neg_uW : MemWkp (d := d) j p (fun x => (-1 : ℝ) * u m x) Ω :=
      MemWkp.const_smul (d := d) hp hΩ h_vW (-1)
    have h_iter_add :=
      iterWeakPartial_add_ae (d := d) hp hΩ β h_uW h_neg_uW
    refine h_iter_add.trans ?_
    have h_iter_smul := iterWeakPartial_const_smul_ae
      (d := d) hp hΩ β h_vW (-1)
    filter_upwards [h_iter_smul] with x hx
    rw [hx]
    ring
  rw [_root_.MeasureTheory.eLpNorm_congr_ae h_iter_sub] at h_iter_le
  exact lt_of_le_of_lt h_iter_le h_bound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_cauchy_of_wkpNorm_cauchy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_cauchy_of_wkpNorm_cauchy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_cauchy_of_wkpNorm_cauchy ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_cauchy_of_wkpNorm_cauchy

theorem exists_eLpNorm_limit_iterWeakPartial
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u : ℕ → E → ℝ}
    (hu : ∀ n, MemWkp (d := d) k p (u n) Ω)
    {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h_cau : ∀ N n m, N ≤ n → N ≤ m →
      iteratedWeakSobolevNorm (d := d) k p (fun x => u n x - u m x) Ω < B N)
    {j : ℕ} (hj : j ≤ k) (β : Fin j → Fin d) :
    ∃ (v : E → ℝ), _root_.MeasureTheory.MemLp v p (volume.restrict Ω) ∧
      atTop.Tendsto
        (fun n => _root_.MeasureTheory.eLpNorm
          (fun x => iterWeakPartial (d := d) p j β (u n) Ω x - v x)
          p (volume.restrict Ω))
        (𝓝 0) := by
  classical
  have h_iter_memLp : ∀ n,
      MemLp (iterWeakPartial (d := d) p j β (u n) Ω) p (volume.restrict Ω) := by
    intro n
    have h_uWj : MemWkp (d := d) j p (u n) Ω := MemWkp.le_of_le hj (hu n)
    exact iterWeakPartial_memLp_of_memWkp (d := d) (p := p) h_uWj β
  have h_iter_cau :=
    iterWeakPartial_cauchy_of_wkpNorm_cauchy (d := d) hp_one hΩ hu h_cau hj β
  have h_iter_cau' : ∀ N n m : ℕ, N ≤ n → N ≤ m →
      _root_.MeasureTheory.eLpNorm
        ((fun n => iterWeakPartial (d := d) p j β (u n) Ω) n -
          (fun n => iterWeakPartial (d := d) p j β (u n) Ω) m)
        p (volume.restrict Ω) < B N := by
    intro N n m hn hm
    have h := h_iter_cau N n m hn hm
    have hEq :
        ((fun n => iterWeakPartial (d := d) p j β (u n) Ω) n -
          (fun n => iterWeakPartial (d := d) p j β (u n) Ω) m) =
        fun x => iterWeakPartial (d := d) p j β (u n) Ω x -
          iterWeakPartial (d := d) p j β (u m) Ω x := by
      funext x
      simp [Pi.sub_apply]
    rw [hEq]
    exact h
  rcases MeasureTheory.Lp.cauchy_complete_eLpNorm
      (μ := volume.restrict Ω) hp_one h_iter_memLp hB h_iter_cau'
      with ⟨v, hv_memLp, hv_tendsto⟩
  refine ⟨v, hv_memLp, ?_⟩
  have hEq : (fun n => _root_.MeasureTheory.eLpNorm
        ((fun n => iterWeakPartial (d := d) p j β (u n) Ω) n - v)
        p (volume.restrict Ω)) =
      (fun n => _root_.MeasureTheory.eLpNorm
        (fun x => iterWeakPartial (d := d) p j β (u n) Ω x - v x)
        p (volume.restrict Ω)) := by
    funext n
    rfl
  rw [hEq] at hv_tendsto
  exact hv_tendsto

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_eLpNorm_limit_iterWeakPartial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_eLpNorm_limit_iterWeakPartial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_eLpNorm_limit_iterWeakPartial ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_eLpNorm_limit_iterWeakPartial

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
