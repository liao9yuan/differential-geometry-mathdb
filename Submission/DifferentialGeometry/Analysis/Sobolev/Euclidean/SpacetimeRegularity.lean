import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Spacetime
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Mixed
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.FiniteOrder
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakPartialTree

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem contDiffOn_of_continuousOn_mixed_weak_partial_tree
    {a b : ℝ} {Ω : Set E} (hΩ : IsOpen Ω) {m K : ℕ}
    (hKm : (m : ℝ) + (d + 1 : ℝ) / 2 < K)
    (u : ℝ × E → ℝ) (hu : ContinuousOn u (_root_.Set.Ioo a b ×ˢ Ω))
    (Y : ∀ n : ℕ, (Fin n → Fin (d + 1)) →
      _root_.MeasureTheory.Lp ℝ 2 ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)))
    (hroot : Y 0 (fun i => Fin.elim0 i)
      =ᵐ[(volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)] u)
    (hweak : ∀ n < K, ∀ α i (φ : ℝ × E → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ _root_.Set.Ioo a b ×ˢ Ω →
      (∫ q, Y n α q * fderiv ℝ φ q
        (Fin.cases (1, 0) (fun l => (0, EuclideanSpace.single l 1)) i)
          ∂(volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) =
        -∫ q, Y (n + 1) (Fin.cons i α) q * φ q
          ∂(volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) :
    ContDiffOn ℝ m u (_root_.Set.Ioo a b ×ˢ Ω) := by
  let e := EuclideanSpace.finSuccEquivProd d
  let Ω₁ := e ⁻¹' (_root_.Set.Ioo a b ×ˢ Ω)
  have hΩ₁ : IsOpen Ω₁ := (isOpen_Ioo.prod hΩ).preimage e.continuous
  obtain ⟨Z, hZ, hZweak⟩ := exists_lp_spacetime_weak_partial_tree K Y hweak
  have hmem : MemWkp K 2 (Z 0 (fun i => Fin.elim0 i)) Ω₁ :=
    memWkp_of_finite_weak_partial_tree (by norm_num) hΩ₁ K
      (fun n α x => Z n α x) (fun n _ α => Lp.memLp (Z n α)) hZweak
  have hν : (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (ℝ × E)).restrict (_root_.Set.Ioo a b ×ˢ Ω) =
      (volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
      Measure.restrict_congr_set _root_.MeasureTheory.Ioo_ae_eq_Icc]
  have he : _root_.MeasureTheory.MeasurePreserving e (volume.restrict Ω₁)
      ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) := by
    have h := (EuclideanSpace.measurePreserving_finSuccEquivProd d).restrict_preimage_emb
      e.toHomeomorph.measurableEmbedding (_root_.Set.Ioo a b ×ˢ Ω)
    simpa only [hν] using h
  have hzu : Z 0 (fun i => Fin.elim0 i) =ᵐ[volume.restrict Ω₁] u ∘ e :=
    (hZ 0 (fun i => Fin.elim0 i)).trans (he.quasiMeasurePreserving.ae hroot)
  have huMem : MemWkp K 2 (u ∘ e) Ω₁ :=
    (MemWkp_congr_ae (by norm_num) hΩ₁ hzu).mp hmem
  have huCont : ContinuousOn (u ∘ e) Ω₁ :=
    hu.comp e.continuous.continuousOn (fun _ hx => hx)
  have huDiff : ContDiffOn ℝ m (u ∘ e) Ω₁ :=
    EuclideanIteratedEmbedding.contDiffOn_of_continuousOn_of_memWkp_two
      hΩ₁ (by simpa only [Nat.cast_add, Nat.cast_one] using hKm) huCont huMem
  have hcomp := huDiff.comp e.symm.contDiff.contDiffOn
    (show _root_.Set.MapsTo e.symm (_root_.Set.Ioo a b ×ˢ Ω) Ω₁ from fun p hp => by
      simpa only [Ω₁, _root_.Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hp)
  simpa only [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply] using hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.contDiffOn_of_continuousOn_mixed_weak_partial_tree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.contDiffOn_of_continuousOn_mixed_weak_partial_tree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.contDiffOn_of_continuousOn_mixed_weak_partial_tree ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.contDiffOn_of_continuousOn_mixed_weak_partial_tree


theorem contDiffOn_of_continuousOn_finite_time_weak_partial_trees
    {a b : ℝ} {Ω : Set E} (hΩ : IsOpen Ω) {m K : ℕ}
    (hKm : (m : ℝ) + (d + 1 : ℝ) / 2 < K)
    (u : ℝ × E → ℝ) (hu : ContinuousOn u (_root_.Set.Ioo a b ×ˢ Ω))
    (U : Fin (K + 1) → ∀ n : ℕ, (Fin n → Fin d) →
      _root_.MeasureTheory.Lp ℝ 2 ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)))
    (hroot : U 0 0 (fun i => Fin.elim0 i)
      =ᵐ[(volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)] u)
    (hspace : ∀ j n, j.val + n < K → ∀ α i, ∀ᵐ t ∂volume.restrict (_root_.Set.Icc a b),
      DeGiorgi.HasWeakPartialDeriv i
        (fun x => U j (n + 1) (Fin.cons i α) (t, x)) (fun x => U j n α (t, x)) Ω)
    (htime : ∀ (j : Fin K) n, j.val + n < K → ∀ α (φ : ℝ × E → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ _root_.Set.Ioo a b ×ˢ Ω →
      (∫ q, U j.castSucc n α q * fderiv ℝ φ q (1, 0)
        ∂(volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) =
        -∫ q, U j.succ n α q * φ q
          ∂(volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) :
    ContDiffOn ℝ m u (_root_.Set.Ioo a b ×ˢ Ω) := by
  obtain ⟨Y, hYroot, hYweak⟩ := exists_lp_mixed_weak_partial_tree_of_finite_time_trees
    (by norm_num) K U hspace htime
  apply contDiffOn_of_continuousOn_mixed_weak_partial_tree hΩ hKm u hu Y _ hYweak
  simpa only [hYroot] using hroot

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.contDiffOn_of_continuousOn_finite_time_weak_partial_trees then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.contDiffOn_of_continuousOn_finite_time_weak_partial_trees"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.contDiffOn_of_continuousOn_finite_time_weak_partial_trees ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.contDiffOn_of_continuousOn_finite_time_weak_partial_trees

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
