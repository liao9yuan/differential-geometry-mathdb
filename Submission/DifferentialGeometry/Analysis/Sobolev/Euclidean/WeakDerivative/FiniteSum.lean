import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set

namespace DeGiorgi

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem HasWeakPartialDeriv.finset_sum
    {i : Fin d} {Omega : Set E} {ι : Type*} (s : Finset ι)
    {f g : ι → E → ℝ}
    (hf : ∀ j ∈ s, _root_.MeasureTheory.LocallyIntegrable (f j) (volume.restrict Omega))
    (hg : ∀ j ∈ s, _root_.MeasureTheory.LocallyIntegrable (g j) (volume.restrict Omega))
    (hparts : ∀ j ∈ s, HasWeakPartialDeriv i (g j) (f j) Omega) :
    HasWeakPartialDeriv i (fun x => ∑ j ∈ s, g j x)
      (fun x => ∑ j ∈ s, f j x) Omega := by
  classical
  induction s using Finset.induction with
  | empty =>
      intro phi hphi hphi_cpt hphi_sub
      simp
  | insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      exact (hparts j (Finset.mem_insert_self _ _)).add
        (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
          (fun k hk => hg k (Finset.mem_insert_of_mem hk))
          (fun k hk => hparts k (Finset.mem_insert_of_mem hk)))
        (hf j (Finset.mem_insert_self _ _))
        (_root_.MeasureTheory.locallyIntegrable_finsetSum s (fun k hk => hf k (Finset.mem_insert_of_mem hk)))
        (hg j (Finset.mem_insert_self _ _))
        (_root_.MeasureTheory.locallyIntegrable_finsetSum s (fun k hk => hg k (Finset.mem_insert_of_mem hk)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.HasWeakPartialDeriv.finset_sum then
    throwError "Refusing to shadow existing declaration DeGiorgi.HasWeakPartialDeriv.finset_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.HasWeakPartialDeriv.finset_sum ``Submission.DeGiorgi.HasWeakPartialDeriv.finset_sum

end DeGiorgi
