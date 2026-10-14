import Submission.DifferentialGeometry.Topology.Morse.FiniteBandEuler
import Submission.DifferentialGeometry.Topology.Morse.RelativePerturbationGlobal
import Submission.DifferentialGeometry.Topology.Morse.Excellent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Topology.Morse
namespace DifferentialGeometry.Morse
variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M] [CompactSpace M]

theorem finiteHomologyType_and_eulerChar_of_finite_morse
    (K : Type) [Field K] {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hfinite : {x | IsCriticalPointAt I f x}.Finite)
    (hnd : ∀ x, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x)
    (hinj : _root_.Set.InjOn f {x | IsCriticalPointAt I f x}) :
    DifferentialGeometry.Homology.finiteHomologyType K (TopCat.of M) ∧
      DifferentialGeometry.Homology.eulerChar K (TopCat.of M) =
        ∑ p ∈ hfinite.toFinset, (-1 : ℤ) ^ sigNeg (chartHessianAt
          (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) := by
  obtain ⟨A,hA⟩ := (isCompact_range hf.continuous).bddAbove
  have hbelow (x : M) : f x < A + 1 := lt_of_le_of_lt (hA (_root_.Set.mem_range_self x)) (lt_add_one A)
  have htop : sublevel f (A + 1) = univ := _root_.Set.eq_univ_of_forall fun x => (hbelow x).le
  let eTop : SublevelSpace f (A + 1) ≃ₜ M :=
    (Homeomorph.setCongr htop).trans (Homeomorph.Set.univ M)
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (Module.finrank_pos (R := ℝ) (M := E)).ne'
  let e : E ≃L[ℝ] MorseModel (m + 1) :=
    ((Module.finBasis ℝ E).reindex (finCongr hm)).equivFunL
  obtain ⟨hfin,hχ⟩ := finiteHomologyType_and_eulerChar_of_finite_morse_sublevel I K e
    hf (A + 1) (htop ▸ isCompact_univ) (fun _ _ => BoundarylessManifold.isInteriorPoint)
    hfinite hnd hinj (fun x _ => hbelow x)
  exact ⟨(DifferentialGeometry.Homology.finiteHomologyType_iff_of_homeomorph K
      (X := TopCat.of (SublevelSpace f (A + 1))) (Y := TopCat.of M) eTop).mp hfin,
    (DifferentialGeometry.Homology.eulerChar_eq_of_homeomorph K eTop).symm.trans hχ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.finiteHomologyType_and_eulerChar_of_finite_morse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.finiteHomologyType_and_eulerChar_of_finite_morse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.finiteHomologyType_and_eulerChar_of_finite_morse ``Submission.DifferentialGeometry.Morse.finiteHomologyType_and_eulerChar_of_finite_morse

theorem exists_morse_eulerChar :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧
      (∀ x, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x) ∧
      _root_.Set.InjOn f {x | IsCriticalPointAt I f x} ∧
      ∃ hfinite : {x | IsCriticalPointAt I f x}.Finite,
        ∀ (K : Type) [Field K], DifferentialGeometry.Homology.finiteHomologyType K (TopCat.of M) ∧
          DifferentialGeometry.Homology.eulerChar K (TopCat.of M) =
            ∑ p ∈ hfinite.toFinset, (-1 : ℤ)^sigNeg (chartHessianAt
              (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) := by
  obtain ⟨g,hg,_,hgpos,hgnd,hgfin⟩ := exists_positive_relative_morse
    (I := I) (f := fun _ : M => (1 : ℝ)) contMDiff_const
    (K := _root_.Set.univ) (U := _root_.Set.univ) (S := _root_.Set.univ) isCompact_univ isOpen_univ (Subset.refl _)
    (fun _ _ => BoundarylessManifold.isInteriorPoint) (fun _ _ => _root_.Set.mem_univ _)
    (Subset.refl _) (fun _ _ => zero_lt_one)
  obtain ⟨f,hf,_,_,hcrit,hinj,hnd,_⟩ := exists_positive_relative_excellent_morse hg hgfin
    (fun x hx => (hgnd x hx).2) (U := _root_.Set.univ) (S := _root_.Set.univ) isOpen_univ (_root_.Set.subset_univ _)
    (fun _ _ => BoundarylessManifold.isInteriorPoint) (Subset.refl _) hgpos
  have hfinite : {x | IsCriticalPointAt I f x}.Finite := hcrit.symm ▸ hgfin
  refine ⟨f,hf,hnd,hinj,hfinite,?_⟩
  intro K instK
  exact finiteHomologyType_and_eulerChar_of_finite_morse I K hf hfinite hnd hinj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.exists_morse_eulerChar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.exists_morse_eulerChar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.exists_morse_eulerChar ``Submission.DifferentialGeometry.Morse.exists_morse_eulerChar

end DifferentialGeometry.Morse
