import Submission.DifferentialGeometry.Topology.Homology.Algebra.CokernelHomotopy
import Submission.DifferentialGeometry.Topology.Homology.Algebra.LocallyNilpotent
import Mathlib.Algebra.Homology.HomologySequenceLemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.CategoryTheory _root_.CategoryTheory.Limits
noncomputable section
universe u v
namespace DifferentialGeometry.HomologicalComplex
variable {k : Type u} [Ring k]
  {A K : ChainComplex (ModuleCat.{v} k) ℕ} (i : A ⟶ K)


theorem quasiIso_of_isZero_cokernel_homology [_root_.CategoryTheory.Mono i]
    (hQ : ∀ n, _root_.CategoryTheory.Limits.IsZero ((_root_.CategoryTheory.Limits.cokernel i).homology n)) :
    _root_.QuasiIso i := by
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact := {
    exact := ShortComplex.exact_of_g_is_cokernel _ (_root_.CategoryTheory.Limits.cokernelIsCokernel i)
    mono_f := inferInstanceAs (_root_.CategoryTheory.Mono i)
    epi_g := inferInstanceAs (_root_.CategoryTheory.Epi (cokernel.π i)) }
  rw [_root_.quasiIso_iff]
  intro n
  rw [_root_.quasiIsoAt_iff_isIso_homologyMap]
  have : _root_.CategoryTheory.Mono (_root_.HomologicalComplex.homologyMap i n) :=
    (hS.homology_exact₁ (n + 1) n rfl).mono_g ((hQ (n + 1)).eq_zero_of_src _)
  have : _root_.CategoryTheory.Epi (_root_.HomologicalComplex.homologyMap i n) :=
    (hS.homology_exact₂ n).epi_f ((hQ n).eq_zero_of_tgt _)
  exact _root_.CategoryTheory.isIso_of_mono_of_epi _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.quasiIso_of_isZero_cokernel_homology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.quasiIso_of_isZero_cokernel_homology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.quasiIso_of_isZero_cokernel_homology ``Submission.DifferentialGeometry.HomologicalComplex.quasiIso_of_isZero_cokernel_homology

variable (a : A ⟶ A) (b : End K) (hab : i ≫ b = a ≫ i)


theorem cokernel_π_endomorphism_pow (N : ℕ) :
    cokernel.π i ≫ (End.of (cokernelEndomorphism i a b hab) ^ N) =
      (b ^ N) ≫ cokernel.π i := by
  induction N with
  | zero => simp
  | succ N hN =>
    rw [pow_succ, End.mul_def, ← Category.assoc, cokernel_π_endomorphism,
      Category.assoc, hN, ← Category.assoc, ← End.mul_def, ← pow_succ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.cokernel_π_endomorphism_pow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.cokernel_π_endomorphism_pow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.cokernel_π_endomorphism_pow ``Submission.DifferentialGeometry.HomologicalComplex.cokernel_π_endomorphism_pow

theorem cokernelEndomorphism_locallyNilpotent
    (henter : ∀ n, ∀ x : K.X n, ∃ N : ℕ,
      ((b ^ N).f n) x ∈ LinearMap.range (i.f n).hom) :
    ∀ n, ∀ x : (_root_.CategoryTheory.Limits.cokernel i).X n, ∃ N : ℕ,
      ((End.of (cokernelEndomorphism i a b hab) ^ N).f n) x = 0 := by
  intro n x
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective ((cokernel.π i).f n)).mp inferInstance x
  obtain ⟨N, z, hz⟩ := henter n y
  refine ⟨N, ?_⟩
  have hh := ConcreteCategory.congr_hom
    (_root_.HomologicalComplex.congr_hom (cokernel_π_endomorphism_pow i a b hab N) n) y
  change ((End.of (cokernelEndomorphism i a b hab) ^ N).f n) ((cokernel.π i).f n y) =
    (cokernel.π i).f n (((b ^ N).f n) y) at hh
  rw [← hz] at hh
  have hz0 := ConcreteCategory.congr_hom
    (_root_.HomologicalComplex.congr_hom (cokernel.condition i) n) z
  exact hh.trans hz0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.cokernelEndomorphism_locallyNilpotent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.cokernelEndomorphism_locallyNilpotent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.cokernelEndomorphism_locallyNilpotent ``Submission.DifferentialGeometry.HomologicalComplex.cokernelEndomorphism_locallyNilpotent

include hab in
theorem quasiIso_of_eventually_in_image [_root_.CategoryTheory.Mono i]
    (H : Homotopy b (𝟙 K)) (hA : ∀ n : ℕ, A.X n ⟶ A.X (n + 1))
    (hcompat : ∀ n, i.f n ≫ H.hom n (n + 1) = hA n ≫ i.f (n + 1))
    (henter : ∀ n, ∀ x : K.X n, ∃ N : ℕ,
      ((b ^ N).f n) x ∈ LinearMap.range (i.f n).hom) :
    _root_.QuasiIso i := by
  apply quasiIso_of_isZero_cokernel_homology i
  exact isZero_homology_of_locallyNilpotent (_root_.CategoryTheory.Limits.cokernel i)
    (End.of (cokernelEndomorphism i a b hab)) (cokernelHomotopy i a b hab H hA hcompat)
    (cokernelEndomorphism_locallyNilpotent i a b hab henter)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.quasiIso_of_eventually_in_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.quasiIso_of_eventually_in_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.quasiIso_of_eventually_in_image ``Submission.DifferentialGeometry.HomologicalComplex.quasiIso_of_eventually_in_image

end DifferentialGeometry.HomologicalComplex
