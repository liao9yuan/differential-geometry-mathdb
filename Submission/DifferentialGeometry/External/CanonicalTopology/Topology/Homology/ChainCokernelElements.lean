import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Concrete representatives in the original chain-complex cokernel -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

universe u v

namespace DifferentialGeometry.Topology

variable {R : Type u} [Ring R] {K L K' L' : ChainComplex (ModuleCat.{v} R) ℕ}

/-- Every element of the ORIGINAL chain-complex cokernel is represented
by an original target chain in the same degree. -/
theorem chainCokernelπ_surjective (f : K ⟶ L) (n : ℕ) :
    Function.Surjective ((cokernel.π f).f n) :=
  (ModuleCat.epi_iff_surjective _).mp inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.chainCokernelπ_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.chainCokernelπ_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.chainCokernelπ_surjective ``Submission.DifferentialGeometry.Topology.chainCokernelπ_surjective

/-- A chain projects to zero exactly when it is the image of an original
source chain. This follows from exactness of the actual cokernel sequence. -/
theorem chainCokernelπ_eq_zero_iff (f : K ⟶ L) (n : ℕ) (c : L.X n) :
    (cokernel.π f).f n c = 0 ↔ ∃ b : K.X n, f.f n b = c := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.Exact := S.exact_of_g_is_cokernel (_root_.CategoryTheory.Limits.cokernelIsCokernel f)
  have hSn := hS.map (_root_.HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.down ℕ) n)
  constructor
  · exact (ShortComplex.moduleCat_exact_iff _).mp hSn c
  · rintro ⟨b, rfl⟩
    exact congrArg (fun k : K ⟶ _root_.CategoryTheory.Limits.cokernel f => k.f n b) (cokernel.condition f)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.chainCokernelπ_eq_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.chainCokernelπ_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.chainCokernelπ_eq_zero_iff ``Submission.DifferentialGeometry.Topology.chainCokernelπ_eq_zero_iff

/-- Equality in the SAME cokernel is equality modulo the actual image. -/
theorem chainCokernelπ_eq_iff (f : K ⟶ L) (n : ℕ) (c d : L.X n) :
    (cokernel.π f).f n c = (cokernel.π f).f n d ↔ ∃ b : K.X n, f.f n b = c - d := by
  rw [← sub_eq_zero, ← map_sub, chainCokernelπ_eq_zero_iff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.chainCokernelπ_eq_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.chainCokernelπ_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.chainCokernelπ_eq_iff ``Submission.DifferentialGeometry.Topology.chainCokernelπ_eq_iff

/-- A map of the original cokernels acts by the original map on the
same representative chain. -/
theorem chainCokernelMap_π (f : K ⟶ L) (g : K' ⟶ L') (p : K ⟶ K') (q : L ⟶ L')
    (h : f ≫ q = p ≫ g) (n : ℕ) (c : L.X n) :
    (cokernel.map f g p q h).f n ((cokernel.π f).f n c) = (cokernel.π g).f n (q.f n c) :=
  congrArg (fun k : L ⟶ _root_.CategoryTheory.Limits.cokernel g => k.f n c) (cokernel.π_desc f _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.chainCokernelMap_π then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.chainCokernelMap_π"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.chainCokernelMap_π ``Submission.DifferentialGeometry.Topology.chainCokernelMap_π

/-- An original cokernel map is an isomorphism when actual image
membership is reflected and every original target representative lifts
modulo the actual target image. -/
theorem isIso_chainCokernelMap_of_representatives (f : K ⟶ L) (g : K' ⟶ L')
    (p : K ⟶ K') (q : L ⟶ L') (h : f ≫ q = p ≫ g)
    (hinj : ∀ n, ∀ c : L.X n, ∀ b : K'.X n, g.f n b = q.f n c →
      ∃ a : K.X n, f.f n a = c)
    (hsurj : ∀ n, ∀ d : L'.X n, ∃ c : L.X n, ∃ b : K'.X n, g.f n b = d - q.f n c) :
    IsIso (cokernel.map f g p q h) := by
  have hcomp (n : ℕ) : _root_.CategoryTheory.IsIso ((cokernel.map f g p q h).f n) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · apply (injective_iff_map_eq_zero ((cokernel.map f g p q h).f n).hom).mpr
      intro z hz
      obtain ⟨c, rfl⟩ := chainCokernelπ_surjective f n z
      change (cokernel.map f g p q h).f n ((cokernel.π f).f n c) = 0 at hz
      rw [chainCokernelMap_π, chainCokernelπ_eq_zero_iff] at hz
      obtain ⟨b, hb⟩ := hz
      exact (chainCokernelπ_eq_zero_iff f n c).mpr (hinj n c b hb)
    · intro z
      obtain ⟨d, rfl⟩ := chainCokernelπ_surjective g n z
      obtain ⟨c, b, hb⟩ := hsurj n d
      refine ⟨(cokernel.π f).f n c, ?_⟩
      rw [chainCokernelMap_π]
      exact ((chainCokernelπ_eq_iff g n d (q.f n c)).mpr ⟨b, hb⟩).symm
  let := hcomp
  exact HomologicalComplex.Hom.isIso_of_components _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isIso_chainCokernelMap_of_representatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isIso_chainCokernelMap_of_representatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isIso_chainCokernelMap_of_representatives ``Submission.DifferentialGeometry.Topology.isIso_chainCokernelMap_of_representatives

end DifferentialGeometry.Topology
