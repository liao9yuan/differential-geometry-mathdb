import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.Abelian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits

namespace DifferentialGeometry.Topology.SphereSeparation

variable {R : Type*} [CommRing R]

def ModuleEndomorphism.IsLocallyNilpotent {M : ModuleCat R} (f : M ⟶ M) : Prop :=
  ∀ x : M, ∃ k : ℕ, (f^[k]) x = 0

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.IsLocallyNilpotent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.IsLocallyNilpotent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.IsLocallyNilpotent ``Submission.DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.IsLocallyNilpotent

namespace ModuleEndomorphism

theorem IsLocallyNilpotent.congr {M : ModuleCat R} {f g : M ⟶ M}
    (hf : IsLocallyNilpotent f) (hfg : f = g) : IsLocallyNilpotent g := by
  subst hfg
  exact hf

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.IsLocallyNilpotent
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.IsLocallyNilpotent.congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.IsLocallyNilpotent.congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.IsLocallyNilpotent.congr ``Submission.DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.IsLocallyNilpotent.congr

theorem iterate_zero {M : ModuleCat R} (f : M ⟶ M) (k : ℕ) :
    (f^[k]) (0 : M) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, map_zero, ih]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.iterate_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.iterate_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.iterate_zero ``Submission.DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.iterate_zero

theorem iterate_add {M : ModuleCat R} (f : M ⟶ M) (k : ℕ) (x y : M) :
    (f^[k]) (x + y) = (f^[k]) x + (f^[k]) y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply, map_add, ih,
        Function.iterate_succ_apply, Function.iterate_succ_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.iterate_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.iterate_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.iterate_add ``Submission.DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.iterate_add

theorem iterate_smul {M : ModuleCat R} (f : M ⟶ M) (k : ℕ) (r : R) (x : M) :
    (f^[k]) (r • x) = r • (f^[k]) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply, map_smul, ih,
        Function.iterate_succ_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.iterate_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.iterate_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.iterate_smul ``Submission.DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.iterate_smul

def locallyNilpotentSubmodule {M : ModuleCat R} (f : M ⟶ M) :
    Submodule R M where
  carrier := {x | ∃ k : ℕ, (f^[k]) x = 0}
  zero_mem' := ⟨0, rfl⟩
  add_mem' {x y} hx hy := by
    obtain ⟨k, hk⟩ := hx
    obtain ⟨l, hl⟩ := hy
    refine ⟨k + l, ?_⟩
    rw [iterate_add]
    have hx' : (f^[k + l]) x = 0 := by
      rw [Nat.add_comm, Function.iterate_add_apply, hk,
        iterate_zero]
    have hy' : (f^[k + l]) y = 0 := by
      rw [Function.iterate_add_apply, hl, iterate_zero]
    rw [hx', hy', add_zero]
  smul_mem' r x hx := by
    obtain ⟨k, hk⟩ := hx
    refine ⟨k, ?_⟩
    rw [iterate_smul, hk, smul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.locallyNilpotentSubmodule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.locallyNilpotentSubmodule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.locallyNilpotentSubmodule ``Submission.DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.locallyNilpotentSubmodule

@[simp]
theorem mem_locallyNilpotentSubmodule_iff {M : ModuleCat R} (f : M ⟶ M)
    (x : M) :
    x ∈ locallyNilpotentSubmodule f ↔ ∃ k : ℕ, (f^[k]) x = 0 :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.mem_locallyNilpotentSubmodule_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.mem_locallyNilpotentSubmodule_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.mem_locallyNilpotentSubmodule_iff ``Submission.DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.mem_locallyNilpotentSubmodule_iff


theorem isLocallyNilpotent_of_span
    {M : ModuleCat R} (f : M ⟶ M) (S : Set M)
    (hspan : Submodule.span R S = ⊤)
    (hS : ∀ x ∈ S, ∃ k : ℕ, (f^[k]) x = 0) :
    IsLocallyNilpotent f := by
  intro x
  have hle : Submodule.span R S ≤ locallyNilpotentSubmodule f :=
    Submodule.span_le.2 (fun y hy ↦ hS y hy)
  exact hle (by rw [hspan]; exact Submodule.mem_top)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.isLocallyNilpotent_of_span then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.isLocallyNilpotent_of_span"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.isLocallyNilpotent_of_span ``Submission.DifferentialGeometry.Topology.SphereSeparation.ModuleEndomorphism.isLocallyNilpotent_of_span

end ModuleEndomorphism

variable {K : ChainComplex (ModuleCat R) ℕ}

theorem locallyNilpotent_cyclesMap_of_f
    (T : K ⟶ K) (n : ℕ)
    (hT : ModuleEndomorphism.IsLocallyNilpotent (T.f n)) :
    ModuleEndomorphism.IsLocallyNilpotent
      (HomologicalComplex.cyclesMap T n) := by
  intro z
  obtain ⟨k, hk⟩ := hT (K.iCycles n z)
  refine ⟨k, ?_⟩
  apply ((ModuleCat.mono_iff_injective (K.iCycles n)).1 inferInstance)
  rw [map_zero]
  have hiterate : ∀ (j : ℕ) (w : K.cycles n),
      K.iCycles n (((HomologicalComplex.cyclesMap T n)^[j]) w) =
        ((T.f n)^[j]) (K.iCycles n w) := by
    intro j
    induction j with
    | zero => intro w; rfl
    | succ j ih =>
        intro w
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
        congr 1
        exact DFunLike.congr_fun
          (congrArg ModuleCat.Hom.hom
            (HomologicalComplex.cyclesMap_i (K := K) (L := K)
              (i := n) (φ := T))) w
  rw [hiterate, hk]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.locallyNilpotent_cyclesMap_of_f then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.locallyNilpotent_cyclesMap_of_f"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.locallyNilpotent_cyclesMap_of_f ``Submission.DifferentialGeometry.Topology.SphereSeparation.locallyNilpotent_cyclesMap_of_f


theorem locallyNilpotent_homologyMap_of_cyclesMap
    (T : K ⟶ K) (n : ℕ)
    (hT : ModuleEndomorphism.IsLocallyNilpotent
      (HomologicalComplex.cyclesMap T n)) :
    ModuleEndomorphism.IsLocallyNilpotent
      (HomologicalComplex.homologyMap T n) := by
  intro x
  obtain ⟨z, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (K.homologyπ n)).1 inferInstance x
  obtain ⟨k, hk⟩ := hT z
  refine ⟨k, ?_⟩
  have hiterate : ∀ (j : ℕ) (w : K.cycles n),
      ((HomologicalComplex.homologyMap T n)^[j]) (K.homologyπ n w) =
        K.homologyπ n (((HomologicalComplex.cyclesMap T n)^[j]) w) := by
    intro j
    induction j with
    | zero => intro w; rfl
    | succ j ih =>
        intro w
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
        rw [show HomologicalComplex.homologyMap T n (K.homologyπ n w) =
            K.homologyπ n (HomologicalComplex.cyclesMap T n w) by
          exact DFunLike.congr_fun
            (congrArg ModuleCat.Hom.hom
              (HomologicalComplex.homologyπ_naturality (φ := T) (i := n))) w]
        exact ih _
  rw [hiterate, hk, map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.locallyNilpotent_homologyMap_of_cyclesMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.locallyNilpotent_homologyMap_of_cyclesMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.locallyNilpotent_homologyMap_of_cyclesMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.locallyNilpotent_homologyMap_of_cyclesMap

theorem locallyNilpotent_homologyMap_of_f
    (T : K ⟶ K) (n : ℕ)
    (hT : ModuleEndomorphism.IsLocallyNilpotent (T.f n)) :
    ModuleEndomorphism.IsLocallyNilpotent
      (HomologicalComplex.homologyMap T n) :=
  locallyNilpotent_homologyMap_of_cyclesMap T n
    (locallyNilpotent_cyclesMap_of_f T n hT)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.locallyNilpotent_homologyMap_of_f then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.locallyNilpotent_homologyMap_of_f"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.locallyNilpotent_homologyMap_of_f ``Submission.DifferentialGeometry.Topology.SphereSeparation.locallyNilpotent_homologyMap_of_f

theorem exactAt_of_homotopic_id_of_locallyNilpotent
    (T : K ⟶ K) (h : _root_.Homotopy T (𝟙 K)) (n : ℕ)
    (hT : ModuleEndomorphism.IsLocallyNilpotent (T.f n)) :
    K.ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun x y ↦ ?_⟩
  have hmap : HomologicalComplex.homologyMap T n = 𝟙 _ := by
    simpa using h.homologyMap_eq n
  have hnil := locallyNilpotent_homologyMap_of_f T n hT
  have hx : x = 0 := by
    obtain ⟨k, hk⟩ := hnil x
    simpa [hmap] using hk
  have hy : y = 0 := by
    obtain ⟨k, hk⟩ := hnil y
    simpa [hmap] using hk
  rw [hx, hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exactAt_of_homotopic_id_of_locallyNilpotent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exactAt_of_homotopic_id_of_locallyNilpotent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exactAt_of_homotopic_id_of_locallyNilpotent ``Submission.DifferentialGeometry.Topology.SphereSeparation.exactAt_of_homotopic_id_of_locallyNilpotent

theorem exact_of_homotopic_id_of_degreewiseLocallyNilpotent
    (T : K ⟶ K) (h : _root_.Homotopy T (𝟙 K))
    (hT : ∀ n : ℕ, ModuleEndomorphism.IsLocallyNilpotent (T.f n)) :
    ∀ n : ℕ, K.ExactAt n :=
  fun n ↦ exactAt_of_homotopic_id_of_locallyNilpotent T h n (hT n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exact_of_homotopic_id_of_degreewiseLocallyNilpotent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exact_of_homotopic_id_of_degreewiseLocallyNilpotent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exact_of_homotopic_id_of_degreewiseLocallyNilpotent ``Submission.DifferentialGeometry.Topology.SphereSeparation.exact_of_homotopic_id_of_degreewiseLocallyNilpotent



noncomputable def chainCokernelSequence
    {A B : ChainComplex (ModuleCat R) ℕ} (i : A ⟶ B) :
    ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk i (cokernel.π i) (cokernel.condition i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.chainCokernelSequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.chainCokernelSequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.chainCokernelSequence ``Submission.DifferentialGeometry.Topology.SphereSeparation.chainCokernelSequence

theorem chainCokernelSequence_shortExact
    {A B : ChainComplex (ModuleCat R) ℕ} (i : A ⟶ B) [_root_.CategoryTheory.Mono i] :
    (chainCokernelSequence i).ShortExact := by
  change (ShortComplex.cokernelSequence i).ShortExact
  apply ShortComplex.ShortExact.mk'
  · exact ShortComplex.cokernelSequence_exact i
  · change _root_.CategoryTheory.Mono i
    infer_instance
  · infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.chainCokernelSequence_shortExact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.chainCokernelSequence_shortExact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.chainCokernelSequence_shortExact ``Submission.DifferentialGeometry.Topology.SphereSeparation.chainCokernelSequence_shortExact

noncomputable def chainCokernelEndomorphism
    {A B : ChainComplex (ModuleCat R) ℕ} (i : A ⟶ B)
    (TA : A ⟶ A) (TB : B ⟶ B) (h : i ≫ TB = TA ≫ i) :
    cokernel i ⟶ _root_.CategoryTheory.Limits.cokernel i :=
  cokernel.map i i TA TB h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.chainCokernelEndomorphism then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.chainCokernelEndomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.chainCokernelEndomorphism ``Submission.DifferentialGeometry.Topology.SphereSeparation.chainCokernelEndomorphism

@[reassoc (attr := simp)]
theorem chainCokernelProjection_naturality
    {A B : ChainComplex (ModuleCat R) ℕ} (i : A ⟶ B)
    (TA : A ⟶ A) (TB : B ⟶ B) (h : i ≫ TB = TA ≫ i) :
    cokernel.π i ≫ chainCokernelEndomorphism i TA TB h =
      TB ≫ cokernel.π i := by
  simp [chainCokernelEndomorphism]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.chainCokernelProjection_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.chainCokernelProjection_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.chainCokernelProjection_naturality ``Submission.DifferentialGeometry.Topology.SphereSeparation.chainCokernelProjection_naturality

theorem locallyNilpotent_chainCokernelEndomorphism
    {A B : ChainComplex (ModuleCat R) ℕ} (i : A ⟶ B)
    (TA : A ⟶ A) (TB : B ⟶ B) (h : i ≫ TB = TA ≫ i)
    (n : ℕ)
    (heventual : ∀ x : B.X n, ∃ k : ℕ,
      (cokernel.π i).f n (((TB.f n)^[k]) x) = 0) :
    ModuleEndomorphism.IsLocallyNilpotent
      ((chainCokernelEndomorphism i TA TB h).f n) := by
  intro y
  obtain ⟨x, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((cokernel.π i).f n)).1 inferInstance y
  obtain ⟨k, hk⟩ := heventual x
  refine ⟨k, ?_⟩
  have hbase : ∀ w : B.X n,
      (chainCokernelEndomorphism i TA TB h).f n ((cokernel.π i).f n w) =
        (cokernel.π i).f n (TB.f n w) := by
    intro w
    exact DFunLike.congr_fun
      (congrArg ModuleCat.Hom.hom
        (HomologicalComplex.congr_hom
          (chainCokernelProjection_naturality i TA TB h) n)) w
  have hiterate : ∀ (j : ℕ) (w : B.X n),
      (((chainCokernelEndomorphism i TA TB h).f n)^[j])
          ((cokernel.π i).f n w) =
        (cokernel.π i).f n (((TB.f n)^[j]) w) := by
    intro j
    induction j with
    | zero => intro w; rfl
    | succ j ih =>
        intro w
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
          hbase, ih]
  rw [hiterate, hk]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.locallyNilpotent_chainCokernelEndomorphism then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.locallyNilpotent_chainCokernelEndomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.locallyNilpotent_chainCokernelEndomorphism ``Submission.DifferentialGeometry.Topology.SphereSeparation.locallyNilpotent_chainCokernelEndomorphism

theorem quasiIso_of_cokernel_acyclic
    {A B : ChainComplex (ModuleCat R) ℕ} (i : A ⟶ B) [_root_.CategoryTheory.Mono i]
    (hQ : ∀ n : ℕ, (_root_.CategoryTheory.Limits.cokernel i).ExactAt n) :
    QuasiIso i := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hmono : _root_.CategoryTheory.Mono (HomologicalComplex.homologyMap i n) := by
    have hzero := (hQ (n + 1)).isZero_homology
    apply ((chainCokernelSequence_shortExact i).homology_exact₁
      (n + 1) n (by simp)).mono_g
    exact hzero.eq_of_src _ _
  have hepi : _root_.CategoryTheory.Epi (HomologicalComplex.homologyMap i n) := by
    have hzero := (hQ n).isZero_homology
    apply ((chainCokernelSequence_shortExact i).homology_exact₂ n).epi_f
    exact hzero.eq_of_tgt _ _
  let _ : _root_.CategoryTheory.Mono (HomologicalComplex.homologyMap i n) := hmono
  let _ : _root_.CategoryTheory.Epi (HomologicalComplex.homologyMap i n) := hepi
  exact _root_.CategoryTheory.isIso_of_mono_of_epi _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.quasiIso_of_cokernel_acyclic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.quasiIso_of_cokernel_acyclic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.quasiIso_of_cokernel_acyclic ``Submission.DifferentialGeometry.Topology.SphereSeparation.quasiIso_of_cokernel_acyclic

theorem quasiIso_of_cokernel_locallyNilpotent_homotopic_id
    {A B : ChainComplex (ModuleCat R) ℕ} (i : A ⟶ B) [_root_.CategoryTheory.Mono i]
    (T : _root_.CategoryTheory.Limits.cokernel i ⟶ _root_.CategoryTheory.Limits.cokernel i)
    (h : _root_.Homotopy T (𝟙 (_root_.CategoryTheory.Limits.cokernel i)))
    (hT : ∀ n : ℕ, ModuleEndomorphism.IsLocallyNilpotent (T.f n)) :
    QuasiIso i :=
  quasiIso_of_cokernel_acyclic i
    (exact_of_homotopic_id_of_degreewiseLocallyNilpotent T h hT)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.quasiIso_of_cokernel_locallyNilpotent_homotopic_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.quasiIso_of_cokernel_locallyNilpotent_homotopic_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.quasiIso_of_cokernel_locallyNilpotent_homotopic_id ``Submission.DifferentialGeometry.Topology.SphereSeparation.quasiIso_of_cokernel_locallyNilpotent_homotopic_id

theorem quasiIso_of_cokernelSubdivision_eventually_zero
    {A B : ChainComplex (ModuleCat R) ℕ} (i : A ⟶ B) [_root_.CategoryTheory.Mono i]
    (TA : A ⟶ A) (TB : B ⟶ B) (hcomm : i ≫ TB = TA ≫ i)
    (hhom : _root_.Homotopy
      (chainCokernelEndomorphism i TA TB hcomm) (𝟙 (_root_.CategoryTheory.Limits.cokernel i)))
    (heventual : ∀ (n : ℕ) (x : B.X n), ∃ k : ℕ,
      (cokernel.π i).f n (((TB.f n)^[k]) x) = 0) :
    QuasiIso i :=
  quasiIso_of_cokernel_locallyNilpotent_homotopic_id i
    (chainCokernelEndomorphism i TA TB hcomm) hhom
    (fun n ↦ locallyNilpotent_chainCokernelEndomorphism
      i TA TB hcomm n (heventual n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.quasiIso_of_cokernelSubdivision_eventually_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.quasiIso_of_cokernelSubdivision_eventually_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.quasiIso_of_cokernelSubdivision_eventually_zero ``Submission.DifferentialGeometry.Topology.SphereSeparation.quasiIso_of_cokernelSubdivision_eventually_zero

end DifferentialGeometry.Topology.SphereSeparation
