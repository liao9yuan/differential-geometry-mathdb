import Submission.DifferentialGeometry.Topology.Homology.Algebra.FiniteType
import Submission.DifferentialGeometry.Topology.Homology.EulerCharacteristic
import Mathlib.Topology.Category.TopCat.EpiMono

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology
noncomputable section
universe u

namespace DifferentialGeometry.Homology
variable (X : TopCat.{u}) (s : Set X) {k : Type u} [Ring k] (R : ModuleCat.{u} k)


def relativeInclusion :
    ((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj (TopCat.of s) ⟶
      ((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj X :=
  ((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map
    (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.relativeInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.relativeInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.relativeInclusion ``Submission.DifferentialGeometry.Homology.relativeInclusion

instance _root_.Submission.DifferentialGeometry.Homology.instMonoChainComplexModuleCatNatRelativeInclusion : _root_.CategoryTheory.Mono (relativeInclusion X s R) := by
  have : _root_.CategoryTheory.Mono (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X))) :=
    (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  unfold relativeInclusion
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.instMonoChainComplexModuleCatNatRelativeInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.instMonoChainComplexModuleCatNatRelativeInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.instMonoChainComplexModuleCatNatRelativeInclusion ``Submission.DifferentialGeometry.Homology.instMonoChainComplexModuleCatNatRelativeInclusion


def relativeChainComplex : ChainComplex (ModuleCat.{u} k) ℕ :=
  _root_.CategoryTheory.Limits.cokernel (relativeInclusion X s R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.relativeChainComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.relativeChainComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.relativeChainComplex ``Submission.DifferentialGeometry.Homology.relativeChainComplex


def relativeProjection :
    ((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj X ⟶
      relativeChainComplex X s R :=
  cokernel.π (relativeInclusion X s R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.relativeProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.relativeProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.relativeProjection ``Submission.DifferentialGeometry.Homology.relativeProjection


@[reassoc (attr := simp)]
theorem relativeInclusion_projection :
    relativeInclusion X s R ≫ relativeProjection X s R = 0 :=
  cokernel.condition _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.relativeInclusion_projection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.relativeInclusion_projection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.relativeInclusion_projection ``Submission.DifferentialGeometry.Homology.relativeInclusion_projection


def relativeShortComplex : _root_.CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk (relativeInclusion X s R) (relativeProjection X s R)
    (relativeInclusion_projection X s R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.relativeShortComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.relativeShortComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.relativeShortComplex ``Submission.DifferentialGeometry.Homology.relativeShortComplex


theorem relativeShortExact : (relativeShortComplex X s R).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (_root_.CategoryTheory.Limits.cokernelIsCokernel _)
  mono_f := inferInstanceAs (_root_.CategoryTheory.Mono (relativeInclusion X s R))
  epi_g := inferInstanceAs (_root_.CategoryTheory.Epi (cokernel.π (relativeInclusion X s R)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.relativeShortExact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.relativeShortExact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.relativeShortExact ``Submission.DifferentialGeometry.Homology.relativeShortExact

def relativeChainQuotientIso (n : ℕ) :
    (relativeChainComplex X s R).X n ≅
      ModuleCat.of k
        ((((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj X).X n ⧸
          LinearMap.range ((relativeInclusion X s R).f n).hom) :=
  PreservesCokernel.iso (_root_.HomologicalComplex.eval _ _ n) (relativeInclusion X s R) ≪≫
    ModuleCat.cokernelIsoRangeQuotient ((relativeInclusion X s R).f n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.relativeChainQuotientIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.relativeChainQuotientIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.relativeChainQuotientIso ``Submission.DifferentialGeometry.Homology.relativeChainQuotientIso

@[reassoc (attr := simp)]
theorem relativeProjection_quotientIso (n : ℕ) :
    (relativeProjection X s R).f n ≫ (relativeChainQuotientIso X s R n).hom =
      ModuleCat.ofHom (LinearMap.range ((relativeInclusion X s R).f n).hom).mkQ := by
  exact (PreservesCokernel.π_iso_hom_assoc
    (_root_.HomologicalComplex.eval _ _ n) (relativeInclusion X s R)
    (ModuleCat.cokernelIsoRangeQuotient
      ((_root_.HomologicalComplex.eval _ _ n).map (relativeInclusion X s R))).hom).trans
        (ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.relativeProjection_quotientIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.relativeProjection_quotientIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.relativeProjection_quotientIso ``Submission.DifferentialGeometry.Homology.relativeProjection_quotientIso


def relativeHomology (n : ℕ) : ModuleCat.{u} k :=
  (relativeChainComplex X s R).homology n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.relativeHomology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.relativeHomology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.relativeHomology ``Submission.DifferentialGeometry.Homology.relativeHomology


section CoefficientIso
variable {R' : ModuleCat.{u} k} (φ : R ≅ R')

def singularChainComplexCoefficientIso :
    (_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R ≅
      (_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R' :=
  (_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).mapIso φ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularChainComplexCoefficientIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularChainComplexCoefficientIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularChainComplexCoefficientIso ``Submission.DifferentialGeometry.Homology.singularChainComplexCoefficientIso

def relativeChainComplexCoefficientIso :
    relativeChainComplex X s R ≅ relativeChainComplex X s R' :=
  cokernel.mapIso (relativeInclusion X s R) (relativeInclusion X s R')
    ((singularChainComplexCoefficientIso (R := R) (R' := R') φ).app (TopCat.of s))
    ((singularChainComplexCoefficientIso (R := R) (R' := R') φ).app X)
    (NatTrans.naturality (singularChainComplexCoefficientIso (R := R) (R' := R') φ).hom
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.relativeChainComplexCoefficientIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.relativeChainComplexCoefficientIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.relativeChainComplexCoefficientIso ``Submission.DifferentialGeometry.Homology.relativeChainComplexCoefficientIso

def relativeHomologyCoefficientIso (n : ℕ) :
    relativeHomology X s R n ≅ relativeHomology X s R' n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) n).mapIso
    (relativeChainComplexCoefficientIso (X := X) (s := s) (R := R) (R' := R') φ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.relativeHomologyCoefficientIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.relativeHomologyCoefficientIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.relativeHomologyCoefficientIso ``Submission.DifferentialGeometry.Homology.relativeHomologyCoefficientIso

end CoefficientIso


def relativeConnecting (n : ℕ) :
    relativeHomology X s R (n + 1) ⟶
      ((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj R).obj (TopCat.of s) :=
  (relativeShortExact X s R).δ (n + 1) n rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.relativeConnecting then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.relativeConnecting"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.relativeConnecting ``Submission.DifferentialGeometry.Homology.relativeConnecting


theorem relative_homology_exact_subspace (n : ℕ) :
    (ShortComplex.mk (relativeConnecting X s R n)
      (_root_.HomologicalComplex.homologyMap (relativeInclusion X s R) n)
      ((relativeShortExact X s R).δ_comp (n + 1) n rfl)).Exact :=
  (relativeShortExact X s R).homology_exact₁ (n + 1) n rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.relative_homology_exact_subspace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.relative_homology_exact_subspace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.relative_homology_exact_subspace ``Submission.DifferentialGeometry.Homology.relative_homology_exact_subspace


theorem relative_homology_exact_absolute (n : ℕ) :
    ((relativeShortComplex X s R).map
      (_root_.HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) n)).Exact :=
  (relativeShortExact X s R).homology_exact₂ n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.relative_homology_exact_absolute then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.relative_homology_exact_absolute"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.relative_homology_exact_absolute ``Submission.DifferentialGeometry.Homology.relative_homology_exact_absolute


theorem relative_homology_exact_relative (n : ℕ) :
    (ShortComplex.mk (_root_.HomologicalComplex.homologyMap (relativeProjection X s R) (n + 1))
      (relativeConnecting X s R n)
      ((relativeShortExact X s R).comp_δ (n + 1) n rfl)).Exact :=
  (relativeShortExact X s R).homology_exact₃ (n + 1) n rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.relative_homology_exact_relative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.relative_homology_exact_relative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.relative_homology_exact_relative ``Submission.DifferentialGeometry.Homology.relative_homology_exact_relative

section Field
variable (k : Type u) [Field k]


theorem finiteHomologyType_relativeChainComplex
    (hs : finiteHomologyType k (TopCat.of s)) (hX : finiteHomologyType k X) :
    DifferentialGeometry.HomologicalComplex.finiteHomologyType (relativeChainComplex X s (ModuleCat.of k k)) :=
  DifferentialGeometry.HomologicalComplex.finiteHomologyType_last
    (relativeShortComplex X s (ModuleCat.of k k)) (relativeShortExact X s (ModuleCat.of k k)) hs hX

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.finiteHomologyType_relativeChainComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.finiteHomologyType_relativeChainComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.finiteHomologyType_relativeChainComplex ``Submission.DifferentialGeometry.Homology.finiteHomologyType_relativeChainComplex

def relativeEulerChar : ℤ :=
  (relativeChainComplex X s (ModuleCat.of k k)).homologyEulerChar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.relativeEulerChar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.relativeEulerChar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.relativeEulerChar ``Submission.DifferentialGeometry.Homology.relativeEulerChar

theorem relativeEulerChar_eq_sub
    (hs : finiteHomologyType k (TopCat.of s)) (hX : finiteHomologyType k X) :
    relativeEulerChar X s k = eulerChar k X - eulerChar k (TopCat.of s) := by
  let S := relativeShortComplex X s (ModuleCat.of k k)
  have hr := finiteHomologyType_relativeChainComplex X s k hs hX
  have : ∀ n, FiniteDimensional k (S.X₁.homology n) := hs.1
  have : ∀ n, FiniteDimensional k (S.X₂.homology n) := hX.1
  have : ∀ n, FiniteDimensional k (S.X₃.homology n) := hr.1
  have h := DifferentialGeometry.HomologicalComplex.homologyEulerChar_additive S
    (relativeShortExact X s (ModuleCat.of k k)) hs.2 hX.2 hr.2
  change eulerChar k X = eulerChar k (TopCat.of s) + relativeEulerChar X s k at h
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.relativeEulerChar_eq_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.relativeEulerChar_eq_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.relativeEulerChar_eq_sub ``Submission.DifferentialGeometry.Homology.relativeEulerChar_eq_sub

end Field
end DifferentialGeometry.Homology
