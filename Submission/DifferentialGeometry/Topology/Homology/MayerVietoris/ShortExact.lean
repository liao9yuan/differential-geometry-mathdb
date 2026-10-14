import Submission.DifferentialGeometry.Topology.Homology.SingularPair
import Mathlib.CategoryTheory.Abelian.CommSq

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.Submission.CategoryTheory _root_.CategoryTheory.Limits _root_.Submission.CategoryTheory.Limits _root_.Simplicial _root_.Opposite _root_.HomologicalComplex _root_.Submission.HomologicalComplex

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

section CokerIso

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  {X₁ X₂ X₃ X₄ : C} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
  {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

def pushoutCokernelIso (h : _root_.CategoryTheory.IsPushout t l r b)
    {cl : _root_.CategoryTheory.Limits.CokernelCofork l} (hl : _root_.CategoryTheory.Limits.IsColimit cl)
    {cr : _root_.CategoryTheory.Limits.CokernelCofork r} (hr : _root_.CategoryTheory.Limits.IsColimit cr) :
    cl.pt ≅ cr.pt where
  hom := Cofork.IsColimit.desc hl (b ≫ cr.π) (by
    rw [← Category.assoc, ← h.w, Category.assoc, cr.condition, _root_.CategoryTheory.Limits.comp_zero, _root_.CategoryTheory.Limits.zero_comp])
  inv := Cofork.IsColimit.desc hr (h.desc 0 cl.π (by simp [cl.condition]))
    (by simp [_root_.CategoryTheory.Limits.zero_comp])
  hom_inv_id := by
    apply Cofork.IsColimit.hom_ext hl
    simp
  inv_hom_id := by
    apply Cofork.IsColimit.hom_ext hr
    apply h.hom_ext
    · simp
    · simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.pushoutCokernelIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.pushoutCokernelIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.pushoutCokernelIso ``Submission.DifferentialGeometry.Topology.SingularPair.pushoutCokernelIso

@[reassoc (attr := simp)]
lemma π_pushoutCokernelIso_hom (h : _root_.CategoryTheory.IsPushout t l r b)
    {cl : _root_.CategoryTheory.Limits.CokernelCofork l} (hl : _root_.CategoryTheory.Limits.IsColimit cl)
    {cr : _root_.CategoryTheory.Limits.CokernelCofork r} (hr : _root_.CategoryTheory.Limits.IsColimit cr) :
    cl.π ≫ (pushoutCokernelIso h hl hr).hom = b ≫ cr.π := by
  simp [pushoutCokernelIso]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.π_pushoutCokernelIso_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.π_pushoutCokernelIso_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.π_pushoutCokernelIso_hom ``Submission.DifferentialGeometry.Topology.SingularPair.π_pushoutCokernelIso_hom

@[reassoc (attr := simp)]
lemma π_pushoutCokernelIso_inv (h : _root_.CategoryTheory.IsPushout t l r b)
    {cl : _root_.CategoryTheory.Limits.CokernelCofork l} (hl : _root_.CategoryTheory.Limits.IsColimit cl)
    {cr : _root_.CategoryTheory.Limits.CokernelCofork r} (hr : _root_.CategoryTheory.Limits.IsColimit cr) :
    b ≫ cr.π ≫ (pushoutCokernelIso h hl hr).inv = cl.π := by
  simp [pushoutCokernelIso]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.π_pushoutCokernelIso_inv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.π_pushoutCokernelIso_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.π_pushoutCokernelIso_inv ``Submission.DifferentialGeometry.Topology.SingularPair.π_pushoutCokernelIso_inv

end CokerIso

variable {K : SSet.{u}} (A B : K.Subcomplex) (R : ModuleCat.{u} ℤ)

lemma bicartSq : SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) where
  sup_eq := rfl
  inf_eq := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.bicartSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.bicartSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.bicartSq ``Submission.DifferentialGeometry.Topology.SingularPair.bicartSq

lemma isPushout_sset :
    _root_.CategoryTheory.IsPushout (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))
      (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))
      (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B))
      (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B)) :=
  (bicartSq A B).isPushout

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isPushout_sset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isPushout_sset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isPushout_sset ``Submission.DifferentialGeometry.Topology.SingularPair.isPushout_sset

abbrev ι₁ :
    ((A ⊓ B : K.Subcomplex) : SSet.{u}).chainComplex R ⟶ (A : SSet.{u}).chainComplex R :=
  SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι₁ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι₁"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι₁ ``Submission.DifferentialGeometry.Topology.SingularPair.ι₁

abbrev ι₂ :
    ((A ⊓ B : K.Subcomplex) : SSet.{u}).chainComplex R ⟶ (B : SSet.{u}).chainComplex R :=
  SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι₂ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι₂"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι₂ ``Submission.DifferentialGeometry.Topology.SingularPair.ι₂

abbrev j₁ :
    (A : SSet.{u}).chainComplex R ⟶ ((A ⊔ B : K.Subcomplex) : SSet.{u}).chainComplex R :=
  SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B)) R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.j₁ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.j₁"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.j₁ ``Submission.DifferentialGeometry.Topology.SingularPair.j₁

abbrev j₂ :
    (B : SSet.{u}).chainComplex R ⟶ ((A ⊔ B : K.Subcomplex) : SSet.{u}).chainComplex R :=
  SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B)) R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.j₂ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.j₂"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.j₂ ``Submission.DifferentialGeometry.Topology.SingularPair.j₂

lemma isPushout_X (n : ℕ) :
    IsPushout ((ι₁ A B R).f n) ((ι₂ A B R).f n) ((j₁ A B R).f n) ((j₂ A B R).f n) :=
  ((isPushout_sset A B).map ((_root_.CategoryTheory.evaluation _ _).obj (_root_.Opposite.op ⦋n⦌))).map (sigmaConst.obj R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isPushout_X then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isPushout_X"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isPushout_X ``Submission.DifferentialGeometry.Topology.SingularPair.isPushout_X

@[reassoc (attr := simp)]
lemma ι₁_j₁ : ι₁ A B R ≫ j₁ A B R = ι₂ A B R ≫ j₂ A B R := by
  simp only [ι₁, j₁, ι₂, j₂, ← Functor.map_comp]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι₁_j₁ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι₁_j₁"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι₁_j₁ ``Submission.DifferentialGeometry.Topology.SingularPair.ι₁_j₁

lemma isPushout : _root_.CategoryTheory.IsPushout (ι₁ A B R) (ι₂ A B R) (j₁ A B R) (j₂ A B R) where
  w := ι₁_j₁ A B R
  isColimit' := ⟨isColimitOfEval _ _ (fun n ↦
    (PushoutCocone.isColimitMapCoconeEquiv _ _).2 (isPushout_X A B R n).isColimit)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isPushout then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isPushout"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isPushout ``Submission.DifferentialGeometry.Topology.SingularPair.isPushout

instance _root_.Submission.DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatι₁ : _root_.CategoryTheory.Mono (ι₁ A B R) :=
  inferInstanceAs (_root_.CategoryTheory.Mono (SSet.chainComplexMap
    (SSetPair.of (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))).hom R))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatι₁ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatι₁"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatι₁ ``Submission.DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatι₁

instance _root_.Submission.DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatι₂ : _root_.CategoryTheory.Mono (ι₂ A B R) :=
  inferInstanceAs (_root_.CategoryTheory.Mono (SSet.chainComplexMap
    (SSetPair.of (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))).hom R))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatι₂ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatι₂"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatι₂ ``Submission.DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatι₂

instance _root_.Submission.DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatJ₁ : _root_.CategoryTheory.Mono (j₁ A B R) :=
  inferInstanceAs (_root_.CategoryTheory.Mono (SSet.chainComplexMap
    (SSetPair.of (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B))).hom R))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatJ₁ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatJ₁"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatJ₁ ``Submission.DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatJ₁

instance _root_.Submission.DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatJ₂ : _root_.CategoryTheory.Mono (j₂ A B R) :=
  inferInstanceAs (_root_.CategoryTheory.Mono (SSet.chainComplexMap
    (SSetPair.of (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B))).hom R))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatJ₂ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatJ₂"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatJ₂ ``Submission.DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatJ₂

@[reassoc]
lemma lift_desc :
    biprod.lift (ι₁ A B R) (-(ι₂ A B R)) ≫ biprod.desc (j₁ A B R) (j₂ A B R) = 0 := by
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.lift_desc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.lift_desc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.lift_desc ``Submission.DifferentialGeometry.Topology.SingularPair.lift_desc

def mvShortComplex : _root_.CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (biprod.lift (ι₁ A B R) (-(ι₂ A B R)))
    (biprod.desc (j₁ A B R) (j₂ A B R)) (lift_desc A B R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvShortComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvShortComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvShortComplex ``Submission.DifferentialGeometry.Topology.SingularPair.mvShortComplex

lemma mvShortComplex_eq : mvShortComplex A B R = (isPushout A B R).shortComplex := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvShortComplex_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvShortComplex_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvShortComplex_eq ``Submission.DifferentialGeometry.Topology.SingularPair.mvShortComplex_eq

@[simp] lemma mvShortComplex_X₁ :
    (mvShortComplex A B R).X₁ = ((A ⊓ B : K.Subcomplex) : SSet.{u}).chainComplex R := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvShortComplex_X₁ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvShortComplex_X₁"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvShortComplex_X₁ ``Submission.DifferentialGeometry.Topology.SingularPair.mvShortComplex_X₁

@[simp] lemma mvShortComplex_X₂ :
    (mvShortComplex A B R).X₂ =
      ((A : SSet.{u}).chainComplex R ⊞ (B : SSet.{u}).chainComplex R) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvShortComplex_X₂ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvShortComplex_X₂"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvShortComplex_X₂ ``Submission.DifferentialGeometry.Topology.SingularPair.mvShortComplex_X₂

@[simp] lemma mvShortComplex_X₃ :
    (mvShortComplex A B R).X₃ = ((A ⊔ B : K.Subcomplex) : SSet.{u}).chainComplex R := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvShortComplex_X₃ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvShortComplex_X₃"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvShortComplex_X₃ ``Submission.DifferentialGeometry.Topology.SingularPair.mvShortComplex_X₃

@[simp] lemma mvShortComplex_f :
    (mvShortComplex A B R).f = biprod.lift (ι₁ A B R) (-(ι₂ A B R)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvShortComplex_f then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvShortComplex_f"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvShortComplex_f ``Submission.DifferentialGeometry.Topology.SingularPair.mvShortComplex_f

@[simp] lemma mvShortComplex_g :
    (mvShortComplex A B R).g = biprod.desc (j₁ A B R) (j₂ A B R) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvShortComplex_g then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvShortComplex_g"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvShortComplex_g ``Submission.DifferentialGeometry.Topology.SingularPair.mvShortComplex_g

theorem mvShortComplex_shortExact : (mvShortComplex A B R).ShortExact where
  exact := (isPushout A B R).exact_shortComplex
  mono_f := by
    dsimp [mvShortComplex]
    exact _root_.CategoryTheory.mono_of_mono_fac (biprod.lift_fst _ _)
  epi_g := (isPushout A B R).epi_shortComplex_g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvShortComplex_shortExact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvShortComplex_shortExact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvShortComplex_shortExact ``Submission.DifferentialGeometry.Topology.SingularPair.mvShortComplex_shortExact

def mvδ (n : ℕ) :
    ((A ⊔ B : K.Subcomplex) : SSet.{u}).homology R (n + 1) ⟶
      ((A ⊓ B : K.Subcomplex) : SSet.{u}).homology R n :=
  (mvShortComplex_shortExact A B R).δ (n + 1) n rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvδ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvδ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvδ ``Submission.DifferentialGeometry.Topology.SingularPair.mvδ

@[reassoc (attr := simp)]
lemma mvδ_comp (n : ℕ) :
    mvδ A B R n ≫ _root_.HomologicalComplex.homologyMap (biprod.lift (ι₁ A B R) (-(ι₂ A B R))) n = 0 :=
  (mvShortComplex_shortExact A B R).δ_comp (n + 1) n rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvδ_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvδ_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvδ_comp ``Submission.DifferentialGeometry.Topology.SingularPair.mvδ_comp

@[reassoc (attr := simp)]
lemma comp_mvδ (n : ℕ) :
    homologyMap (biprod.desc (j₁ A B R) (j₂ A B R)) (n + 1) ≫ mvδ A B R n = 0 :=
  (mvShortComplex_shortExact A B R).comp_δ (n + 1) n rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.comp_mvδ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.comp_mvδ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.comp_mvδ ``Submission.DifferentialGeometry.Topology.SingularPair.comp_mvδ

lemma homologyMap_lift_desc (n : ℕ) :
    _root_.HomologicalComplex.homologyMap (biprod.lift (ι₁ A B R) (-(ι₂ A B R))) n ≫
      homologyMap (biprod.desc (j₁ A B R) (j₂ A B R)) n = 0 := by
  rw [← _root_.HomologicalComplex.homologyMap_comp, lift_desc, _root_.HomologicalComplex.homologyMap_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homologyMap_lift_desc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homologyMap_lift_desc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homologyMap_lift_desc ``Submission.DifferentialGeometry.Topology.SingularPair.homologyMap_lift_desc

theorem mv_exact₁ (n : ℕ) :
    (ShortComplex.mk (mvδ A B R n) (_root_.HomologicalComplex.homologyMap (biprod.lift (ι₁ A B R) (-(ι₂ A B R))) n)
      (mvδ_comp A B R n)).Exact :=
  (mvShortComplex_shortExact A B R).homology_exact₁ (n + 1) n rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mv_exact₁ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mv_exact₁"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mv_exact₁ ``Submission.DifferentialGeometry.Topology.SingularPair.mv_exact₁

theorem mv_exact₂ (n : ℕ) :
    (ShortComplex.mk (_root_.HomologicalComplex.homologyMap (biprod.lift (ι₁ A B R) (-(ι₂ A B R))) n)
      (_root_.HomologicalComplex.homologyMap (biprod.desc (j₁ A B R) (j₂ A B R)) n)
      (homologyMap_lift_desc A B R n)).Exact :=
  (mvShortComplex_shortExact A B R).homology_exact₂ n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mv_exact₂ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mv_exact₂"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mv_exact₂ ``Submission.DifferentialGeometry.Topology.SingularPair.mv_exact₂

theorem mv_exact₃ (n : ℕ) :
    (ShortComplex.mk (_root_.HomologicalComplex.homologyMap (biprod.desc (j₁ A B R) (j₂ A B R)) (n + 1)) (mvδ A B R n)
      (comp_mvδ A B R n)).Exact :=
  (mvShortComplex_shortExact A B R).homology_exact₃ (n + 1) n rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mv_exact₃ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mv_exact₃"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mv_exact₃ ``Submission.DifferentialGeometry.Topology.SingularPair.mv_exact₃

def homologyBiprodIso (n : ℕ) :
    ((A : SSet.{u}).chainComplex R ⊞ (B : SSet.{u}).chainComplex R).homology n ≅
      ((A : SSet.{u}).homology R n ⊞ (B : SSet.{u}).homology R n) where
  hom := biprod.lift (_root_.HomologicalComplex.homologyMap biprod.fst n) (_root_.HomologicalComplex.homologyMap biprod.snd n)
  inv := biprod.desc (_root_.HomologicalComplex.homologyMap biprod.inl n) (_root_.HomologicalComplex.homologyMap biprod.inr n)
  hom_inv_id := by
    rw [biprod.lift_desc, ← _root_.HomologicalComplex.homologyMap_comp, ← _root_.HomologicalComplex.homologyMap_comp, ← _root_.HomologicalComplex.homologyMap_add,
      biprod.total, _root_.HomologicalComplex.homologyMap_id]
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp [← _root_.HomologicalComplex.homologyMap_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homologyBiprodIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homologyBiprodIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homologyBiprodIso ``Submission.DifferentialGeometry.Topology.SingularPair.homologyBiprodIso

def mvLift (n : ℕ) :
    ((A ⊓ B : K.Subcomplex) : SSet.{u}).homology R n ⟶
      ((A : SSet.{u}).homology R n ⊞ (B : SSet.{u}).homology R n) :=
  biprod.lift (SSet.homologyMap (SSet.Subcomplex.homOfLE inf_le_left) R n)
    (-(SSet.homologyMap (SSet.Subcomplex.homOfLE inf_le_right) R n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvLift ``Submission.DifferentialGeometry.Topology.SingularPair.mvLift

def mvDesc (n : ℕ) :
    ((A : SSet.{u}).homology R n ⊞ (B : SSet.{u}).homology R n) ⟶
      ((A ⊔ B : K.Subcomplex) : SSet.{u}).homology R n :=
  biprod.desc (SSet.homologyMap (SSet.Subcomplex.homOfLE le_sup_left) R n)
    (SSet.homologyMap (SSet.Subcomplex.homOfLE le_sup_right) R n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvDesc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvDesc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvDesc ``Submission.DifferentialGeometry.Topology.SingularPair.mvDesc

@[simp]
lemma mvLift_fst (n : ℕ) :
    mvLift A B R n ≫ biprod.fst =
      SSet.homologyMap (SSet.Subcomplex.homOfLE inf_le_left) R n :=
  biprod.lift_fst _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvLift_fst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvLift_fst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvLift_fst ``Submission.DifferentialGeometry.Topology.SingularPair.mvLift_fst

@[simp]
lemma mvLift_snd (n : ℕ) :
    mvLift A B R n ≫ biprod.snd =
      -SSet.homologyMap (SSet.Subcomplex.homOfLE inf_le_right) R n :=
  biprod.lift_snd _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvLift_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvLift_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvLift_snd ``Submission.DifferentialGeometry.Topology.SingularPair.mvLift_snd

@[simp]
lemma inl_mvDesc (n : ℕ) :
    biprod.inl ≫ mvDesc A B R n =
      SSet.homologyMap (SSet.Subcomplex.homOfLE le_sup_left) R n :=
  biprod.inl_desc _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.inl_mvDesc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.inl_mvDesc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.inl_mvDesc ``Submission.DifferentialGeometry.Topology.SingularPair.inl_mvDesc

@[simp]
lemma inr_mvDesc (n : ℕ) :
    biprod.inr ≫ mvDesc A B R n =
      SSet.homologyMap (SSet.Subcomplex.homOfLE le_sup_right) R n :=
  biprod.inr_desc _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.inr_mvDesc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.inr_mvDesc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.inr_mvDesc ``Submission.DifferentialGeometry.Topology.SingularPair.inr_mvDesc

lemma homologyMap_lift_homologyBiprodIso_hom (n : ℕ) :
    _root_.HomologicalComplex.homologyMap (biprod.lift (ι₁ A B R) (-(ι₂ A B R))) n ≫ (homologyBiprodIso A B R n).hom =
      mvLift A B R n := by
  dsimp only [homologyBiprodIso, mvLift]
  apply biprod.hom_ext
  · simp [← _root_.HomologicalComplex.homologyMap_comp]
  · simp [← _root_.HomologicalComplex.homologyMap_comp, _root_.HomologicalComplex.homologyMap_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homologyMap_lift_homologyBiprodIso_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homologyMap_lift_homologyBiprodIso_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homologyMap_lift_homologyBiprodIso_hom ``Submission.DifferentialGeometry.Topology.SingularPair.homologyMap_lift_homologyBiprodIso_hom

lemma homologyBiprodIso_inv_homologyMap_desc (n : ℕ) :
    (homologyBiprodIso A B R n).inv ≫ _root_.HomologicalComplex.homologyMap (biprod.desc (j₁ A B R) (j₂ A B R)) n =
      mvDesc A B R n := by
  dsimp only [homologyBiprodIso, mvDesc]
  apply biprod.hom_ext'
  · simp [← _root_.HomologicalComplex.homologyMap_comp]
  · simp [← _root_.HomologicalComplex.homologyMap_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homologyBiprodIso_inv_homologyMap_desc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homologyBiprodIso_inv_homologyMap_desc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homologyBiprodIso_inv_homologyMap_desc ``Submission.DifferentialGeometry.Topology.SingularPair.homologyBiprodIso_inv_homologyMap_desc

@[reassoc (attr := simp)]
lemma mvδ_mvLift (n : ℕ) : mvδ A B R n ≫ mvLift A B R n = 0 := by
  rw [← homologyMap_lift_homologyBiprodIso_hom, mvδ_comp_assoc, _root_.CategoryTheory.Limits.zero_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvδ_mvLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvδ_mvLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvδ_mvLift ``Submission.DifferentialGeometry.Topology.SingularPair.mvδ_mvLift

@[reassoc (attr := simp)]
lemma mvLift_mvDesc (n : ℕ) : mvLift A B R n ≫ mvDesc A B R n = 0 := by
  rw [← homologyMap_lift_homologyBiprodIso_hom, ← homologyBiprodIso_inv_homologyMap_desc,
    Category.assoc, Iso.hom_inv_id_assoc, homologyMap_lift_desc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvLift_mvDesc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvLift_mvDesc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvLift_mvDesc ``Submission.DifferentialGeometry.Topology.SingularPair.mvLift_mvDesc

@[reassoc (attr := simp)]
lemma mvDesc_mvδ (n : ℕ) : mvDesc A B R (n + 1) ≫ mvδ A B R n = 0 := by
  rw [← homologyBiprodIso_inv_homologyMap_desc, Category.assoc, comp_mvδ, _root_.CategoryTheory.Limits.comp_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvDesc_mvδ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvDesc_mvδ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvDesc_mvδ ``Submission.DifferentialGeometry.Topology.SingularPair.mvDesc_mvδ

theorem mv_exact₁' (n : ℕ) :
    (ShortComplex.mk (mvδ A B R n) (mvLift A B R n) (mvδ_mvLift A B R n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mv_exact₁ A B R n)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (homologyBiprodIso A B R n)
    (by simp) (by simp [homologyMap_lift_homologyBiprodIso_hom])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mv_exact₁' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mv_exact₁'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mv_exact₁' ``Submission.DifferentialGeometry.Topology.SingularPair.mv_exact₁'

theorem mv_exact₂' (n : ℕ) :
    (ShortComplex.mk (mvLift A B R n) (mvDesc A B R n) (mvLift_mvDesc A B R n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mv_exact₂ A B R n)
  exact ShortComplex.isoMk (Iso.refl _) (homologyBiprodIso A B R n) (Iso.refl _)
    (by simp [homologyMap_lift_homologyBiprodIso_hom])
    (by simp [← homologyBiprodIso_inv_homologyMap_desc])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mv_exact₂' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mv_exact₂'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mv_exact₂' ``Submission.DifferentialGeometry.Topology.SingularPair.mv_exact₂'

theorem mv_exact₃' (n : ℕ) :
    (ShortComplex.mk (mvDesc A B R (n + 1)) (mvδ A B R n) (mvDesc_mvδ A B R n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mv_exact₃ A B R n)
  exact ShortComplex.isoMk (homologyBiprodIso A B R (n + 1)) (Iso.refl _) (Iso.refl _)
    (by simp [← homologyBiprodIso_inv_homologyMap_desc]) (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mv_exact₃' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mv_exact₃'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mv_exact₃' ``Submission.DifferentialGeometry.Topology.SingularPair.mv_exact₃'

abbrev pairSup : SSetPair.{u} :=
  SSetPair.of (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.pairSup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.pairSup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.pairSup ``Submission.DifferentialGeometry.Topology.SingularPair.pairSup

abbrev pairInf : SSetPair.{u} :=
  SSetPair.of (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.pairInf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.pairInf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.pairInf ``Submission.DifferentialGeometry.Topology.SingularPair.pairInf

def cokerIso : (pairInf A B).chainComplex R ≅ (pairSup A B).chainComplex R :=
  pushoutCokernelIso (isPushout A B R) ((pairInf A B).isColimitCokernelCoforkChainComplex R)
    ((pairSup A B).isColimitCokernelCoforkChainComplex R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.cokerIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.cokerIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.cokerIso ``Submission.DifferentialGeometry.Topology.SingularPair.cokerIso

@[reassoc (attr := simp)]
lemma chainComplexπ_cokerIso_hom :
    (pairInf A B).chainComplexπ R ≫ (cokerIso A B R).hom =
      j₂ A B R ≫ (pairSup A B).chainComplexπ R :=
  π_pushoutCokernelIso_hom (isPushout A B R) _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.chainComplexπ_cokerIso_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.chainComplexπ_cokerIso_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.chainComplexπ_cokerIso_hom ``Submission.DifferentialGeometry.Topology.SingularPair.chainComplexπ_cokerIso_hom

def homologyCokerIso (n : ℕ) : (pairInf A B).homology R n ≅ (pairSup A B).homology R n :=
  _root_.HomologicalComplex.homologyMapIso (cokerIso A B R) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homologyCokerIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homologyCokerIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homologyCokerIso ``Submission.DifferentialGeometry.Topology.SingularPair.homologyCokerIso

@[reassoc]
lemma chainComplexMap_right_chainComplexπ {P P' : SSetPair.{u}} (φ : P ⟶ P') :
    SSet.chainComplexMap φ.right R ≫ P'.chainComplexπ R =
      P.chainComplexπ R ≫ SSetPair.chainComplexMap φ R :=
  ((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℤ)).app R).naturality φ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.chainComplexMap_right_chainComplexπ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.chainComplexMap_right_chainComplexπ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.chainComplexMap_right_chainComplexπ ``Submission.DifferentialGeometry.Topology.SingularPair.chainComplexMap_right_chainComplexπ

@[reassoc]
lemma homologyMap_right_homologyπ {P P' : SSetPair.{u}} (φ : P ⟶ P') (n : ℕ) :
    SSet.homologyMap φ.right R n ≫ P'.homologyπ R n =
      P.homologyπ R n ≫ SSetPair.homologyMap φ R n := by
  simp only [SSetPair.homologyπ, SSetPair.homologyMap, SSet.homologyMap, ← _root_.HomologicalComplex.homologyMap_comp,
    chainComplexMap_right_chainComplexπ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homologyMap_right_homologyπ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homologyMap_right_homologyπ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homologyMap_right_homologyπ ``Submission.DifferentialGeometry.Topology.SingularPair.homologyMap_right_homologyπ

def excisionPairMap : pairInf A B ⟶ pairSup A B :=
  SSetPair.homMk (SSet.Subcomplex.homOfLE inf_le_left) (SSet.Subcomplex.homOfLE le_sup_right)
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.excisionPairMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.excisionPairMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.excisionPairMap ``Submission.DifferentialGeometry.Topology.SingularPair.excisionPairMap

lemma excisionPairMap_right :
    (excisionPairMap A B).right = SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.excisionPairMap_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.excisionPairMap_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.excisionPairMap_right ``Submission.DifferentialGeometry.Topology.SingularPair.excisionPairMap_right

lemma excisionPairMap_left :
    (excisionPairMap A B).left = SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.excisionPairMap_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.excisionPairMap_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.excisionPairMap_left ``Submission.DifferentialGeometry.Topology.SingularPair.excisionPairMap_left

lemma chainComplexMap_excisionPairMap :
    SSetPair.chainComplexMap (excisionPairMap A B) R = (cokerIso A B R).hom := by
  apply Cofork.IsColimit.hom_ext ((pairInf A B).isColimitCokernelCoforkChainComplex R)
  dsimp only [SSetPair.cokernelCoforkChainComplex]
  rw [Cofork.π_ofπ, ← chainComplexMap_right_chainComplexπ, chainComplexπ_cokerIso_hom]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.chainComplexMap_excisionPairMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.chainComplexMap_excisionPairMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.chainComplexMap_excisionPairMap ``Submission.DifferentialGeometry.Topology.SingularPair.chainComplexMap_excisionPairMap

instance isIso_chainComplexMap_excisionPairMap :
    IsIso (SSetPair.chainComplexMap (excisionPairMap A B) R) := by
  rw [chainComplexMap_excisionPairMap]
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_chainComplexMap_excisionPairMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_chainComplexMap_excisionPairMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_chainComplexMap_excisionPairMap ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_chainComplexMap_excisionPairMap

lemma homologyMap_excisionPairMap (n : ℕ) :
    SSetPair.homologyMap (excisionPairMap A B) R n = (homologyCokerIso A B R n).hom := by
  simp only [SSetPair.homologyMap, chainComplexMap_excisionPairMap, homologyCokerIso,
    _root_.HomologicalComplex.homologyMapIso_hom]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homologyMap_excisionPairMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homologyMap_excisionPairMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homologyMap_excisionPairMap ``Submission.DifferentialGeometry.Topology.SingularPair.homologyMap_excisionPairMap

instance isIso_homologyMap_excisionPairMap (n : ℕ) :
    IsIso (SSetPair.homologyMap (excisionPairMap A B) R n) := by
  rw [homologyMap_excisionPairMap]
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_excisionPairMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_excisionPairMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_excisionPairMap ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_excisionPairMap

@[reassoc]
lemma homologyπ_homologyCokerIso_hom (n : ℕ) :
    (pairInf A B).homologyπ R n ≫ (homologyCokerIso A B R n).hom =
      SSet.homologyMap (excisionPairMap A B).right R n ≫ (pairSup A B).homologyπ R n := by
  rw [← homologyMap_excisionPairMap, homologyMap_right_homologyπ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homologyπ_homologyCokerIso_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homologyπ_homologyCokerIso_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homologyπ_homologyCokerIso_hom ``Submission.DifferentialGeometry.Topology.SingularPair.homologyπ_homologyCokerIso_hom

end DifferentialGeometry.Topology.SingularPair
