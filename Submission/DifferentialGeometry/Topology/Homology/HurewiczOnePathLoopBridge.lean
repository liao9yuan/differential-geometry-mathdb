import Submission.DifferentialGeometry.Topology.Homology.HurewiczOneAbelianization
import Submission.DifferentialGeometry.Topology.Homology.HurewiczTwoMultiplication
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.PathEvaluation
import Submission.DifferentialGeometry.Topology.Homology.SimplexBoundaryFilling
import Submission.DifferentialGeometry.Topology.Homotopy.CubeSphereProjection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module
open scoped _root_.Simplicial _root_.Topology

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]
variable {Y : Type u} [TopologicalSpace Y]

theorem integralHomologyClass_eq_integralSingularCycleClass (n : ℕ)
    (c : (integralSingularChains X).X (n + 1))
    (hc : (integralSingularChains X).d (n + 1) n c = 0) :
    integralHomologyClass n c hc = integralSingularCycleClass n X ⟨c, hc⟩ := by
  let K := integralSingularChains X
  let x : (K.sc (n + 1)).cycles :=
    K.liftCycles (integralChainHom (n + 1) c) n ((ComplexShape.down ℕ).next_eq' (by rfl))
      (by rw [integralChainHom_d n c, hc, integralChainHom_zero]) (ULift.up 1)
  have hx : K.homologyπ (n + 1) x = integralHomologyClass n c hc := rfl
  have hcomp : (integralSingularHomologyCycleEquiv n X) (integralHomologyClass n c hc) =
      Submodule.Quotient.mk (⟨c, hc⟩ : integralSingularCycles n X) := by
    rw [← hx]
    change (K.sc' (n + 2) (n + 1) n).moduleCatHomologyIso.hom
        ((K.homologyIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).hom (K.homologyπ (n + 1) x)) =
      Submodule.Quotient.mk (⟨c, hc⟩ : integralSingularCycles n X)
    have h1 : (K.homologyIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).hom (K.homologyπ (n + 1) x) =
        (K.sc' (n + 2) (n + 1) n).homologyπ
          ((K.cyclesIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).hom x) := by
      have h := congrArg ModuleCat.Hom.hom
        (HomologicalComplex.π_homologyIsoSc'_hom K (n + 2) (n + 1) n (by simp) (by simp))
      simp only [ModuleCat.hom_comp] at h
      exact LinearMap.congr_fun h x
    rw [h1]
    set y := (K.cyclesIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).hom x
    have h2 : (K.sc' (n + 2) (n + 1) n).moduleCatHomologyIso.hom
          ((K.sc' (n + 2) (n + 1) n).homologyπ y) =
        (K.sc' (n + 2) (n + 1) n).moduleCatLeftHomologyData.π
          ((K.sc' (n + 2) (n + 1) n).moduleCatCyclesIso.hom y) := by
      have h := congrArg ModuleCat.Hom.hom
        (ShortComplex.π_moduleCatCyclesIso_hom (K.sc' (n + 2) (n + 1) n))
      simp only [ModuleCat.hom_comp] at h
      exact LinearMap.congr_fun h y
    rw [h2]
    have hy : (K.sc' (n + 2) (n + 1) n).moduleCatCyclesIso.hom y =
        (⟨c, hc⟩ : integralSingularCycles n X) := by
      apply Subtype.ext
      rw [moduleCatCyclesIso_hom_val]
      have hi : (K.sc' (n + 2) (n + 1) n).iCycles y = K.iCycles (n + 1) x := by
        have h := congrArg ModuleCat.Hom.hom
          (HomologicalComplex.cyclesIsoSc'_hom_iCycles K (n + 2) (n + 1) n (by simp) (by simp))
        simp only [ModuleCat.hom_comp] at h
        exact LinearMap.congr_fun h x
      rw [hi]
      have hli := congrArg ModuleCat.Hom.hom
        (HomologicalComplex.liftCycles_i K (integralChainHom (n + 1) c) n
          ((ComplexShape.down ℕ).next_eq' (by rfl))
          (by rw [integralChainHom_d n c, hc, integralChainHom_zero]))
      simp only [ModuleCat.hom_comp] at hli
      have hli2 := LinearMap.congr_fun hli (ULift.up 1)
      rw [integralChainHom_apply_one] at hli2
      exact hli2
    rw [hy]
    rfl
  exact (AddEquiv.eq_symm_apply (integralSingularHomologyCycleEquiv n X)).mpr hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralHomologyClass_eq_integralSingularCycleClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralHomologyClass_eq_integralSingularCycleClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralHomologyClass_eq_integralSingularCycleClass ``Submission.DifferentialGeometry.Topology.integralHomologyClass_eq_integralSingularCycleClass

theorem integralPathSimplex_map (f : C(X, Y)) {x y : X} (p : Path x y) :
    integralPathSimplex (p.map f.continuous) =
      singularSimplexImageGen 1 f (integralPathSimplex p) := by
  apply (integralSingularSimplexEquiv 1 Y).injective
  apply ContinuousMap.ext
  intro q
  simp only [singularSimplexImageGen_apply_val, ContinuousMap.comp_apply,
    integralPathSimplex_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPathSimplex_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPathSimplex_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPathSimplex_map ``Submission.DifferentialGeometry.Topology.integralPathSimplex_map

theorem integralPathChain_map_eq_singularChainImageGen (f : C(X, Y)) {x y : X} (p : Path x y) :
    integralPathChain (p.map f.continuous) =
      singularChainImageGen 1 f (integralPathChain p) := by
  rw [integralPathChain, integralPathChain, integralPathSimplex_map, singularChainImageGen_simplex]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPathChain_map_eq_singularChainImageGen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPathChain_map_eq_singularChainImageGen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPathChain_map_eq_singularChainImageGen ``Submission.DifferentialGeometry.Topology.integralPathChain_map_eq_singularChainImageGen


def circleSphereLoop :
    Path (ULift.up (cubeSphereBasepoint 0) : liftedHomotopySphere.{u} 0)
      (ULift.up (cubeSphereBasepoint 0) : liftedHomotopySphere.{u} 0) where
  toFun t := ULift.up (cubeSphereProjection 0 (fun _ : Fin 1 => t))
  continuous_toFun := continuous_uliftUp.comp ((cubeSphereProjection 0).continuous.comp
    (continuous_pi (fun _ => continuous_id)))
  source' := by
    rw [cubeSphereProjection_boundary 0 (fun _ : Fin 1 => 0) ⟨default, Or.inl rfl⟩]
  target' := by
    rw [cubeSphereProjection_boundary 0 (fun _ : Fin 1 => 1) ⟨default, Or.inr rfl⟩]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.circleSphereLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.circleSphereLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.circleSphereLoop ``Submission.DifferentialGeometry.Topology.circleSphereLoop

theorem circleSphereLoop_apply (t : unitInterval) :
    circleSphereLoop t = ULift.up (cubeSphereProjection 0 (fun _ : Fin 1 => t)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.circleSphereLoop_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.circleSphereLoop_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.circleSphereLoop_apply ``Submission.DifferentialGeometry.Topology.circleSphereLoop_apply

def circleSphereFundamentalChain : (integralSingularChains (liftedHomotopySphere.{u} 0)).X 1 :=
  integralPathChain circleSphereLoop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.circleSphereFundamentalChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.circleSphereFundamentalChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.circleSphereFundamentalChain ``Submission.DifferentialGeometry.Topology.circleSphereFundamentalChain

theorem circleSphereFundamentalChain_boundary :
    (integralSingularChains (liftedHomotopySphere.{u} 0)).d 1 0 circleSphereFundamentalChain =
      0 :=
  integralPathChain_cycle circleSphereLoop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.circleSphereFundamentalChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.circleSphereFundamentalChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.circleSphereFundamentalChain_boundary ``Submission.DifferentialGeometry.Topology.circleSphereFundamentalChain_boundary

def circleSphereFundamentalClass : integralSingularHomology 1 (liftedHomotopySphere.{u} 0) :=
  integralPathLoopClass circleSphereLoop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.circleSphereFundamentalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.circleSphereFundamentalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.circleSphereFundamentalClass ``Submission.DifferentialGeometry.Topology.circleSphereFundamentalClass

theorem integralPathLoopClass_eq_integralHomologyClass {x : X} (p : Path x x) :
    integralPathLoopClass p =
      integralHomologyClass 0 (integralPathChain p) (integralPathChain_cycle p) := by
  rw [integralPathLoopClass,
    ← integralHomologyClass_eq_integralSingularCycleClass 0 (integralPathChain p)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPathLoopClass_eq_integralHomologyClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPathLoopClass_eq_integralHomologyClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPathLoopClass_eq_integralHomologyClass ``Submission.DifferentialGeometry.Topology.integralPathLoopClass_eq_integralHomologyClass

theorem circleSphereFundamentalClass_eq_integralHomologyClass :
    circleSphereFundamentalClass = integralHomologyClass 0 circleSphereFundamentalChain
      circleSphereFundamentalChain_boundary := by
  rw [show circleSphereFundamentalClass = integralHomologyClass 0
      (integralPathChain circleSphereLoop) (integralPathChain_cycle circleSphereLoop) from
    integralPathLoopClass_eq_integralHomologyClass circleSphereLoop]
  exact integralHomologyClass_congr rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.circleSphereFundamentalClass_eq_integralHomologyClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.circleSphereFundamentalClass_eq_integralHomologyClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.circleSphereFundamentalClass_eq_integralHomologyClass ``Submission.DifferentialGeometry.Topology.circleSphereFundamentalClass_eq_integralHomologyClass

private theorem circleSphereLoop_map_apply (x : X) (Γ : GenLoop (Fin 1) X x) (t : unitInterval) :
    (circleSphereLoop.map ((genLoopSphereHomeomorph 0 x Γ).val.comp
        (liftedHomotopySphereDown 0)).continuous) t = (genLoopEquivOfUnique (Fin 1) Γ) t := by
  rw [Path.map_coe, Function.comp_apply, circleSphereLoop_apply]
  exact genLoopSphereHomeomorph_projection 0 x Γ (fun _ : Fin 1 => t)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.circleSphereLoop_map_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.circleSphereLoop_map_apply target :: scope.openDecls } }

private theorem circleSphereLoop_map_pathChain (x : X) (Γ : GenLoop (Fin 1) X x) :
    integralPathChain (circleSphereLoop.map ((genLoopSphereHomeomorph 0 x Γ).val.comp
        (liftedHomotopySphereDown 0)).continuous) =
      integralPathChain (genLoopEquivOfUnique (Fin 1) Γ) := by
  unfold integralPathChain
  apply congrArg (integralSimplexChain 1)
  apply (integralSingularSimplexEquiv 1 X).injective
  apply ContinuousMap.ext
  intro q
  rw [integralPathSimplex_apply, integralPathSimplex_apply, circleSphereLoop_map_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.circleSphereLoop_map_pathChain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.circleSphereLoop_map_pathChain target :: scope.openDecls } }

theorem sphereHurewicz_circleSphereFundamentalClass_mk (x : X) (Γ : GenLoop (Fin 1) X x) :
    sphereHurewicz 0 x circleSphereFundamentalClass (Quotient.mk _ Γ) =
      integralPathLoopClass (genLoopEquivOfUnique (Fin 1) Γ) := by
  rw [sphereHurewicz_mk, circleSphereFundamentalClass_eq_integralHomologyClass,
    integralPathLoopClass_eq_integralHomologyClass, integralSingularHomologyMap_integralHomologyClass]
  apply integralHomologyClass_congr
  rw [integralSingularChainMap_apply_eq_singularChainImageGen, circleSphereFundamentalChain,
    ← integralPathChain_map_eq_singularChainImageGen, circleSphereLoop_map_pathChain]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz_circleSphereFundamentalClass_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz_circleSphereFundamentalClass_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz_circleSphereFundamentalClass_mk ``Submission.DifferentialGeometry.Topology.sphereHurewicz_circleSphereFundamentalClass_mk

theorem sphereHurewicz_circleSphereFundamentalClass_transAt (x : X)
    (Γ Δ : GenLoop (Fin 1) X x) :
    sphereHurewicz 0 x circleSphereFundamentalClass
        (Quotient.mk _ (GenLoop.transAt _root_.Inhabited.default Δ Γ)) =
      sphereHurewicz 0 x circleSphereFundamentalClass (Quotient.mk _ Γ) +
        sphereHurewicz 0 x circleSphereFundamentalClass (Quotient.mk _ Δ) := by
  rw [sphereHurewicz_circleSphereFundamentalClass_mk x (GenLoop.transAt _root_.Inhabited.default Δ Γ),
    sphereHurewicz_circleSphereFundamentalClass_mk x Γ,
    sphereHurewicz_circleSphereFundamentalClass_mk x Δ,
    HomotopyGroup.genLoopEquivOfUnique_transAt (Fin 1) Γ Δ,
    integralPathLoopClass_trans]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz_circleSphereFundamentalClass_transAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz_circleSphereFundamentalClass_transAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz_circleSphereFundamentalClass_transAt ``Submission.DifferentialGeometry.Topology.sphereHurewicz_circleSphereFundamentalClass_transAt

theorem sphereHurewicz_circleSphereFundamentalClass_mul (x : X)
    (a b : HomotopyGroup (Fin 1) X x) :
    sphereHurewicz 0 x circleSphereFundamentalClass (a * b) =
      sphereHurewicz 0 x circleSphereFundamentalClass a +
        sphereHurewicz 0 x circleSphereFundamentalClass b := by
  induction a using Quotient.inductionOn with
  | h Γ =>
    induction b using Quotient.inductionOn with
    | h Δ =>
      simp only [HomotopyGroup.mul_spec (i := (_root_.Inhabited.default : Fin 1))]
      exact sphereHurewicz_circleSphereFundamentalClass_transAt x Γ Δ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz_circleSphereFundamentalClass_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz_circleSphereFundamentalClass_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz_circleSphereFundamentalClass_mul ``Submission.DifferentialGeometry.Topology.sphereHurewicz_circleSphereFundamentalClass_mul

theorem sphereHurewicz_integralLiftedSphereGenerator_eq_or_eq_neg
    (hgen : IsSphereHomologyGenerator.{u} 0 circleSphereFundamentalClass.{u}) (x : X)
    (Γ : GenLoop (Fin 1) X x) :
    sphereHurewicz 0 x (integralLiftedSphereGenerator.{u} 0) (Quotient.mk _ Γ) =
        integralPathLoopClass (genLoopEquivOfUnique (Fin 1) Γ) ∨
      sphereHurewicz 0 x (integralLiftedSphereGenerator.{u} 0) (Quotient.mk _ Γ) =
        -integralPathLoopClass (genLoopEquivOfUnique (Fin 1) Γ) := by
  rcases IsSphereHomologyGenerator.eq_or_eq_neg.{u} 0
    (integralLiftedSphereGenerator_isGenerator 0) hgen with h | h
  · left
    rw [h, sphereHurewicz_circleSphereFundamentalClass_mk]
  · right
    rw [h]
    exact (sphereHurewicz_neg 0 x circleSphereFundamentalClass (Quotient.mk _ Γ)).trans
      (congrArg Neg.neg (sphereHurewicz_circleSphereFundamentalClass_mk x Γ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz_integralLiftedSphereGenerator_eq_or_eq_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz_integralLiftedSphereGenerator_eq_or_eq_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz_integralLiftedSphereGenerator_eq_or_eq_neg ``Submission.DifferentialGeometry.Topology.sphereHurewicz_integralLiftedSphereGenerator_eq_or_eq_neg

theorem hurewiczOneMultiplicative_of_circleSphereFundamentalClass_isSphereHomologyGenerator
    (hgen : IsSphereHomologyGenerator.{u} 0 circleSphereFundamentalClass.{u}) :
    HurewiczOneMultiplicative X := by
  intro x c hc a b
  rcases IsSphereHomologyGenerator.eq_or_eq_neg.{u} 0 hc hgen with h | h
  · rw [h]
    exact sphereHurewicz_circleSphereFundamentalClass_mul x a b
  · rw [h]
    rw [show sphereHurewicz 0 x (-circleSphereFundamentalClass) =
        fun a => -sphereHurewicz 0 x circleSphereFundamentalClass a from
      funext fun a => sphereHurewicz_neg 0 x circleSphereFundamentalClass a]
    exact (congrArg Neg.neg (sphereHurewicz_circleSphereFundamentalClass_mul x a b)).trans
      (neg_add _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczOneMultiplicative_of_circleSphereFundamentalClass_isSphereHomologyGenerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczOneMultiplicative_of_circleSphereFundamentalClass_isSphereHomologyGenerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczOneMultiplicative_of_circleSphereFundamentalClass_isSphereHomologyGenerator ``Submission.DifferentialGeometry.Topology.hurewiczOneMultiplicative_of_circleSphereFundamentalClass_isSphereHomologyGenerator

theorem hurewiczOneMultiplicative_iff_integralLiftedSphereGenerator :
    HurewiczOneMultiplicative X ↔
      ∀ (x : X) (a b : HomotopyGroup (Fin 1) X x),
        sphereHurewicz 0 x (integralLiftedSphereGenerator.{u} 0) (a * b) =
          sphereHurewicz 0 x (integralLiftedSphereGenerator.{u} 0) a +
            sphereHurewicz 0 x (integralLiftedSphereGenerator.{u} 0) b := by
  constructor
  · intro h x a b
    exact h x _ (integralLiftedSphereGenerator_isGenerator 0) a b
  · intro h x c hc a b
    rcases (isSphereHomologyGenerator_iff_eq_or_eq_neg_integralLiftedSphereGenerator.{u} 0
      c).mp hc with rfl | hneg
    · exact h x a b
    · rw [hneg, sphereHurewicz_neg, sphereHurewicz_neg, sphereHurewicz_neg, h x a b, neg_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczOneMultiplicative_iff_integralLiftedSphereGenerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczOneMultiplicative_iff_integralLiftedSphereGenerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczOneMultiplicative_iff_integralLiftedSphereGenerator ``Submission.DifferentialGeometry.Topology.hurewiczOneMultiplicative_iff_integralLiftedSphereGenerator

theorem isSphereHomologyGenerator_circleSphereFundamentalClass_iff_coordinate :
    IsSphereHomologyGenerator.{u} 0 circleSphereFundamentalClass.{u} ↔
      integralLiftedSphereTopEquiv.{u} 0 circleSphereFundamentalClass.{u} = 1 ∨
        integralLiftedSphereTopEquiv.{u} 0 circleSphereFundamentalClass.{u} = -1 := by
  constructor
  · intro h
    rcases (isSphereHomologyGenerator_iff_eq_or_eq_neg_integralLiftedSphereGenerator.{u} 0
      circleSphereFundamentalClass.{u}).mp h with h' | h'
    · exact Or.inl (by rw [h', integralLiftedSphereGenerator_coordinate])
    · exact Or.inr (by rw [h', map_neg, integralLiftedSphereGenerator_coordinate])
  · rintro (h | h)
    · exact ⟨integralLiftedSphereTopEquiv 0, h⟩
    · refine ⟨(integralLiftedSphereTopEquiv 0).trans (LinearEquiv.neg ℤ), ?_⟩
      rw [LinearEquiv.trans_apply, h]
      simp [LinearEquiv.neg_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereHomologyGenerator_circleSphereFundamentalClass_iff_coordinate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereHomologyGenerator_circleSphereFundamentalClass_iff_coordinate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereHomologyGenerator_circleSphereFundamentalClass_iff_coordinate ``Submission.DifferentialGeometry.Topology.isSphereHomologyGenerator_circleSphereFundamentalClass_iff_coordinate

theorem hurewiczOneLoopGeneration_iff_surjective_sphereHurewicz_circleSphereFundamentalClass
    [PathConnectedSpace X] (x : X) :
    HurewiczOneLoopGeneration x ↔
      Function.Surjective (sphereHurewicz 0 x circleSphereFundamentalClass) := by
  let h : HomotopyGroup (Fin 1) X x →* Multiplicative (integralSingularHomology 1 X) :=
    hurewiczSphereMonoidHom x circleSphereFundamentalClass
      (fun a b => sphereHurewicz_circleSphereFundamentalClass_mul x a b)
  let ψ : Additive (HomotopyGroup (Fin 1) X x) →+ integralSingularHomology 1 X :=
    { toFun := fun a => Multiplicative.toAdd (h (Additive.toMul a))
      map_zero' := by simp
      map_add' := fun a b => by simp }
  have hψ : ∀ a, ψ a = sphereHurewicz 0 x circleSphereFundamentalClass
      (Additive.toMul a) := fun a => rfl
  have hR_smul : ∀ (k : ℤ) {z : integralSingularHomology 1 X},
      z ∈ ψ.range → k • z ∈ ψ.range := by
    intro k z hz
    simpa only [Int.cast_smul_eq_zsmul ℤ] using ψ.range.zsmul_mem hz k
  let R : Submodule ℤ (integralSingularHomology 1 X) :=
    { carrier := {z | z ∈ ψ.range}
      zero_mem' := by simpa only [Set.mem_ofPred_eq] using ψ.range.zero_mem
      add_mem' := fun hx hy => by
        simpa only [Set.mem_ofPred_eq] using
          ψ.range.add_mem (by simpa only [Set.mem_ofPred_eq] using hx)
            (by simpa only [Set.mem_ofPred_eq] using hy)
      smul_mem' := fun k z hz => by
        have hz' : z ∈ ψ.range := by simpa only [Set.mem_ofPred_eq] using hz
        have h := ψ.range.zsmul_mem hz' k
        rw [← Int.cast_smul_eq_zsmul ℤ k z] at h
        simpa only [Set.mem_ofPred_eq, Int.cast_id] using h }
  have hS_le : Submodule.span ℤ (Set.range (fun γ : Path x x => integralPathLoopClass γ)) ≤
      R := by
    refine Submodule.span_le.mpr fun γ hγ => ?_
    obtain ⟨δ, rfl⟩ := hγ
    change integralPathLoopClass δ ∈ ψ.range
    refine ⟨Additive.ofMul (Quotient.mk _ ((genLoopEquivOfUnique (Fin 1)).symm δ)), ?_⟩
    change sphereHurewicz 0 x circleSphereFundamentalClass
      (Quotient.mk _ ((genLoopEquivOfUnique (Fin 1)).symm δ)) = integralPathLoopClass δ
    rw [sphereHurewicz_circleSphereFundamentalClass_mk, Equiv.apply_symm_apply]
  have hR_le : (ψ.range : Set (integralSingularHomology 1 X)) ⊆
      Submodule.span ℤ (Set.range (fun γ : Path x x => integralPathLoopClass γ)) := by
    rintro y hy
    obtain ⟨a, rfl⟩ := hy
    change sphereHurewicz 0 x circleSphereFundamentalClass (Additive.toMul a) ∈
      Submodule.span ℤ (Set.range (fun γ : Path x x => integralPathLoopClass γ))
    refine Quotient.inductionOn (Additive.toMul a) fun Γ => ?_
    rw [sphereHurewicz_circleSphereFundamentalClass_mk]
    exact Submodule.subset_span ⟨_, rfl⟩
  have hrange : Submodule.span ℤ (Set.range (fun γ : Path x x => integralPathLoopClass γ)) = ⊤ ↔
      ψ.range = ⊤ := by
    rw [Submodule.eq_top_iff', AddSubgroup.eq_top_iff']
    exact ⟨fun h y => hS_le (h y), fun h y => hR_le (h y)⟩
  have hsurj : Function.Surjective (sphereHurewicz 0 x circleSphereFundamentalClass) ↔
      Function.Surjective ψ := by
    constructor
    · intro hf b
      obtain ⟨a, ha⟩ := hf b
      exact ⟨Additive.ofMul a, by rw [hψ]; exact ha⟩
    · intro hf b
      obtain ⟨a, ha⟩ := hf b
      exact ⟨Additive.toMul a, (hψ a).symm.trans ha⟩
  have hloop : HurewiczOneLoopGeneration x ↔
      Submodule.span ℤ (Set.range (fun γ : Path x x => integralPathLoopClass γ)) = ⊤ :=
    ⟨fun h => Submodule.eq_top_iff'.mpr h, fun h y => Submodule.eq_top_iff'.mp h y⟩
  rw [hloop, hrange]
  exact AddMonoidHom.range_eq_top.trans hsurj.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczOneLoopGeneration_iff_surjective_sphereHurewicz_circleSphereFundamentalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczOneLoopGeneration_iff_surjective_sphereHurewicz_circleSphereFundamentalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczOneLoopGeneration_iff_surjective_sphereHurewicz_circleSphereFundamentalClass ``Submission.DifferentialGeometry.Topology.hurewiczOneLoopGeneration_iff_surjective_sphereHurewicz_circleSphereFundamentalClass

theorem abelianizationHomotopyGroupOne_equiv_of_circleSphereFundamentalClass
    [PathConnectedSpace X] (x : X)
    (hsurj : Function.Surjective (sphereHurewicz 0 x circleSphereFundamentalClass))
    (hker : ∀ a : HomotopyGroup (Fin 1) X x,
      sphereHurewicz 0 x circleSphereFundamentalClass a = 0 →
        a ∈ commutator (HomotopyGroup (Fin 1) X x)) :
    Nonempty (Abelianization (HomotopyGroup (Fin 1) X x) ≃*
      Multiplicative (integralSingularHomology 1 X)) :=
  abelianizationHomotopyGroupOne_equiv_of_hurewiczOne x circleSphereFundamentalClass
    (fun a b => sphereHurewicz_circleSphereFundamentalClass_mul x a b) hsurj hker

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.abelianizationHomotopyGroupOne_equiv_of_circleSphereFundamentalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.abelianizationHomotopyGroupOne_equiv_of_circleSphereFundamentalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.abelianizationHomotopyGroupOne_equiv_of_circleSphereFundamentalClass ``Submission.DifferentialGeometry.Topology.abelianizationHomotopyGroupOne_equiv_of_circleSphereFundamentalClass

theorem integralSingularHomologyMap_circleSphereFundamentalClass (x : X)
    (Γ : GenLoop (Fin 1) X x) :
    integralSingularHomologyMap 1 ((genLoopSphereHomeomorph 0 x Γ).val.comp
        (liftedHomotopySphereDown 0)) circleSphereFundamentalClass =
      integralPathLoopClass (genLoopEquivOfUnique (Fin 1) Γ) :=
  (sphereHurewicz_mk 0 x circleSphereFundamentalClass Γ).symm.trans
    (sphereHurewicz_circleSphereFundamentalClass_mk x Γ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomologyMap_circleSphereFundamentalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomologyMap_circleSphereFundamentalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomologyMap_circleSphereFundamentalClass ``Submission.DifferentialGeometry.Topology.integralSingularHomologyMap_circleSphereFundamentalClass

theorem circleSphereFundamentalClass_ne_zero_of_isSphereHomologyGenerator
    (hgen : IsSphereHomologyGenerator.{u} 0 circleSphereFundamentalClass.{u}) :
    circleSphereFundamentalClass.{u} ≠ 0 :=
  IsSphereHomologyGenerator.ne_zero 0 hgen

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.circleSphereFundamentalClass_ne_zero_of_isSphereHomologyGenerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.circleSphereFundamentalClass_ne_zero_of_isSphereHomologyGenerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.circleSphereFundamentalClass_ne_zero_of_isSphereHomologyGenerator ``Submission.DifferentialGeometry.Topology.circleSphereFundamentalClass_ne_zero_of_isSphereHomologyGenerator

theorem hurewiczOneMultiplicative_punit : HurewiczOneMultiplicative PUnit.{u + 1} := by
  intro x c hc a b
  exact @Subsingleton.elim (integralSingularHomology 1 PUnit.{u + 1})
    (integralSingularHomology_subsingleton_of_contractible (X := PUnit.{u + 1}) 1 (by omega)) _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hurewiczOneMultiplicative_punit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hurewiczOneMultiplicative_punit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hurewiczOneMultiplicative_punit ``Submission.DifferentialGeometry.Topology.hurewiczOneMultiplicative_punit

end DifferentialGeometry.Topology
