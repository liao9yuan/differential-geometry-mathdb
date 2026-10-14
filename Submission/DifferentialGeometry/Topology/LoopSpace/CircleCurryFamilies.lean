import Submission.DifferentialGeometry.Topology.LoopSpace.CircleCurry
import Submission.DifferentialGeometry.Topology.LoopSpace.FreeAdjunction
import Submission.DifferentialGeometry.Topology.Homotopy.TransportComposition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {K Q : Type*} [TopologicalSpace K] [TopologicalSpace Q]



theorem continuous_genLoopCircleCurry_family (n : ℕ) (b : K → Q)
    (Γ : ∀ k, GenLoop (Fin (n + 2)) Q (b k))
    (hΓ : Continuous (fun z : K × (Fin (n + 2) → unitInterval) => Γ z.1 z.2)) :
    Continuous (fun z : K × (Fin (n + 1) → unitInterval) =>
      (genLoopCircleCurry n (b z.1) (Γ z.1) z.2).val) := by
  apply _root_.ContinuousMap.continuous_of_continuous_uncurry
  apply (unitInterval_to_loopCircle_prod_quotient (K × (Fin (n + 1) → unitInterval))).continuous_iff.mpr
  have hc : Continuous (fun z : (K × (Fin (n + 1) → unitInterval)) × unitInterval =>
      Γ z.1.1 (cubeCircleCoordinates n z.1.2 z.2)) :=
    hΓ.comp ((continuous_fst.comp continuous_fst).prodMk
      ((continuous_cubeCircleCoordinates n).comp
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))
  apply hc.congr
  intro z
  exact (genLoopCircleCurry_coe n (b z.1.1) (Γ z.1.1) z.1.2 z.2).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_genLoopCircleCurry_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_genLoopCircleCurry_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_genLoopCircleCurry_family ``Submission.DifferentialGeometry.Topology.continuous_genLoopCircleCurry_family


def circleCurryFreeGenLoop (n : ℕ) (q : Q) (Γ : GenLoop (Fin (n + 2)) Q q) :
    GenLoop (Fin (n + 1)) (freeLoop Q) (FreeLoop.constants q) :=
  genLoopBasedMap (basedCircleInclusion q) (basedCircleConstant q) (FreeLoop.constants q) rfl
    (genLoopCircleCurry n q Γ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.circleCurryFreeGenLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.circleCurryFreeGenLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.circleCurryFreeGenLoop ``Submission.DifferentialGeometry.Topology.circleCurryFreeGenLoop


theorem circleCurryFreeGenLoop_coe (n : ℕ) (q : Q) (Γ : GenLoop (Fin (n + 2)) Q q)
    (v : Fin (n + 1) → unitInterval) (s : unitInterval) :
    circleCurryFreeGenLoop n q Γ v (s.val : loopCircle) = Γ (cubeCircleCoordinates n v s) :=
  genLoopCircleCurry_coe n q Γ v s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.circleCurryFreeGenLoop_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.circleCurryFreeGenLoop_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.circleCurryFreeGenLoop_coe ``Submission.DifferentialGeometry.Topology.circleCurryFreeGenLoop_coe



def cubePathExtensionSlice (n : ℕ) {x y : Q} (p : Path x y)
    (Γ : GenLoop (Fin (n + 1)) Q x) (t : unitInterval) : GenLoop (Fin (n + 1)) Q (p t) :=
  ⟨⟨fun v => cubePathExtension n p Γ (t, v),
    (continuous_cubePathExtension n p Γ).comp (continuous_const.prodMk continuous_id)⟩,
      cubePathExtension_boundary n p Γ t⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubePathExtensionSlice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubePathExtensionSlice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubePathExtensionSlice ``Submission.DifferentialGeometry.Topology.cubePathExtensionSlice



def circleCurryExtension (n : ℕ) {x y : Q} (p : Path x y)
    (Γ : GenLoop (Fin (n + 2)) Q x) :
    C(unitInterval × (Fin (n + 1) → unitInterval), freeLoop Q) :=
  ⟨fun z => (genLoopCircleCurry n (p z.1) (cubePathExtensionSlice (n + 1) p Γ z.1) z.2).val,
    continuous_genLoopCircleCurry_family n p (cubePathExtensionSlice (n + 1) p Γ)
      (continuous_cubePathExtension (n + 1) p Γ)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.circleCurryExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.circleCurryExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.circleCurryExtension ``Submission.DifferentialGeometry.Topology.circleCurryExtension


theorem circleCurryExtension_zero (n : ℕ) {x y : Q} (p : Path x y)
    (Γ : GenLoop (Fin (n + 2)) Q x) (v : Fin (n + 1) → unitInterval) :
    circleCurryExtension n p Γ (0, v) = circleCurryFreeGenLoop n x Γ v := by
  ext θ
  obtain ⟨s, rfl⟩ := unitInterval_to_loopCircle_surjective θ
  change (genLoopCircleCurry n (p 0) (cubePathExtensionSlice (n + 1) p Γ 0) v).val
    (s.val : loopCircle) = _
  rw [genLoopCircleCurry_coe, circleCurryFreeGenLoop_coe]
  exact cubePathExtension_zero (n + 1) p Γ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.circleCurryExtension_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.circleCurryExtension_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.circleCurryExtension_zero ``Submission.DifferentialGeometry.Topology.circleCurryExtension_zero


theorem circleCurryExtension_one (n : ℕ) {x y : Q} (p : Path x y)
    (Γ : GenLoop (Fin (n + 2)) Q x) (v : Fin (n + 1) → unitInterval) :
    circleCurryExtension n p Γ (1, v) =
      circleCurryFreeGenLoop n y (genLoopTransport (n + 1) p Γ) v := by
  ext θ
  obtain ⟨s, rfl⟩ := unitInterval_to_loopCircle_surjective θ
  change (genLoopCircleCurry n (p 1) (cubePathExtensionSlice (n + 1) p Γ 1) v).val
    (s.val : loopCircle) = _
  rw [genLoopCircleCurry_coe, circleCurryFreeGenLoop_coe]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.circleCurryExtension_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.circleCurryExtension_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.circleCurryExtension_one ``Submission.DifferentialGeometry.Topology.circleCurryExtension_one



theorem circleCurryExtension_boundary (n : ℕ) {x y : Q} (p : Path x y)
    (Γ : GenLoop (Fin (n + 2)) Q x) (t : unitInterval)
    (v : Fin (n + 1) → unitInterval) (hv : v ∈ Cube.boundary (Fin (n + 1))) :
    circleCurryExtension n p Γ (t, v) = FreeLoop.constants (p t) := by
  ext θ
  obtain ⟨s, rfl⟩ := unitInterval_to_loopCircle_surjective θ
  change (genLoopCircleCurry n (p t) (cubePathExtensionSlice (n + 1) p Γ t) v).val
    (s.val : loopCircle) = p t
  rw [genLoopCircleCurry_coe]
  exact cubePathExtension_boundary (n + 1) p Γ t _ (cubeCircleCoordinates_boundary n v hv s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.circleCurryExtension_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.circleCurryExtension_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.circleCurryExtension_boundary ``Submission.DifferentialGeometry.Topology.circleCurryExtension_boundary

end DifferentialGeometry.Topology
