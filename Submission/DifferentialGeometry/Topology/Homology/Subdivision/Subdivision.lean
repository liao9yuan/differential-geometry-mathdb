import Submission.DifferentialGeometry.Topology.Homology.Subdivision.AffineChains

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.Submission.CategoryTheory _root_.CategoryTheory.Limits _root_.Submission.CategoryTheory.Limits _root_.AlgebraicTopology _root_.Submission.DifferentialGeometry.MathlibCompat

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

open scoped _root_.Simplicial in
abbrev Sing (X : TopCat.{u}) (k : ℕ) : Type u := (TopCat.toSSet.obj X) _⦋k⦌

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sing ``Submission.DifferentialGeometry.Topology.SingularPair.Sing

lemma bary_fin_one {n : ℕ} (w : Fin 1 → Δ n) : (fun _ : Fin 1 => bary w) = w := by
  have hw : w = fun _ => w 0 := by
    funext j
    obtain rfl : j = 0 := Fin.ext (Nat.lt_one_iff.mp j.isLt)
    rfl
  rw [hw, bary_const]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.bary_fin_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.bary_fin_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.bary_fin_one ``Submission.DifferentialGeometry.Topology.SingularPair.bary_fin_one

namespace AffChain

def barycentricSubdivision {n : ℕ} : (k : ℕ) → AffChain k n →ₗ[ℤ] AffChain k n
  | 0 => LinearMap.id
  | k + 1 => Finsupp.linearCombination ℤ
      (fun w => coneL (bary w) k (barycentricSubdivision k (bd k (Finsupp.single w 1))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.barycentricSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.barycentricSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.barycentricSubdivision ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.barycentricSubdivision

def subdivisionHomotopyMap {n : ℕ} : (k : ℕ) → AffChain k n →ₗ[ℤ] AffChain (k + 1) n
  | 0 => Finsupp.linearCombination ℤ fun w => coneL (bary w) 0 (Finsupp.single w 1)
  | k + 1 => Finsupp.linearCombination ℤ
      (fun w => coneL (bary w) (k + 1) (Finsupp.single w 1 - subdivisionHomotopyMap k (bd k (Finsupp.single w 1))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.subdivisionHomotopyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.subdivisionHomotopyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.subdivisionHomotopyMap ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.subdivisionHomotopyMap

@[simp] lemma barycentricSubdivision_zero {n : ℕ} :
    (barycentricSubdivision 0 : AffChain 0 n →ₗ[ℤ] AffChain 0 n) = LinearMap.id := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.barycentricSubdivision_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.barycentricSubdivision_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.barycentricSubdivision_zero ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.barycentricSubdivision_zero

lemma barycentricSubdivision_succ_single {n : ℕ} {k : ℕ} (w : Fin (k + 2) → Δ n) (z : ℤ) :
    barycentricSubdivision (k + 1) (Finsupp.single w z) =
      z • coneL (bary w) k (barycentricSubdivision k (bd k (Finsupp.single w 1))) := by
  simp [barycentricSubdivision, Finsupp.linearCombination_single]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.barycentricSubdivision_succ_single then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.barycentricSubdivision_succ_single"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.barycentricSubdivision_succ_single ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.barycentricSubdivision_succ_single

lemma subdivisionHomotopyMap_zero_single {n : ℕ} (w : Fin 1 → Δ n) (z : ℤ) :
    subdivisionHomotopyMap 0 (Finsupp.single w z) = z • coneL (bary w) 0 (Finsupp.single w 1) := by
  simp [subdivisionHomotopyMap, Finsupp.linearCombination_single]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.subdivisionHomotopyMap_zero_single then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.subdivisionHomotopyMap_zero_single"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.subdivisionHomotopyMap_zero_single ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.subdivisionHomotopyMap_zero_single

lemma subdivisionHomotopyMap_succ_single {n : ℕ} {k : ℕ} (w : Fin (k + 2) → Δ n) (z : ℤ) :
    subdivisionHomotopyMap (k + 1) (Finsupp.single w z) =
      z • coneL (bary w) (k + 1) (Finsupp.single w 1 - subdivisionHomotopyMap k (bd k (Finsupp.single w 1))) := by
  simp [subdivisionHomotopyMap, Finsupp.linearCombination_single]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.subdivisionHomotopyMap_succ_single then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.subdivisionHomotopyMap_succ_single"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.subdivisionHomotopyMap_succ_single ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.subdivisionHomotopyMap_succ_single

theorem bd_comp_barycentricSubdivision {n : ℕ} : ∀ k, (bd k).comp (barycentricSubdivision (k + 1) : AffChain (k + 1) n →ₗ[ℤ] _) =
    (barycentricSubdivision k).comp (bd k)
  | 0 => by
    ext w : 2
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, barycentricSubdivision_succ_single, one_smul, barycentricSubdivision_zero,
      LinearMap.id_apply, bd_coneL_zero]
    have := LinearMap.congr_fun (eps_comp_bd (n := n)) (Finsupp.single w 1)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
    rw [this, zero_smul, sub_zero]
  | k + 1 => by
    ext w : 2
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, barycentricSubdivision_succ_single, one_smul]
    rw [← LinearMap.comp_apply (bd (k + 1)) (coneL _ _), bd_comp_coneL, LinearMap.sub_apply,
      LinearMap.id_apply, LinearMap.comp_apply,
      ← LinearMap.comp_apply (bd k) (barycentricSubdivision (k + 1)), bd_comp_barycentricSubdivision k, LinearMap.comp_apply,
      ← LinearMap.comp_apply (bd k) (bd (k + 1)), bd_comp_bd, LinearMap.zero_apply, map_zero,
      map_zero, sub_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_barycentricSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_barycentricSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_barycentricSubdivision ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_barycentricSubdivision

lemma bd_barycentricSubdivision_succ {n : ℕ} (k : ℕ) (c : AffChain (k + 1) n) :
    bd k (barycentricSubdivision (k + 1) c) = barycentricSubdivision k (bd k c) :=
  LinearMap.congr_fun (bd_comp_barycentricSubdivision k) c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.bd_barycentricSubdivision_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.bd_barycentricSubdivision_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.bd_barycentricSubdivision_succ ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.bd_barycentricSubdivision_succ

theorem bd_comp_subdivisionHomotopyMap_zero {n : ℕ} : (bd 0).comp (subdivisionHomotopyMap 0 : AffChain 0 n →ₗ[ℤ] _) = 0 := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, subdivisionHomotopyMap_zero_single, one_smul, bd_coneL_zero,
    eps_single, bary_fin_one, LinearMap.zero_comp, LinearMap.zero_apply, sub_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_subdivisionHomotopyMap_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_subdivisionHomotopyMap_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_subdivisionHomotopyMap_zero ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_subdivisionHomotopyMap_zero

theorem bd_comp_subdivisionHomotopyMap_succ_of {n : ℕ} (k : ℕ)
    (h : ∀ y : AffChain (k + 1) n, bd k (subdivisionHomotopyMap k (bd k y)) = bd k y - barycentricSubdivision k (bd k y)) :
    (bd (k + 1)).comp (subdivisionHomotopyMap (k + 1) : AffChain (k + 1) n →ₗ[ℤ] _) + (subdivisionHomotopyMap k).comp (bd k) =
      LinearMap.id - barycentricSubdivision (k + 1) := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, subdivisionHomotopyMap_succ_single, one_smul,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, barycentricSubdivision_succ_single]
  rw [← LinearMap.comp_apply (bd (k + 1)) (coneL _ _), bd_comp_coneL, LinearMap.sub_apply,
    LinearMap.id_apply, LinearMap.comp_apply, map_sub, h, sub_sub_cancel]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_subdivisionHomotopyMap_succ_of then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_subdivisionHomotopyMap_succ_of"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_subdivisionHomotopyMap_succ_of ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_subdivisionHomotopyMap_succ_of

theorem bd_comp_subdivisionHomotopyMap_succ {n : ℕ} : ∀ k,
    (bd (k + 1)).comp (subdivisionHomotopyMap (k + 1) : AffChain (k + 1) n →ₗ[ℤ] _) + (subdivisionHomotopyMap k).comp (bd k) =
      LinearMap.id - barycentricSubdivision (k + 1)
  | 0 => bd_comp_subdivisionHomotopyMap_succ_of 0 fun y => by
      have := LinearMap.congr_fun (bd_comp_subdivisionHomotopyMap_zero (n := n)) (bd 0 y)
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
      rw [this, barycentricSubdivision_zero, LinearMap.id_apply, sub_self]
  | k + 1 => bd_comp_subdivisionHomotopyMap_succ_of (k + 1) fun y => by
      have := LinearMap.congr_fun (bd_comp_subdivisionHomotopyMap_succ k) (bd (k + 1) y)
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.id_apply] at this
      rw [← LinearMap.comp_apply (bd k) (bd (k + 1)), bd_comp_bd, LinearMap.zero_apply,
        map_zero, add_zero] at this
      exact this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_subdivisionHomotopyMap_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_subdivisionHomotopyMap_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_subdivisionHomotopyMap_succ ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_subdivisionHomotopyMap_succ

lemma bd_subdivisionHomotopyMap_zero {n : ℕ} (c : AffChain 0 n) : bd (n := n) 0 (subdivisionHomotopyMap 0 c) = 0 :=
  LinearMap.congr_fun bd_comp_subdivisionHomotopyMap_zero c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.bd_subdivisionHomotopyMap_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.bd_subdivisionHomotopyMap_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.bd_subdivisionHomotopyMap_zero ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.bd_subdivisionHomotopyMap_zero

lemma bd_subdivisionHomotopyMap_succ_add_subdivisionHomotopyMap_bd {n : ℕ} (k : ℕ) (c : AffChain (k + 1) n) :
    bd (k + 1) (subdivisionHomotopyMap (k + 1) c) + subdivisionHomotopyMap k (bd k c) = c - barycentricSubdivision (k + 1) c :=
  LinearMap.congr_fun (bd_comp_subdivisionHomotopyMap_succ k) c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.bd_subdivisionHomotopyMap_succ_add_subdivisionHomotopyMap_bd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.bd_subdivisionHomotopyMap_succ_add_subdivisionHomotopyMap_bd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.bd_subdivisionHomotopyMap_succ_add_subdivisionHomotopyMap_bd ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.bd_subdivisionHomotopyMap_succ_add_subdivisionHomotopyMap_bd

lemma push_affineSimplex_comp_idVerts {m n : ℕ} (u : Fin (m + 1) → Δ n) :
    affineSimplex u ∘ idVerts m = u := by
  funext i; simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.push_affineSimplex_comp_idVerts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.push_affineSimplex_comp_idVerts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.push_affineSimplex_comp_idVerts ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.push_affineSimplex_comp_idVerts

theorem push_comp_barycentricSubdivision {n n' : ℕ} (u : Fin (n + 1) → Δ n') : ∀ k,
    (push (affineSimplex u) k).comp (barycentricSubdivision k) = (barycentricSubdivision k).comp (push (affineSimplex u) k)
  | 0 => by simp
  | k + 1 => by
    ext w : 2
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, barycentricSubdivision_succ_single, one_smul, push_single]
    rw [← LinearMap.comp_apply (push _ _) (coneL _ _), push_comp_coneL, LinearMap.comp_apply,
      ← LinearMap.comp_apply (push _ _) (barycentricSubdivision k), push_comp_barycentricSubdivision u k, LinearMap.comp_apply,
      ← LinearMap.comp_apply (push _ _) (bd k), push_comp_bd, LinearMap.comp_apply, push_single,
      affineSimplex_bary]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_barycentricSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_barycentricSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_barycentricSubdivision ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_barycentricSubdivision

theorem push_comp_subdivisionHomotopyMap {n n' : ℕ} (u : Fin (n + 1) → Δ n') : ∀ k,
    (push (affineSimplex u) (k + 1)).comp (subdivisionHomotopyMap k) = (subdivisionHomotopyMap k).comp (push (affineSimplex u) k)
  | 0 => by
    ext w : 2
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, subdivisionHomotopyMap_zero_single, one_smul, push_single]
    rw [← LinearMap.comp_apply (push _ _) (coneL _ _), push_comp_coneL, LinearMap.comp_apply,
      push_single, affineSimplex_bary]
  | k + 1 => by
    ext w : 2
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, subdivisionHomotopyMap_succ_single, one_smul, push_single]
    rw [← LinearMap.comp_apply (push _ _) (coneL _ _), push_comp_coneL, LinearMap.comp_apply,
      map_sub, push_single, ← LinearMap.comp_apply (push _ _) (subdivisionHomotopyMap k), push_comp_subdivisionHomotopyMap u k,
      LinearMap.comp_apply, ← LinearMap.comp_apply (push _ _) (bd k), push_comp_bd,
      LinearMap.comp_apply, push_single, affineSimplex_bary]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_subdivisionHomotopyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_subdivisionHomotopyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_subdivisionHomotopyMap ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_subdivisionHomotopyMap

lemma push_barycentricSubdivision {n n' : ℕ} (u : Fin (n + 1) → Δ n') (k : ℕ) (c : AffChain k n) :
    push (affineSimplex u) k (barycentricSubdivision k c) = barycentricSubdivision k (push (affineSimplex u) k c) :=
  LinearMap.congr_fun (push_comp_barycentricSubdivision u k) c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.push_barycentricSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.push_barycentricSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.push_barycentricSubdivision ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.push_barycentricSubdivision

lemma push_subdivisionHomotopyMap {n n' : ℕ} (u : Fin (n + 1) → Δ n') (k : ℕ) (c : AffChain k n) :
    push (affineSimplex u) (k + 1) (subdivisionHomotopyMap k c) = subdivisionHomotopyMap k (push (affineSimplex u) k c) :=
  LinearMap.congr_fun (push_comp_subdivisionHomotopyMap u k) c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.push_subdivisionHomotopyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.push_subdivisionHomotopyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.push_subdivisionHomotopyMap ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.push_subdivisionHomotopyMap

def iteratedBarycentricSubdivision {n : ℕ} (k : ℕ) : ℕ → AffChain k n →ₗ[ℤ] AffChain k n
  | 0 => LinearMap.id
  | j + 1 => (barycentricSubdivision k).comp (iteratedBarycentricSubdivision k j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.iteratedBarycentricSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.iteratedBarycentricSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.iteratedBarycentricSubdivision ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.iteratedBarycentricSubdivision

@[simp] lemma iteratedBarycentricSubdivision_zero {n : ℕ} (k : ℕ) :
    (iteratedBarycentricSubdivision k 0 : AffChain k n →ₗ[ℤ] _) = LinearMap.id := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.iteratedBarycentricSubdivision_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.iteratedBarycentricSubdivision_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.iteratedBarycentricSubdivision_zero ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.iteratedBarycentricSubdivision_zero

lemma iteratedBarycentricSubdivision_succ {n : ℕ} (k j : ℕ) :
    (iteratedBarycentricSubdivision k (j + 1) : AffChain k n →ₗ[ℤ] _) = (barycentricSubdivision k).comp (iteratedBarycentricSubdivision k j) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.iteratedBarycentricSubdivision_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.iteratedBarycentricSubdivision_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.iteratedBarycentricSubdivision_succ ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.iteratedBarycentricSubdivision_succ

lemma iteratedBarycentricSubdivision_succ' {n : ℕ} (k j : ℕ) :
    (iteratedBarycentricSubdivision k (j + 1) : AffChain k n →ₗ[ℤ] _) = (iteratedBarycentricSubdivision k j).comp (barycentricSubdivision k) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [iteratedBarycentricSubdivision_succ, ih, ← LinearMap.comp_assoc, ← iteratedBarycentricSubdivision_succ, ih]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.iteratedBarycentricSubdivision_succ' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.iteratedBarycentricSubdivision_succ'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.iteratedBarycentricSubdivision_succ' ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.iteratedBarycentricSubdivision_succ'

lemma bd_iteratedBarycentricSubdivision_succ {n : ℕ} (k j : ℕ) (c : AffChain (k + 1) n) :
    bd k (iteratedBarycentricSubdivision (k + 1) j c) = iteratedBarycentricSubdivision k j (bd k c) := by
  induction j generalizing c with
  | zero => rfl
  | succ j ih => rw [iteratedBarycentricSubdivision_succ, LinearMap.comp_apply, bd_barycentricSubdivision_succ, ih, iteratedBarycentricSubdivision_succ,
      LinearMap.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.bd_iteratedBarycentricSubdivision_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.bd_iteratedBarycentricSubdivision_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.bd_iteratedBarycentricSubdivision_succ ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.bd_iteratedBarycentricSubdivision_succ

lemma push_iteratedBarycentricSubdivision {n n' : ℕ} (u : Fin (n + 1) → Δ n') (k j : ℕ) (c : AffChain k n) :
    push (affineSimplex u) k (iteratedBarycentricSubdivision k j c) = iteratedBarycentricSubdivision k j (push (affineSimplex u) k c) := by
  induction j generalizing c with
  | zero => rfl
  | succ j ih => rw [iteratedBarycentricSubdivision_succ, LinearMap.comp_apply, push_barycentricSubdivision, ih, iteratedBarycentricSubdivision_succ,
      LinearMap.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.push_iteratedBarycentricSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.push_iteratedBarycentricSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.push_iteratedBarycentricSubdivision ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.push_iteratedBarycentricSubdivision

end AffChain

variable (R : ModuleCat.{u} ℤ)

open _root_.Submission.DifferentialGeometry.Topology.SingularPair.AffChain

lemma toSSetObjEquiv_affSing {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) {k : ℕ}
    (w : Fin (k + 1) → Δ m) :
    X.toSSetObjEquiv _ (affSing σ w) = σ.comp (affineSimplex w) :=
  Equiv.apply_symm_apply _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.toSSetObjEquiv_affSing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.toSSetObjEquiv_affSing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.toSSetObjEquiv_affSing ``Submission.DifferentialGeometry.Topology.SingularPair.toSSetObjEquiv_affSing

lemma sing_toSSetObjEquiv {X : TopCat.{u}} {k : ℕ} (τ : Sing X k) :
    sing (X.toSSetObjEquiv _ τ) = τ :=
  Equiv.symm_apply_apply _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.sing_toSSetObjEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.sing_toSSetObjEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.sing_toSSetObjEquiv ``Submission.DifferentialGeometry.Topology.SingularPair.sing_toSSetObjEquiv

lemma toSSetObjEquiv_toSSet_map_app {X Y : TopCat.{u}} (f : X ⟶ Y) {k : ℕ}
    (τ : Sing X k) :
    Y.toSSetObjEquiv _ ((TopCat.toSSet.map f).app _ τ) = f.hom.comp (X.toSSetObjEquiv _ τ) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.toSSetObjEquiv_toSSet_map_app then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.toSSetObjEquiv_toSSet_map_app"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.toSSetObjEquiv_toSSet_map_app ``Submission.DifferentialGeometry.Topology.SingularPair.toSSetObjEquiv_toSSet_map_app

def ofUniversal (X : TopCat.{u}) (c : ∀ k, AffChain k k) (k : ℕ) :
    (simplicialChains R X).X k ⟶ (simplicialChains R X).X k :=
  Sigma.desc fun τ => toChain R (X.toSSetObjEquiv _ τ) k (c k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ofUniversal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ofUniversal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ofUniversal ``Submission.DifferentialGeometry.Topology.SingularPair.ofUniversal

@[reassoc]
lemma ι_ofUniversal (X : TopCat.{u}) (c : ∀ k, AffChain k k) (k : ℕ)
    (τ : Sing X k) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ ofUniversal R X c k =
      toChain R (X.toSSetObjEquiv _ τ) k (c k) :=
  Sigma.ι_desc _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι_ofUniversal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι_ofUniversal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι_ofUniversal ``Submission.DifferentialGeometry.Topology.SingularPair.ι_ofUniversal

def barycentricSubdivisionComponent (X : TopCat.{u}) (k : ℕ) : (simplicialChains R X).X k ⟶ (simplicialChains R X).X k :=
  ofUniversal R X (fun k => barycentricSubdivision k (Finsupp.single (idVerts k) 1)) k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.barycentricSubdivisionComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.barycentricSubdivisionComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.barycentricSubdivisionComponent ``Submission.DifferentialGeometry.Topology.SingularPair.barycentricSubdivisionComponent

@[reassoc]
lemma ι_barycentricSubdivisionComponent (X : TopCat.{u}) (k : ℕ) (τ : Sing X k) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ barycentricSubdivisionComponent R X k =
      toChain R (X.toSSetObjEquiv _ τ) k (barycentricSubdivision k (Finsupp.single (idVerts k) 1)) :=
  ι_ofUniversal R X _ k τ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι_barycentricSubdivisionComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι_barycentricSubdivisionComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι_barycentricSubdivisionComponent ``Submission.DifferentialGeometry.Topology.SingularPair.ι_barycentricSubdivisionComponent

lemma toChain_barycentricSubdivisionComponent {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) (k : ℕ) (c : AffChain k m) :
    toChain R σ k c ≫ barycentricSubdivisionComponent R X k = toChain R σ k (barycentricSubdivision k c) := by
  suffices (Preadditive.rightComp R (barycentricSubdivisionComponent R X k)).comp (toChain R σ k) =
      (toChain R σ k).comp (barycentricSubdivision k).toAddMonoidHom from DFunLike.congr_fun this c
  ext w : 2
  simp only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply, toChain_single, one_smul,
    rightComp_apply_eq, ι_barycentricSubdivisionComponent, toSSetObjEquiv_affSing]
  rw [← toChain_push, push_barycentricSubdivision, push_single, push_affineSimplex_comp_idVerts]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.toChain_barycentricSubdivisionComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.toChain_barycentricSubdivisionComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.toChain_barycentricSubdivisionComponent ``Submission.DifferentialGeometry.Topology.SingularPair.toChain_barycentricSubdivisionComponent

def subdivisionHomotopyComponent (X : TopCat.{u}) (k : ℕ) : (simplicialChains R X).X k ⟶ (simplicialChains R X).X (k + 1) :=
  Sigma.desc fun τ =>
    toChain R (X.toSSetObjEquiv _ τ) (k + 1) (subdivisionHomotopyMap k (Finsupp.single (idVerts k) 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.subdivisionHomotopyComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.subdivisionHomotopyComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.subdivisionHomotopyComponent ``Submission.DifferentialGeometry.Topology.SingularPair.subdivisionHomotopyComponent

@[reassoc]
lemma ι_subdivisionHomotopyComponent (X : TopCat.{u}) (k : ℕ) (τ : Sing X k) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ subdivisionHomotopyComponent R X k =
      toChain R (X.toSSetObjEquiv _ τ) (k + 1) (subdivisionHomotopyMap k (Finsupp.single (idVerts k) 1)) :=
  Sigma.ι_desc _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι_subdivisionHomotopyComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι_subdivisionHomotopyComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι_subdivisionHomotopyComponent ``Submission.DifferentialGeometry.Topology.SingularPair.ι_subdivisionHomotopyComponent

lemma toChain_subdivisionHomotopyComponent {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) (k : ℕ) (c : AffChain k m) :
    toChain R σ k c ≫ subdivisionHomotopyComponent R X k = toChain R σ (k + 1) (subdivisionHomotopyMap k c) := by
  suffices (Preadditive.rightComp R (subdivisionHomotopyComponent R X k)).comp (toChain R σ k) =
      (toChain R σ (k + 1)).comp (subdivisionHomotopyMap k).toAddMonoidHom from DFunLike.congr_fun this c
  ext w : 2
  simp only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply, toChain_single, one_smul,
    rightComp_apply_eq, ι_subdivisionHomotopyComponent, toSSetObjEquiv_affSing]
  rw [← toChain_push, push_subdivisionHomotopyMap, push_single, push_affineSimplex_comp_idVerts]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.toChain_subdivisionHomotopyComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.toChain_subdivisionHomotopyComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.toChain_subdivisionHomotopyComponent ``Submission.DifferentialGeometry.Topology.SingularPair.toChain_subdivisionHomotopyComponent

lemma ι_eq_toChain {X : TopCat.{u}} {k : ℕ} (τ : Sing X k) :
    (TopCat.toSSet.obj X).ιChainComplex τ =
      toChain R (X.toSSetObjEquiv _ τ) k (Finsupp.single (idVerts k) 1) := by
  rw [toChain_single_idVerts, sing_toSSetObjEquiv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι_eq_toChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι_eq_toChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι_eq_toChain ``Submission.DifferentialGeometry.Topology.SingularPair.ι_eq_toChain

def barycentricSubdivisionMap (X : TopCat.{u}) : simplicialChains R X ⟶ simplicialChains R X where
  f k := barycentricSubdivisionComponent R X k
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    refine SSet.chainComplex_hom_ext fun τ => ?_
    rw [ι_barycentricSubdivisionComponent_assoc, ← toChain_bd, bd_barycentricSubdivision_succ, ι_eq_toChain R τ, ← Category.assoc,
      ← toChain_bd, toChain_barycentricSubdivisionComponent]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.barycentricSubdivisionMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.barycentricSubdivisionMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.barycentricSubdivisionMap ``Submission.DifferentialGeometry.Topology.SingularPair.barycentricSubdivisionMap

@[simp] lemma barycentricSubdivisionMap_f (X : TopCat.{u}) (k : ℕ) : (barycentricSubdivisionMap R X).f k = barycentricSubdivisionComponent R X k := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.barycentricSubdivisionMap_f then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.barycentricSubdivisionMap_f"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.barycentricSubdivisionMap_f ``Submission.DifferentialGeometry.Topology.SingularPair.barycentricSubdivisionMap_f

lemma ι_barycentricSubdivisionMap_f (X : TopCat.{u}) (k : ℕ) (τ : Sing X k) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (barycentricSubdivisionMap R X).f k =
      toChain R (X.toSSetObjEquiv _ τ) k (barycentricSubdivision k (Finsupp.single (idVerts k) 1)) :=
  ι_barycentricSubdivisionComponent R X k τ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι_barycentricSubdivisionMap_f then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι_barycentricSubdivisionMap_f"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι_barycentricSubdivisionMap_f ``Submission.DifferentialGeometry.Topology.SingularPair.ι_barycentricSubdivisionMap_f

lemma toChain_barycentricSubdivisionMap_f {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) (k : ℕ) (c : AffChain k m) :
    toChain R σ k c ≫ (barycentricSubdivisionMap R X).f k = toChain R σ k (barycentricSubdivision k c) :=
  toChain_barycentricSubdivisionComponent R σ k c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.toChain_barycentricSubdivisionMap_f then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.toChain_barycentricSubdivisionMap_f"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.toChain_barycentricSubdivisionMap_f ``Submission.DifferentialGeometry.Topology.SingularPair.toChain_barycentricSubdivisionMap_f

theorem barycentricSubdivisionMap_natural {X Y : TopCat.{u}} (f : X ⟶ Y) :
    SSet.chainComplexMap (TopCat.toSSet.map f) R ≫ barycentricSubdivisionMap R Y =
      barycentricSubdivisionMap R X ≫ SSet.chainComplexMap (TopCat.toSSet.map f) R := by
  refine HomologicalComplex.hom_ext _ _ fun k => SSet.chainComplex_hom_ext fun τ => ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, SSet.ι_chainComplexMap_f_assoc,
    barycentricSubdivisionMap_f, barycentricSubdivisionMap_f, ι_barycentricSubdivisionComponent, ι_barycentricSubdivisionComponent_assoc, toChain_map, toSSetObjEquiv_toSSet_map_app]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.barycentricSubdivisionMap_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.barycentricSubdivisionMap_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.barycentricSubdivisionMap_natural ``Submission.DifferentialGeometry.Topology.SingularPair.barycentricSubdivisionMap_natural

theorem subdivisionHomotopyComponent_natural {X Y : TopCat.{u}} (f : X ⟶ Y) (k : ℕ) :
    (SSet.chainComplexMap (TopCat.toSSet.map f) R).f k ≫ subdivisionHomotopyComponent R Y k =
      subdivisionHomotopyComponent R X k ≫ (SSet.chainComplexMap (TopCat.toSSet.map f) R).f (k + 1) := by
  refine SSet.chainComplex_hom_ext fun τ => ?_
  rw [SSet.ι_chainComplexMap_f_assoc, ι_subdivisionHomotopyComponent, ι_subdivisionHomotopyComponent_assoc, toChain_map,
    toSSetObjEquiv_toSSet_map_app]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.subdivisionHomotopyComponent_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.subdivisionHomotopyComponent_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.subdivisionHomotopyComponent_natural ``Submission.DifferentialGeometry.Topology.SingularPair.subdivisionHomotopyComponent_natural

def homotopyIdBarycentricSubdivision (X : TopCat.{u}) : Homotopy (𝟙 (simplicialChains R X)) (barycentricSubdivisionMap R X) where
  hom i j := if h : i + 1 = j then subdivisionHomotopyComponent R X i ≫ ((simplicialChains R X).XIsoOfEq h).hom else 0
  zero i j hij := by
    have : ¬ i + 1 = j := hij
    simp [this]
  comm i := by
    rcases i with _ | i
    · rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dif_pos rfl, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id,
        zero_add, HomologicalComplex.id_f, barycentricSubdivisionMap_f]
      refine SSet.chainComplex_hom_ext fun τ => ?_
      rw [Category.comp_id, Preadditive.comp_add, ι_subdivisionHomotopyComponent_assoc, ← toChain_bd, bd_subdivisionHomotopyMap_zero,
        map_zero, zero_add, ι_barycentricSubdivisionComponent, barycentricSubdivision_zero, LinearMap.id_apply, ι_eq_toChain]
    · rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dif_pos rfl, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id,
        HomologicalComplex.id_f, barycentricSubdivisionMap_f]
      refine SSet.chainComplex_hom_ext fun τ => ?_
      rw [Category.comp_id, Preadditive.comp_add, Preadditive.comp_add, ι_subdivisionHomotopyComponent_assoc,
        ← toChain_bd, ι_barycentricSubdivisionComponent, ι_eq_toChain R τ, ← Category.assoc, ← toChain_bd,
        toChain_subdivisionHomotopyComponent, ← map_add, ← map_add, add_comm (subdivisionHomotopyMap _ _), bd_subdivisionHomotopyMap_succ_add_subdivisionHomotopyMap_bd,
        sub_add_cancel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homotopyIdBarycentricSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homotopyIdBarycentricSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homotopyIdBarycentricSubdivision ``Submission.DifferentialGeometry.Topology.SingularPair.homotopyIdBarycentricSubdivision

def homotopyBarycentricSubdivisionId (X : TopCat.{u}) : Homotopy (barycentricSubdivisionMap R X) (𝟙 (simplicialChains R X)) :=
  (homotopyIdBarycentricSubdivision R X).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homotopyBarycentricSubdivisionId then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homotopyBarycentricSubdivisionId"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homotopyBarycentricSubdivisionId ``Submission.DifferentialGeometry.Topology.SingularPair.homotopyBarycentricSubdivisionId

def iteratedBarycentricSubdivisionMap (X : TopCat.{u}) : ℕ → (simplicialChains R X ⟶ simplicialChains R X)
  | 0 => 𝟙 _
  | j + 1 => iteratedBarycentricSubdivisionMap X j ≫ barycentricSubdivisionMap R X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.iteratedBarycentricSubdivisionMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.iteratedBarycentricSubdivisionMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.iteratedBarycentricSubdivisionMap ``Submission.DifferentialGeometry.Topology.SingularPair.iteratedBarycentricSubdivisionMap

@[simp] lemma iteratedBarycentricSubdivisionMap_zero (X : TopCat.{u}) : iteratedBarycentricSubdivisionMap R X 0 = 𝟙 _ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.iteratedBarycentricSubdivisionMap_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.iteratedBarycentricSubdivisionMap_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.iteratedBarycentricSubdivisionMap_zero ``Submission.DifferentialGeometry.Topology.SingularPair.iteratedBarycentricSubdivisionMap_zero

lemma iteratedBarycentricSubdivisionMap_succ (X : TopCat.{u}) (j : ℕ) : iteratedBarycentricSubdivisionMap R X (j + 1) = iteratedBarycentricSubdivisionMap R X j ≫ barycentricSubdivisionMap R X := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.iteratedBarycentricSubdivisionMap_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.iteratedBarycentricSubdivisionMap_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.iteratedBarycentricSubdivisionMap_succ ``Submission.DifferentialGeometry.Topology.SingularPair.iteratedBarycentricSubdivisionMap_succ

lemma toChain_iteratedBarycentricSubdivisionMap_f {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) (k j : ℕ) (c : AffChain k m) :
    toChain R σ k c ≫ (iteratedBarycentricSubdivisionMap R X j).f k = toChain R σ k (iteratedBarycentricSubdivision k j c) := by
  induction j generalizing c with
  | zero => simp
  | succ j ih => rw [iteratedBarycentricSubdivisionMap_succ, HomologicalComplex.comp_f, ← Category.assoc, ih, barycentricSubdivisionMap_f,
      toChain_barycentricSubdivisionComponent, iteratedBarycentricSubdivision_succ, LinearMap.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.toChain_iteratedBarycentricSubdivisionMap_f then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.toChain_iteratedBarycentricSubdivisionMap_f"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.toChain_iteratedBarycentricSubdivisionMap_f ``Submission.DifferentialGeometry.Topology.SingularPair.toChain_iteratedBarycentricSubdivisionMap_f

@[reassoc]
lemma ι_iteratedBarycentricSubdivisionMap_f (X : TopCat.{u}) (k j : ℕ) (τ : Sing X k) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (iteratedBarycentricSubdivisionMap R X j).f k =
      toChain R (X.toSSetObjEquiv _ τ) k (iteratedBarycentricSubdivision k j (Finsupp.single (idVerts k) 1)) := by
  rw [ι_eq_toChain R τ, toChain_iteratedBarycentricSubdivisionMap_f]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι_iteratedBarycentricSubdivisionMap_f then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι_iteratedBarycentricSubdivisionMap_f"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι_iteratedBarycentricSubdivisionMap_f ``Submission.DifferentialGeometry.Topology.SingularPair.ι_iteratedBarycentricSubdivisionMap_f

lemma iteratedBarycentricSubdivisionMap_natural {X Y : TopCat.{u}} (f : X ⟶ Y) (j : ℕ) :
    SSet.chainComplexMap (TopCat.toSSet.map f) R ≫ iteratedBarycentricSubdivisionMap R Y j =
      iteratedBarycentricSubdivisionMap R X j ≫ SSet.chainComplexMap (TopCat.toSSet.map f) R := by
  induction j with
  | zero => simp
  | succ j ih => rw [iteratedBarycentricSubdivisionMap_succ, iteratedBarycentricSubdivisionMap_succ, ← Category.assoc, ih, Category.assoc, barycentricSubdivisionMap_natural,
      Category.assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.iteratedBarycentricSubdivisionMap_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.iteratedBarycentricSubdivisionMap_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.iteratedBarycentricSubdivisionMap_natural ``Submission.DifferentialGeometry.Topology.SingularPair.iteratedBarycentricSubdivisionMap_natural

lemma toChain_eq_toChainSub {X : TopCat.{u}} (A : (TopCat.toSSet.obj X).Subcomplex) {m : ℕ}
    (σ : C(Δ m, X)) (k : ℕ) (c : AffChain k m)
    (hc : ∀ w ∈ c.support, affSing σ w ∈ A.obj _) :
    toChain R σ k c = toChainSub R A σ k c ≫ (SSet.chainComplexMap A.ι R).f k :=
  (toChainSub_ι R A σ k c hc).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.toChain_eq_toChainSub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.toChain_eq_toChainSub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.toChain_eq_toChainSub ``Submission.DifferentialGeometry.Topology.SingularPair.toChain_eq_toChainSub

end DifferentialGeometry.Topology.SingularPair
