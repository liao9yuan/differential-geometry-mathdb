import Submission.DifferentialGeometry.Topology.Homology.SingularPair
import Submission.DifferentialGeometry.MathlibCompat.StdSimplex
import Mathlib.Analysis.Normed.Module.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.Submission.CategoryTheory _root_.CategoryTheory.Limits _root_.Submission.CategoryTheory.Limits _root_.AlgebraicTopology _root_.Submission.DifferentialGeometry.MathlibCompat
open scoped _root_.Simplicial

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

abbrev Δ (n : ℕ) : Type := StdSimplex ℝ (Fin (n + 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Δ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Δ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Δ ``Submission.DifferentialGeometry.Topology.SingularPair.Δ

abbrev wt {n : ℕ} (t : Δ n) : Fin (n + 1) → ℝ := t.weights

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.wt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.wt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.wt ``Submission.DifferentialGeometry.Topology.SingularPair.wt

lemma weights_affineMapMk_apply {m n : ℕ} (v : Fin (m + 1) → Δ n) (t : Δ m)
    (j : Fin (n + 1)) :
    (StdSimplex.affineMapMk v t).weights j = ∑ i, t.weights i * (v i).weights j := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.weights_affineMapMk_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.weights_affineMapMk_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.weights_affineMapMk_apply ``Submission.DifferentialGeometry.Topology.SingularPair.weights_affineMapMk_apply

lemma continuous_affineMapMk {m n : ℕ} (v : Fin (m + 1) → Δ n) :
    Continuous (StdSimplex.affineMapMk v) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  change Continuous (fun t : Δ m => ∑ i, t.val i * (v i).val j)
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp continuous_subtype_val).mul continuous_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.continuous_affineMapMk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.continuous_affineMapMk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.continuous_affineMapMk ``Submission.DifferentialGeometry.Topology.SingularPair.continuous_affineMapMk

def affineSimplex {m n : ℕ} (v : Fin (m + 1) → Δ n) : C(Δ m, Δ n) :=
  ⟨StdSimplex.affineMapMk v, continuous_affineMapMk v⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.affineSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.affineSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.affineSimplex ``Submission.DifferentialGeometry.Topology.SingularPair.affineSimplex

@[simp] lemma affineSimplex_apply {m n : ℕ} (v : Fin (m + 1) → Δ n) (t : Δ m) :
    affineSimplex v t = StdSimplex.affineMapMk v t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.affineSimplex_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.affineSimplex_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.affineSimplex_apply ``Submission.DifferentialGeometry.Topology.SingularPair.affineSimplex_apply

@[simp] lemma affineSimplex_single_apply {m n : ℕ} (v : Fin (m + 1) → Δ n) (i : Fin (m + 1)) :
    affineSimplex v (.single i) = v i := StdSimplex.affineMapMk_single v i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.affineSimplex_single_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.affineSimplex_single_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.affineSimplex_single_apply ``Submission.DifferentialGeometry.Topology.SingularPair.affineSimplex_single_apply

lemma affineSimplex_single {n : ℕ} :
    affineSimplex (fun i : Fin (n + 1) => (StdSimplex.single i : Δ n)) = .id _ := by
  ext t : 1
  exact StdSimplex.affineMapMk_single_vertices t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.affineSimplex_single then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.affineSimplex_single"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.affineSimplex_single ``Submission.DifferentialGeometry.Topology.SingularPair.affineSimplex_single

lemma affineSimplex_comp_affineSimplex {k m n : ℕ} (v : Fin (m + 1) → Δ n)
    (w : Fin (k + 1) → Δ m) :
    (affineSimplex v).comp (affineSimplex w) = affineSimplex (affineSimplex v ∘ w) := by
  ext t : 1
  exact StdSimplex.affineMapMk_comp v w t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.affineSimplex_comp_affineSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.affineSimplex_comp_affineSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.affineSimplex_comp_affineSimplex ``Submission.DifferentialGeometry.Topology.SingularPair.affineSimplex_comp_affineSimplex

lemma affineSimplex_single_comp {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    affineSimplex (fun i => (StdSimplex.single (f i) : Δ n)) =
      ⟨StdSimplex.map f, StdSimplex.continuous_map ℝ f⟩ := by
  ext t : 1
  exact StdSimplex.affineMapMk_single_comp f t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.affineSimplex_single_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.affineSimplex_single_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.affineSimplex_single_comp ``Submission.DifferentialGeometry.Topology.SingularPair.affineSimplex_single_comp

lemma affineSimplex_comp_map {k m n : ℕ} (v : Fin (m + 1) → Δ n)
    (f : Fin (k + 1) → Fin (m + 1)) :
    (affineSimplex v).comp ⟨StdSimplex.map f, StdSimplex.continuous_map ℝ f⟩ =
      affineSimplex (v ∘ f) := by
  rw [← affineSimplex_single_comp, affineSimplex_comp_affineSimplex]
  congr 1
  funext i
  exact affineSimplex_single_apply v (f i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.affineSimplex_comp_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.affineSimplex_comp_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.affineSimplex_comp_map ``Submission.DifferentialGeometry.Topology.SingularPair.affineSimplex_comp_map

lemma toSSetObjEquiv_symm_δ {X : TopCat.{u}} {n : ℕ} (f : C(Δ (n + 1), X)) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj X).δ i ((X.toSSetObjEquiv _).symm f) =
      (X.toSSetObjEquiv _).symm (f.comp (affineSimplex fun j => .single (i.succAbove j))) := by
  rw [affineSimplex_single_comp]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.toSSetObjEquiv_symm_δ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.toSSetObjEquiv_symm_δ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.toSSetObjEquiv_symm_δ ``Submission.DifferentialGeometry.Topology.SingularPair.toSSetObjEquiv_symm_δ

def bary {m n : ℕ} (v : Fin (m + 1) → Δ n) : Δ n :=
  affineSimplex v StdSimplex.barycenter

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.bary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.bary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.bary ``Submission.DifferentialGeometry.Topology.SingularPair.bary

lemma affineSimplex_bary {k m n : ℕ} (u : Fin (m + 1) → Δ n) (v : Fin (k + 1) → Δ m) :
    affineSimplex u (bary v) = bary (affineSimplex u ∘ v) :=
  StdSimplex.affineMapMk_comp u v StdSimplex.barycenter

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.affineSimplex_bary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.affineSimplex_bary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.affineSimplex_bary ``Submission.DifferentialGeometry.Topology.SingularPair.affineSimplex_bary

lemma bary_const {m n : ℕ} (b : Δ n) : bary (fun _ : Fin (m + 1) => b) = b := by
  apply Subtype.ext
  funext j
  change (∑ i : Fin (m + 1), StdSimplex.barycenter.weights i * b.weights j) = b.weights j
  rw [← Finset.sum_mul, StdSimplex.sum_weights, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.bary_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.bary_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.bary_const ``Submission.DifferentialGeometry.Topology.SingularPair.bary_const

lemma weights_bary {m n : ℕ} (v : Fin (m + 1) → Δ n) (j : Fin (n + 1)) :
    (bary v).weights j = ∑ i, ((m : ℝ) + 1)⁻¹ * (v i).weights j := by
  simp [bary, StdSimplex.barycenter, StdSimplex.weights,
    stdSimplex.barycenter]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.weights_bary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.weights_bary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.weights_bary ``Submission.DifferentialGeometry.Topology.SingularPair.weights_bary

abbrev cone {m n : ℕ} (b : Δ n) (v : Fin m → Δ n) : Fin (m + 1) → Δ n := Fin.cons b v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.cone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.cone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.cone ``Submission.DifferentialGeometry.Topology.SingularPair.cone

lemma cone_comp_succAbove_zero {m n : ℕ} (b : Δ n) (v : Fin m → Δ n) :
    cone b v ∘ (0 : Fin (m + 1)).succAbove = v := by
  funext j; simp [cone]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.cone_comp_succAbove_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.cone_comp_succAbove_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.cone_comp_succAbove_zero ``Submission.DifferentialGeometry.Topology.SingularPair.cone_comp_succAbove_zero

lemma cone_comp_succAbove_succ {m n : ℕ} (b : Δ n) (v : Fin (m + 1) → Δ n) (i : Fin (m + 1)) :
    cone b v ∘ i.succ.succAbove = cone b (v ∘ i.succAbove) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [cone]
  · simp [cone, Fin.succ_succAbove_succ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.cone_comp_succAbove_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.cone_comp_succAbove_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.cone_comp_succAbove_succ ``Submission.DifferentialGeometry.Topology.SingularPair.cone_comp_succAbove_succ

lemma cone_fin_zero {n : ℕ} (b : Δ n) (v : Fin 0 → Δ n) : cone b v = fun _ => b := by
  funext j
  obtain rfl : j = 0 := Fin.ext (Nat.lt_one_iff.mp j.isLt)
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.cone_fin_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.cone_fin_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.cone_fin_zero ``Submission.DifferentialGeometry.Topology.SingularPair.cone_fin_zero

lemma comp_cone {m n n' : ℕ} (u : Δ n → Δ n') (b : Δ n) (v : Fin m → Δ n) :
    u ∘ cone b v = cone (u b) (u ∘ v) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp [cone]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.comp_cone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.comp_cone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.comp_cone ``Submission.DifferentialGeometry.Topology.SingularPair.comp_cone

abbrev AffChain (k n : ℕ) : Type := (Fin (k + 1) → Δ n) →₀ ℤ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain

namespace AffChain

def push {n n' : ℕ} (u : Δ n → Δ n') (k : ℕ) : AffChain k n →ₗ[ℤ] AffChain k n' :=
  Finsupp.lmapDomain ℤ ℤ (fun w => u ∘ w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.push then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.push"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.push ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.push

def coneL {n : ℕ} (b : Δ n) (k : ℕ) : AffChain k n →ₗ[ℤ] AffChain (k + 1) n :=
  Finsupp.lmapDomain ℤ ℤ (cone b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.coneL then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.coneL"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.coneL ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.coneL

def face {n : ℕ} (k : ℕ) (i : Fin (k + 2)) : AffChain (k + 1) n →ₗ[ℤ] AffChain k n :=
  Finsupp.lmapDomain ℤ ℤ (fun w => w ∘ i.succAbove)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.face ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.face

def bd {n : ℕ} (k : ℕ) : AffChain (k + 1) n →ₗ[ℤ] AffChain k n :=
  ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • face k i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.bd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.bd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.bd ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.bd

def eps {n : ℕ} : AffChain 0 n →ₗ[ℤ] ℤ := Finsupp.linearCombination ℤ (fun _ => 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.eps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.eps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.eps ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.eps

@[simp] lemma push_single {n n' : ℕ} (u : Δ n → Δ n') {k : ℕ} (w : Fin (k + 1) → Δ n)
    (z : ℤ) :
    push u k (Finsupp.single w z) = Finsupp.single (u ∘ w) z := by
  simp [push]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.push_single then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.push_single"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.push_single ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.push_single

@[simp] lemma coneL_single {n : ℕ} (b : Δ n) {k : ℕ} (w : Fin (k + 1) → Δ n) (z : ℤ) :
    coneL b k (Finsupp.single w z) = Finsupp.single (cone b w) z := by
  simp [coneL]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.coneL_single then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.coneL_single"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.coneL_single ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.coneL_single

@[simp] lemma face_single {n : ℕ} {k : ℕ} (i : Fin (k + 2)) (w : Fin (k + 2) → Δ n)
    (z : ℤ) :
    face k i (Finsupp.single w z) = Finsupp.single (w ∘ i.succAbove) z := by
  simp [face]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.face_single then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.face_single"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.face_single ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.face_single

lemma bd_single {n : ℕ} {k : ℕ} (w : Fin (k + 2) → Δ n) (z : ℤ) :
    bd k (Finsupp.single w z) =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (w ∘ i.succAbove) z := by
  simp only [bd, LinearMap.sum_apply, LinearMap.smul_apply, face_single]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.bd_single then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.bd_single"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.bd_single ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.bd_single

@[simp] lemma eps_single {n : ℕ} (w : Fin 1 → Δ n) (z : ℤ) :
    eps (Finsupp.single w z) = z := by
  simp [eps]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.eps_single then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.eps_single"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.eps_single ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.eps_single

lemma push_comp_push {n n' n'' : ℕ} (u : Δ n → Δ n') (u' : Δ n' → Δ n'') (k : ℕ) :
    (push u' k).comp (push u k) = push (u' ∘ u) k := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, push_single, Function.comp_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_push then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_push"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_push ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_push

lemma push_id {n : ℕ} (k : ℕ) : push (id : Δ n → Δ n) k = LinearMap.id := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, push_single, Function.id_comp,
    LinearMap.id_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.push_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.push_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.push_id ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.push_id

lemma push_comp_coneL {n n' : ℕ} (u : Δ n → Δ n') (b : Δ n) (k : ℕ) :
    (push u (k + 1)).comp (coneL b k) = (coneL (u b) k).comp (push u k) := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, push_single, coneL_single, comp_cone]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_coneL then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_coneL"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_coneL ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_coneL

lemma push_comp_face {n n' : ℕ} (u : Δ n → Δ n') (k : ℕ) (i : Fin (k + 2)) :
    (push u k).comp (face k i) = (face k i).comp (push u (k + 1)) := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, push_single, face_single,
    Function.comp_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_face ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_face

lemma push_comp_bd {n n' : ℕ} (u : Δ n → Δ n') (k : ℕ) :
    (push u k).comp (bd k) = (bd k).comp (push u (k + 1)) := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, push_single, bd_single, map_sum,
    map_zsmul, Function.comp_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_bd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_bd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_bd ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.push_comp_bd

lemma eps_comp_push {n n' : ℕ} (u : Δ n → Δ n') :
    eps.comp (push u 0) = eps := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, push_single, eps_single]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.eps_comp_push then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.eps_comp_push"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.eps_comp_push ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.eps_comp_push

lemma eps_comp_bd {n : ℕ} : eps.comp (bd 0 : AffChain 1 n →ₗ[ℤ] AffChain 0 n) = 0 := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, bd_single, map_sum, map_zsmul,
    eps_single, LinearMap.zero_comp, LinearMap.zero_apply]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.eps_comp_bd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.eps_comp_bd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.eps_comp_bd ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.eps_comp_bd

lemma face_comp_coneL_zero {n : ℕ} (b : Δ n) (k : ℕ) :
    (face k 0).comp (coneL b k) = LinearMap.id := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, coneL_single, face_single,
    cone_comp_succAbove_zero, LinearMap.id_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.face_comp_coneL_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.face_comp_coneL_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.face_comp_coneL_zero ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.face_comp_coneL_zero

lemma face_comp_coneL_succ {n : ℕ} (b : Δ n) (k : ℕ) (i : Fin (k + 2)) :
    (face (k + 1) i.succ).comp (coneL b (k + 1)) = (coneL b k).comp (face k i) := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, coneL_single, face_single,
    cone_comp_succAbove_succ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.face_comp_coneL_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.face_comp_coneL_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.face_comp_coneL_succ ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.face_comp_coneL_succ

lemma bd_comp_coneL {n : ℕ} (b : Δ n) (k : ℕ) :
    (bd (k + 1)).comp (coneL b (k + 1)) = LinearMap.id - (coneL b k).comp (bd k) := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.sub_apply,
    LinearMap.id_apply, coneL_single, bd_single, map_sum, map_zsmul]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, cone_comp_succAbove_zero,
    cone_comp_succAbove_succ, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_coneL then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_coneL"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_coneL ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_coneL

lemma bd_coneL_zero {n : ℕ} (b : Δ n) (c : AffChain 0 n) :
    bd 0 (coneL b 0 c) = c - eps c • Finsupp.single (fun _ => b) 1 := by
  have : (bd 0).comp (coneL b 0) =
      LinearMap.id - (Finsupp.lsingle (fun _ => b)).comp (eps (n := n)) := by
    ext w : 2
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.sub_apply,
      LinearMap.id_apply, coneL_single, bd_single, eps_single]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, cone_comp_succAbove_zero,
      cone_comp_succAbove_succ, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
      Finset.univ_eq_empty, Finset.sum_empty, add_zero, cone_fin_zero, sub_eq_add_neg]
  have h := LinearMap.congr_fun this c
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    Finsupp.lsingle_apply] at h
  rw [h, Finsupp.smul_single, smul_eq_mul, mul_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.bd_coneL_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.bd_coneL_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.bd_coneL_zero ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.bd_coneL_zero

lemma neg_one_pow_succAbove_predAbove {k : ℕ} (i : Fin (k + 3)) (j : Fin (k + 2)) :
    (-1 : ℤ) ^ ((i.succAbove j : Fin (k + 3)) : ℕ) *
      (-1) ^ ((j.predAbove i : Fin (k + 2)) : ℕ) = -((-1) ^ (i : ℕ) * (-1) ^ (j : ℕ)) := by
  have key : (i.succAbove j : ℕ) + (j.predAbove i : ℕ) + 1 = i + j ∨
      (i.succAbove j : ℕ) + (j.predAbove i : ℕ) = i + j + 1 := by
    simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val,
      Fin.val_pred, Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
    split_ifs <;> omega
  rw [← pow_add, ← pow_add]
  rcases key with h | h
  · rw [← h, pow_succ]; ring
  · rw [h, pow_succ]; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.neg_one_pow_succAbove_predAbove then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.neg_one_pow_succAbove_predAbove"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.neg_one_pow_succAbove_predAbove ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.neg_one_pow_succAbove_predAbove

lemma bd_comp_bd {n : ℕ} (k : ℕ) :
    (bd k).comp (bd (k + 1) : AffChain (k + 2) n →ₗ[ℤ] _) = 0 := by
  ext w : 2
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_comp,
    LinearMap.zero_apply, bd_single, map_sum, map_zsmul, Finset.smul_sum, smul_smul,
    Function.comp_assoc]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  refine Finset.sum_ninvolution (fun p => (p.1.succAbove p.2, p.2.predAbove p.1)) ?_ ?_
    (fun _ => Finset.mem_univ _) ?_
  · rintro ⟨i, j⟩
    have hf : w ∘ (i.succAbove j).succAbove ∘ (j.predAbove i).succAbove =
        w ∘ i.succAbove ∘ j.succAbove := by
      funext l
      simp only [Function.comp_apply, Fin.succAbove_succAbove_succAbove_predAbove]
    simp only [hf, neg_one_pow_succAbove_predAbove, neg_smul, add_neg_cancel]
  · rintro ⟨i, j⟩ - h
    exact Fin.succAbove_ne i j (congrArg Prod.fst h)
  · rintro ⟨i, j⟩
    exact Prod.ext (Fin.succAbove_succAbove_predAbove i j) (Fin.predAbove_predAbove_succAbove i j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_bd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_bd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_bd ``Submission.DifferentialGeometry.Topology.SingularPair.AffChain.bd_comp_bd

end AffChain

abbrev sing {X : TopCat.{u}} {k : ℕ} (f : C(Δ k, X)) : (TopCat.toSSet.obj X) _⦋k⦌ :=
  (X.toSSetObjEquiv _).symm f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.sing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.sing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.sing ``Submission.DifferentialGeometry.Topology.SingularPair.sing

abbrev affSing {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) {k : ℕ} (w : Fin (k + 1) → Δ m) :
    (TopCat.toSSet.obj X) _⦋k⦌ :=
  sing (σ.comp (affineSimplex w))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.affSing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.affSing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.affSing ``Submission.DifferentialGeometry.Topology.SingularPair.affSing

lemma δ_sing {X : TopCat.{u}} {k : ℕ} (f : C(Δ (k + 1), X)) (i : Fin (k + 2)) :
    (TopCat.toSSet.obj X).δ i (sing f) =
      sing (f.comp (affineSimplex fun j => .single (i.succAbove j))) :=
  toSSetObjEquiv_symm_δ f i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.δ_sing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.δ_sing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.δ_sing ``Submission.DifferentialGeometry.Topology.SingularPair.δ_sing

lemma δ_affSing {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) {k : ℕ} (w : Fin (k + 2) → Δ m)
    (i : Fin (k + 2)) :
    (TopCat.toSSet.obj X).δ i (affSing σ w) = affSing σ (w ∘ i.succAbove) := by
  change (TopCat.toSSet.obj X).δ i (sing (σ.comp (affineSimplex w))) =
    sing (σ.comp (affineSimplex (w ∘ i.succAbove)))
  rw [δ_sing, ContinuousMap.comp_assoc, affineSimplex_comp_affineSimplex]
  congr 3
  funext j
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.δ_affSing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.δ_affSing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.δ_affSing ``Submission.DifferentialGeometry.Topology.SingularPair.δ_affSing

@[simp] lemma rightComp_apply_eq {V : Type*} [_root_.CategoryTheory.Category V] [_root_.CategoryTheory.Preadditive V] (P : V) {Q S : V}
    (g : Q ⟶ S) (f : P ⟶ Q) : Preadditive.rightComp P g f = f ≫ g := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.rightComp_apply_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.rightComp_apply_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.rightComp_apply_eq ``Submission.DifferentialGeometry.Topology.SingularPair.rightComp_apply_eq

lemma affSing_comp {X : TopCat.{u}} {m m' : ℕ} (σ : C(Δ m, X)) (v : Fin (m' + 1) → Δ m)
    {k : ℕ} (w : Fin (k + 1) → Δ m') :
    affSing (σ.comp (affineSimplex v)) w = affSing σ (affineSimplex v ∘ w) := by
  change sing ((σ.comp (affineSimplex v)).comp (affineSimplex w)) =
    sing (σ.comp (affineSimplex (affineSimplex v ∘ w)))
  rw [ContinuousMap.comp_assoc, affineSimplex_comp_affineSimplex]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.affSing_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.affSing_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.affSing_comp ``Submission.DifferentialGeometry.Topology.SingularPair.affSing_comp

lemma toSSet_map_app_sing {X Y : TopCat.{u}} (f : X ⟶ Y) {k : ℕ} (g : C(Δ k, X)) :
    (TopCat.toSSet.map f).app _ (sing g) = sing (f.hom.comp g) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.toSSet_map_app_sing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.toSSet_map_app_sing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.toSSet_map_app_sing ``Submission.DifferentialGeometry.Topology.SingularPair.toSSet_map_app_sing

variable (R : ModuleCat.{u} ℤ)

abbrev simplicialChains (X : TopCat.{u}) : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  (TopCat.toSSet.obj X).chainComplex R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.simplicialChains then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.simplicialChains"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.simplicialChains ``Submission.DifferentialGeometry.Topology.SingularPair.simplicialChains

example (X : TopCat.{u}) : simplicialChains R X = singularChains R X := rfl

lemma singularChainFunctor_map_eq {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (singularChainFunctor R).map f = SSet.chainComplexMap (TopCat.toSSet.map f) R := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.singularChainFunctor_map_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.singularChainFunctor_map_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.singularChainFunctor_map_eq ``Submission.DifferentialGeometry.Topology.SingularPair.singularChainFunctor_map_eq

def toChain {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) (k : ℕ) :
    AffChain k m →+ (R ⟶ (simplicialChains R X).X k) :=
  Finsupp.liftAddHom fun w => zmultiplesHom _ ((TopCat.toSSet.obj X).ιChainComplex (affSing σ w))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.toChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.toChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.toChain ``Submission.DifferentialGeometry.Topology.SingularPair.toChain

@[simp] lemma toChain_single {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) {k : ℕ}
    (w : Fin (k + 1) → Δ m) (z : ℤ) :
    toChain R σ k (Finsupp.single w z) =
      z • (TopCat.toSSet.obj X).ιChainComplex (affSing σ w) := by
  simp [toChain]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.toChain_single then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.toChain_single"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.toChain_single ``Submission.DifferentialGeometry.Topology.SingularPair.toChain_single

lemma toChain_apply {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) {k : ℕ} (c : AffChain k m) :
    toChain R σ k c =
      c.sum fun w z => z • (TopCat.toSSet.obj X).ιChainComplex (affSing σ w) := by
  rw [toChain, Finsupp.liftAddHom_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.toChain_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.toChain_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.toChain_apply ``Submission.DifferentialGeometry.Topology.SingularPair.toChain_apply

lemma toChain_bd {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) (k : ℕ) (c : AffChain (k + 1) m) :
    toChain R σ k (AffChain.bd k c) = toChain R σ (k + 1) c ≫ (simplicialChains R X).d (k + 1) k := by
  suffices (toChain R σ k).comp (AffChain.bd k).toAddMonoidHom =
      (Preadditive.rightComp R ((simplicialChains R X).d (k + 1) k)).comp (toChain R σ (k + 1)) from
    DFunLike.congr_fun this c
  ext w : 2
  simp only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply, LinearMap.toAddMonoidHom_coe,
    AffChain.bd_single, map_sum, map_zsmul, toChain_single, one_smul, rightComp_apply_eq,
    SSet.ιChainComplex_d, δ_affSing]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.toChain_bd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.toChain_bd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.toChain_bd ``Submission.DifferentialGeometry.Topology.SingularPair.toChain_bd

lemma toChain_push {X : TopCat.{u}} {m m' : ℕ} (σ : C(Δ m, X)) (v : Fin (m' + 1) → Δ m)
    (k : ℕ) (c : AffChain k m') :
    toChain R σ k (AffChain.push (affineSimplex v) k c) =
      toChain R (σ.comp (affineSimplex v)) k c := by
  suffices (toChain R σ k).comp (AffChain.push (affineSimplex v) k).toAddMonoidHom =
      toChain R (σ.comp (affineSimplex v)) k from DFunLike.congr_fun this c
  ext w : 2
  simp only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply, LinearMap.toAddMonoidHom_coe,
    AffChain.push_single, toChain_single, affSing_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.toChain_push then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.toChain_push"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.toChain_push ``Submission.DifferentialGeometry.Topology.SingularPair.toChain_push

lemma toChain_map {X Y : TopCat.{u}} (f : X ⟶ Y) {m : ℕ} (σ : C(Δ m, X)) (k : ℕ)
    (c : AffChain k m) :
    toChain R σ k c ≫ (SSet.chainComplexMap (TopCat.toSSet.map f) R).f k =
      toChain R (f.hom.comp σ) k c := by
  suffices (Preadditive.rightComp R ((SSet.chainComplexMap (TopCat.toSSet.map f) R).f k)).comp
      (toChain R σ k) = toChain R (f.hom.comp σ) k from DFunLike.congr_fun this c
  ext w : 2
  simp only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply, toChain_single,
    rightComp_apply_eq, SSet.ι_chainComplexMap_f, toSSet_map_app_sing, one_smul]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.toChain_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.toChain_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.toChain_map ``Submission.DifferentialGeometry.Topology.SingularPair.toChain_map

abbrev idVerts (m : ℕ) : Fin (m + 1) → Δ m := fun i => StdSimplex.single i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.idVerts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.idVerts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.idVerts ``Submission.DifferentialGeometry.Topology.SingularPair.idVerts

lemma affSing_idVerts {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) :
    affSing σ (idVerts m) = sing σ := by
  simp [affSing, affineSimplex_single]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.affSing_idVerts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.affSing_idVerts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.affSing_idVerts ``Submission.DifferentialGeometry.Topology.SingularPair.affSing_idVerts

lemma toChain_single_idVerts {X : TopCat.{u}} {m : ℕ} (σ : C(Δ m, X)) :
    toChain R σ m (Finsupp.single (idVerts m) 1) =
      (TopCat.toSSet.obj X).ιChainComplex (sing σ) := by
  simp [affSing_idVerts]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.toChain_single_idVerts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.toChain_single_idVerts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.toChain_single_idVerts ``Submission.DifferentialGeometry.Topology.SingularPair.toChain_single_idVerts

open _root_.Classical in
def toChainSub {X : TopCat.{u}} (A : (TopCat.toSSet.obj X).Subcomplex) {m : ℕ} (σ : C(Δ m, X))
    (k : ℕ) : AffChain k m →+ (R ⟶ (A.toSSet.chainComplex R).X k) :=
  Finsupp.liftAddHom fun w => zmultiplesHom _
    (if h : affSing σ w ∈ A.obj _ then A.toSSet.ιChainComplex (⟨affSing σ w, h⟩ : A.obj _)
      else 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.toChainSub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.toChainSub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.toChainSub ``Submission.DifferentialGeometry.Topology.SingularPair.toChainSub

set_option backward.isDefEq.respectTransparency false in
lemma toChainSub_ι {X : TopCat.{u}} (A : (TopCat.toSSet.obj X).Subcomplex) {m : ℕ}
    (σ : C(Δ m, X)) (k : ℕ) (c : AffChain k m)
    (hc : ∀ w ∈ c.support, affSing σ w ∈ A.obj _) :
    toChainSub R A σ k c ≫ (SSet.chainComplexMap A.ι R).f k = toChain R σ k c := by
  rw [toChain_apply, toChainSub, Finsupp.liftAddHom_apply]
  simp only [zmultiplesHom_apply, Finsupp.sum]
  rw [Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Preadditive.zsmul_comp, dif_pos (hc w hw), SSet.ι_chainComplexMap_f]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.toChainSub_ι then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.toChainSub_ι"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.toChainSub_ι ``Submission.DifferentialGeometry.Topology.SingularPair.toChainSub_ι

lemma wt_affineSimplex {m n : ℕ} (v : Fin (m + 1) → Δ n) (t : Δ m) :
    wt (affineSimplex v t) = ∑ i, t.weights i • wt (v i) := by
  funext j
  simp [Finset.sum_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.wt_affineSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.wt_affineSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.wt_affineSimplex ``Submission.DifferentialGeometry.Topology.SingularPair.wt_affineSimplex

lemma wt_affineSimplex_mem_convexHull {m n : ℕ} (v : Fin (m + 1) → Δ n) (t : Δ m) :
    wt (affineSimplex v t) ∈ _root_.convexHull ℝ (Set.range (wt ∘ v)) := by
  rw [wt_affineSimplex]
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => t.weights_nonneg i) (by simp)
    (fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.wt_affineSimplex_mem_convexHull then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.wt_affineSimplex_mem_convexHull"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.wt_affineSimplex_mem_convexHull ``Submission.DifferentialGeometry.Topology.SingularPair.wt_affineSimplex_mem_convexHull

lemma range_wt_comp_affineSimplex_subset {m n : ℕ} (v : Fin (m + 1) → Δ n) :
    Set.range (wt ∘ affineSimplex v) ⊆ _root_.convexHull ℝ (Set.range (wt ∘ v)) := by
  rintro _ ⟨t, rfl⟩
  exact wt_affineSimplex_mem_convexHull v t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.range_wt_comp_affineSimplex_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.range_wt_comp_affineSimplex_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.range_wt_comp_affineSimplex_subset ``Submission.DifferentialGeometry.Topology.SingularPair.range_wt_comp_affineSimplex_subset

lemma isBounded_range_wt (n : ℕ) : Bornology.IsBounded (Set.range (wt (n := n))) :=
  StdSimplex.isBounded_range_toFun_comp_weights _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isBounded_range_wt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isBounded_range_wt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isBounded_range_wt ``Submission.DifferentialGeometry.Topology.SingularPair.isBounded_range_wt

lemma isBounded_of_subset_range_wt {n : ℕ} {s : Set (Fin (n + 1) → ℝ)}
    (hs : s ⊆ Set.range wt) : Bornology.IsBounded s :=
  (isBounded_range_wt n).subset hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isBounded_of_subset_range_wt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isBounded_of_subset_range_wt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isBounded_of_subset_range_wt ``Submission.DifferentialGeometry.Topology.SingularPair.isBounded_of_subset_range_wt

lemma isBounded_range_wt_comp {n : ℕ} {α : Type*} (v : α → Δ n) :
    Bornology.IsBounded (Set.range (wt ∘ v)) :=
  isBounded_of_subset_range_wt (by rintro _ ⟨i, rfl⟩; exact ⟨v i, rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isBounded_range_wt_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isBounded_range_wt_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isBounded_range_wt_comp ``Submission.DifferentialGeometry.Topology.SingularPair.isBounded_range_wt_comp

lemma diam_range_wt_le (n : ℕ) : Metric.diam (Set.range (wt (n := n))) ≤ 1 :=
  StdSimplex.diam_range_toFun_comp_weights_subset_closedBall _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.diam_range_wt_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.diam_range_wt_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.diam_range_wt_le ``Submission.DifferentialGeometry.Topology.SingularPair.diam_range_wt_le

lemma wt_bary {m n : ℕ} (v : Fin (m + 1) → Δ n) :
    wt (bary v) = ∑ i, ((m : ℝ) + 1)⁻¹ • wt (v i) := by
  funext j; simp [weights_bary, Finset.sum_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.wt_bary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.wt_bary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.wt_bary ``Submission.DifferentialGeometry.Topology.SingularPair.wt_bary

lemma dist_wt_bary_le {m n : ℕ} (v : Fin (m + 1) → Δ n) (j : Fin (m + 1)) :
    dist (wt (bary v)) (wt (v j)) ≤ (m / (m + 1 : ℝ)) * Metric.diam (Set.range (wt ∘ v)) := by
  classical
  have hb := isBounded_range_wt_comp v
  rw [dist_eq_norm, wt_bary]
  have : ∑ i, ((m : ℝ) + 1)⁻¹ • wt (v i) - wt (v j) =
      ∑ i, ((m : ℝ) + 1)⁻¹ • (wt (v i) - wt (v j)) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [mul_inv_cancel₀ (by positivity), one_smul]
  rw [this]
  calc ‖∑ i, ((m : ℝ) + 1)⁻¹ • (wt (v i) - wt (v j))‖
      ≤ ∑ i, ‖((m : ℝ) + 1)⁻¹ • (wt (v i) - wt (v j))‖ := norm_sum_le _ _
    _ = ∑ i ∈ Finset.univ.erase j, ((m : ℝ) + 1)⁻¹ * ‖wt (v i) - wt (v j)‖ := by
        rw [← Finset.sum_erase (s := Finset.univ) (a := j)
          (f := fun i => ‖((m : ℝ) + 1)⁻¹ • (wt (v i) - wt (v j))‖) (by simp)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, Real.norm_of_nonneg (show (0 : ℝ) ≤ ((m : ℝ) + 1)⁻¹ by positivity)]
    _ ≤ ∑ i ∈ Finset.univ.erase j,
          ((m : ℝ) + 1)⁻¹ * Metric.diam (Set.range (wt ∘ v)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        gcongr
        rw [← dist_eq_norm]
        exact Metric.dist_le_diam_of_mem hb ⟨i, rfl⟩ ⟨j, rfl⟩
    _ = (m / (m + 1 : ℝ)) * Metric.diam (Set.range (wt ∘ v)) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin, Nat.add_sub_cancel, nsmul_eq_mul]
        ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.dist_wt_bary_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.dist_wt_bary_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.dist_wt_bary_le ``Submission.DifferentialGeometry.Topology.SingularPair.dist_wt_bary_le

lemma dist_wt_map_le {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (hf : Function.Injective f)
    (s t : Δ m) :
    dist (wt (StdSimplex.map f s)) (wt (StdSimplex.map f t)) ≤ _root_.Dist.dist (wt s) (wt t) := by
  rw [dist_pi_le_iff dist_nonneg]
  intro b
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hb
    have hmap (x : Δ m) : wt (StdSimplex.map f x) (f a) = wt x a := by
      change FunOnFinite.linearMap ℝ ℝ f x (f a) = x a
      rw [FunOnFinite.linearMap_apply_apply]
      classical
      simp [hf.eq_iff, Finset.sum_filter]
    rw [hmap, hmap]
    exact dist_le_pi_dist _ _ a
  · have hmap (x : Δ m) : wt (StdSimplex.map f x) b = 0 := by
      change FunOnFinite.linearMap ℝ ℝ f x b = 0
      rw [FunOnFinite.linearMap_apply_apply]
      classical
      apply Finset.sum_eq_zero
      intro a ha
      have h := (Finset.mem_filter.mp ha).2
      exact (hb ⟨a, h⟩).elim
    rw [hmap, hmap, dist_self]
    exact dist_nonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.dist_wt_map_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.dist_wt_map_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.dist_wt_map_le ``Submission.DifferentialGeometry.Topology.SingularPair.dist_wt_map_le

end DifferentialGeometry.Topology.SingularPair
