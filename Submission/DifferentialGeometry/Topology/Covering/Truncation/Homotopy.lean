import Mathlib.Topology.Path
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Subpath
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

open _root_.Set _root_.unitInterval

def concatTrans {X : Type*} [TopologicalSpace X]
    {k : ℕ} {p : Fin (k + 1) → X}
    (F : (i : Fin k) → _root_.Path (p i.castSucc) (p i.succ)) :
    _root_.Path (p 0) (p (Fin.last k)) :=
  _root_.Path.concat p F

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.concatTrans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.concatTrans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.concatTrans ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.concatTrans

namespace TruncateHomotopy

variable {X : Type*} [TopologicalSpace X]


private def truncParam (t₀ t₁ : ℝ) (s : I) : ℝ := _root_.Min.min (_root_.Max.max (s : ℝ) t₀) t₁

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.TruncateHomotopy.truncParam
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.TruncateHomotopy.truncParam target :: scope.openDecls } }


private def linParam (t₀ t₁ : ℝ) (s : I) : ℝ := (1 - (s : ℝ)) * t₀ + (s : ℝ) * t₁

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.TruncateHomotopy.linParam
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.TruncateHomotopy.linParam target :: scope.openDecls } }

private lemma continuous_truncParam (t₀ t₁ : ℝ) :
    Continuous (truncParam t₀ t₁) := by
  unfold truncParam
  exact (continuous_subtype_val.max continuous_const).min continuous_const

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.TruncateHomotopy.continuous_truncParam
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.TruncateHomotopy.continuous_truncParam target :: scope.openDecls } }

private lemma continuous_linParam (t₀ t₁ : ℝ) :
    Continuous (linParam t₀ t₁) := by
  unfold linParam
  exact ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
    (continuous_subtype_val.mul continuous_const)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.TruncateHomotopy.continuous_linParam
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.TruncateHomotopy.continuous_linParam target :: scope.openDecls } }

private lemma truncParam_zero {t₀ t₁ : ℝ} (h0 : 0 ≤ t₀) (h : t₀ ≤ t₁) :
    truncParam t₀ t₁ (0 : I) = t₀ := by
  unfold truncParam
  rw [Icc.coe_zero, max_eq_right h0, min_eq_left h]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.TruncateHomotopy.truncParam_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.TruncateHomotopy.truncParam_zero target :: scope.openDecls } }

private lemma truncParam_one {t₀ t₁ : ℝ} (h : t₀ ≤ t₁) (h1 : t₁ ≤ 1) :
    truncParam t₀ t₁ (1 : I) = t₁ := by
  unfold truncParam
  rw [Icc.coe_one]
  have h_max : _root_.Max.max (1 : ℝ) t₀ = 1 := max_eq_left (h.trans h1)
  rw [h_max, min_eq_right h1]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.TruncateHomotopy.truncParam_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.TruncateHomotopy.truncParam_one target :: scope.openDecls } }

private lemma linParam_zero (t₀ t₁ : ℝ) :
    linParam t₀ t₁ (0 : I) = t₀ := by
  unfold linParam
  rw [Icc.coe_zero, sub_zero, one_mul, _root_.MulZeroClass.zero_mul, add_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.TruncateHomotopy.linParam_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.TruncateHomotopy.linParam_zero target :: scope.openDecls } }

private lemma linParam_one (t₀ t₁ : ℝ) :
    linParam t₀ t₁ (1 : I) = t₁ := by
  unfold linParam
  rw [Icc.coe_one, sub_self, _root_.MulZeroClass.zero_mul, one_mul, zero_add]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.TruncateHomotopy.linParam_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.TruncateHomotopy.linParam_one target :: scope.openDecls } }

end TruncateHomotopy

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.TruncateHomotopy in
lemma truncateOfLE_homotopic_subpath
    {X : Type*} [TopologicalSpace X] {a b : X} (γ : _root_.Path a b)
    {t₀ t₁ : ℝ} (h : t₀ ≤ t₁) (ht₀ : t₀ ∈ I) (ht₁ : t₁ ∈ I) :
    (γ.truncateOfLE h).Homotopic
      ((γ.subpath ⟨t₀, ht₀⟩ ⟨t₁, ht₁⟩).cast
        (_root_.Path.extend_extends' γ ⟨t₀, ht₀⟩)
        (_root_.Path.extend_extends' γ ⟨t₁, ht₁⟩)) := by
  refine ⟨{
    toFun := fun ut => γ.extend
      ((1 - (ut.1 : ℝ)) * truncParam t₀ t₁ ut.2 + (ut.1 : ℝ) * linParam t₀ t₁ ut.2)
    continuous_toFun := ?cont
    map_zero_left := ?mz
    map_one_left := ?mo
    prop' := ?prop }⟩
  case cont =>
    refine γ.continuous_extend.comp ?_
    refine ((continuous_const.sub
      (continuous_subtype_val.comp continuous_fst)).mul
        ((continuous_truncParam t₀ t₁).comp continuous_snd)).add ?_
    exact (continuous_subtype_val.comp continuous_fst).mul
      ((continuous_linParam t₀ t₁).comp continuous_snd)
  case mz =>
    intro s
    change γ.extend ((1 - ((0 : I) : ℝ)) * truncParam t₀ t₁ s
        + ((0 : I) : ℝ) * linParam t₀ t₁ s)
      = (γ.truncateOfLE h).toContinuousMap s
    rw [Icc.coe_zero, sub_zero, one_mul, _root_.MulZeroClass.zero_mul, add_zero]
    change γ.extend (truncParam t₀ t₁ s) = (γ.truncateOfLE h) s
    unfold truncParam
    have hcoe :
        ((γ.truncateOfLE h) s : X) = ((γ.truncate t₀ t₁) s : X) := by
      simp [_root_.Path.truncateOfLE, _root_.Path.cast_coe]
    rw [hcoe]
    rfl
  case mo =>
    intro s
    change γ.extend ((1 - ((1 : I) : ℝ)) * truncParam t₀ t₁ s
        + ((1 : I) : ℝ) * linParam t₀ t₁ s)
      = ((γ.subpath ⟨t₀, ht₀⟩ ⟨t₁, ht₁⟩).cast _ _).toContinuousMap s
    rw [Icc.coe_one, sub_self, _root_.MulZeroClass.zero_mul, one_mul, zero_add]
    change γ.extend (linParam t₀ t₁ s) = ((γ.subpath ⟨t₀, ht₀⟩ ⟨t₁, ht₁⟩).cast _ _) s
    rw [_root_.Path.cast_coe]
    change γ.extend (linParam t₀ t₁ s)
        = γ (Icc.convexComb (⟨t₀, ht₀⟩ : I) ⟨t₁, ht₁⟩ s)
    unfold linParam
    have hmem : ((1 - (s : ℝ)) * t₀ + (s : ℝ) * t₁) ∈ (_root_.Set.Icc 0 1 : Set ℝ) :=
      (Icc.convexComb (⟨t₀, ht₀⟩ : I) ⟨t₁, ht₁⟩ s).2
    rw [_root_.Path.extend_apply _ hmem]
    congr
  case prop =>
    intro u s hs
    rcases hs with hs0 | hs1
    · subst hs0
      change γ.extend ((1 - (u : ℝ)) * truncParam t₀ t₁ 0 + (u : ℝ) * linParam t₀ t₁ 0)
          = (γ.truncateOfLE h).toContinuousMap 0
      rw [truncParam_zero ht₀.1 h, linParam_zero]
      have hcomb : (1 - (u : ℝ)) * t₀ + (u : ℝ) * t₀ = t₀ := by ring
      rw [hcomb]
      change γ.extend t₀ = (γ.truncateOfLE h) 0
      rw [_root_.Path.source]
    · rw [Set.mem_singleton_iff] at hs1
      subst hs1
      change γ.extend ((1 - (u : ℝ)) * truncParam t₀ t₁ 1 + (u : ℝ) * linParam t₀ t₁ 1)
          = (γ.truncateOfLE h).toContinuousMap 1
      rw [truncParam_one h ht₁.2, linParam_one]
      have hcomb : (1 - (u : ℝ)) * t₁ + (u : ℝ) * t₁ = t₁ := by ring
      rw [hcomb]
      change γ.extend t₁ = (γ.truncateOfLE h) 1
      rw [_root_.Path.target]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.truncateOfLE_homotopic_subpath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.truncateOfLE_homotopic_subpath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.truncateOfLE_homotopic_subpath ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.truncateOfLE_homotopic_subpath

lemma Path_concat_cast_eq {X : Type*} [TopologicalSpace X] :
    ∀ {k : ℕ} {p p' : Fin (k + 1) → X} (heq : ∀ i, p i = p' i)
      (F : (i : Fin k) → _root_.Path (p i.castSucc) (p i.succ)),
      _root_.Path.concat p' (fun i =>
          (F i).cast (heq i.castSucc).symm (heq i.succ).symm) =
        (_root_.Path.concat p F).cast (heq 0).symm (heq (Fin.last k)).symm
  | 0, _, _, heq, F => by
      rw [_root_.Path.concat_zero, _root_.Path.concat_zero]
      apply _root_.Path.ext
      ext s
      change _root_.Path.refl _ s = _root_.Path.refl _ s
      simp only [_root_.Path.refl_apply]
      exact (heq 0).symm
  | n + 1, p, p', heq, F => by
      rw [_root_.Path.concat_succ, _root_.Path.concat_succ]
      have ih := Path_concat_cast_eq (k := n)
        (p := p ∘ Fin.castSucc) (p' := p' ∘ Fin.castSucc)
        (fun i => heq i.castSucc)
        (fun i => F i.castSucc)
      apply _root_.Path.ext
      ext s
      change (_root_.Path.trans _ _) s = (_root_.Path.trans _ _) s
      simp only [_root_.Path.trans_apply]
      split_ifs with hs
      · have h2s_mem : 2 * (s : ℝ) ∈ I :=
          (_root_.unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩
        have key := congr_fun (congr_arg DFunLike.coe ih) ⟨2 * (s : ℝ), h2s_mem⟩
        rw [_root_.Path.cast_coe] at key
        exact key
      · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Path_concat_cast_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Path_concat_cast_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Path_concat_cast_eq ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Path_concat_cast_eq

lemma Path.trans_truncate_homotopic
    {X : Type*} [TopologicalSpace X] {a b : X} (γ : _root_.Path a b)
    {k : ℕ} (t : Fin (k + 1) → unitInterval)
    (ht0 : t 0 = 0) (htlast : t (Fin.last k) = 1)
    (htmono : Monotone t) :
    γ.Homotopic
      ((concatTrans (p := fun i => γ.extend ((t i : I) : ℝ))
          (fun i : Fin k => γ.truncateOfLE
            (show ((t i.castSucc : I) : ℝ) ≤ ((t i.succ : I) : ℝ) from
              htmono (Fin.castSucc_le_succ i)))).cast
        (by
          show a = γ.extend ((t 0 : I) : ℝ)
          rw [ht0]
          simp)
        (by
          show b = γ.extend ((t (Fin.last k) : I) : ℝ)
          rw [htlast]
          simp)) := by
  set F : (i : Fin k) →
      _root_.Path (γ.extend ((t i.castSucc : I) : ℝ)) (γ.extend ((t i.succ : I) : ℝ)) :=
    fun i => γ.truncateOfLE
      (show ((t i.castSucc : I) : ℝ) ≤ ((t i.succ : I) : ℝ) from
        htmono (Fin.castSucc_le_succ i)) with hFdef
  set G : (i : Fin k) →
      _root_.Path (γ (t i.castSucc : I)) (γ (t i.succ : I)) :=
    fun i => γ.subpath (t i.castSucc) (t i.succ) with hGdef
  have hpEq : ∀ i : Fin (k + 1),
      γ.extend ((t i : I) : ℝ) = γ (t i : I) :=
    fun i => _root_.Path.extend_extends' γ (t i : (_root_.Set.Icc 0 1 : Set ℝ))
  set G' : (i : Fin k) →
      _root_.Path (γ.extend ((t i.castSucc : I) : ℝ)) (γ.extend ((t i.succ : I) : ℝ)) :=
    fun i => (G i).cast (hpEq i.castSucc) (hpEq i.succ) with hG'def
  have hFG' : ∀ i : Fin k, (F i).Homotopic (G' i) := by
    intro i
    have hbridge := truncateOfLE_homotopic_subpath γ
      (h := htmono (Fin.castSucc_le_succ i))
      (ht₀ := (t i.castSucc).2) (ht₁ := (t i.succ).2)
    convert hbridge using 2
  have hConcat_FG' :
      (concatTrans (p := fun i => γ.extend ((t i : I) : ℝ)) F).Homotopic
        (concatTrans (p := fun i => γ.extend ((t i : I) : ℝ)) G') := by
    unfold concatTrans
    exact _root_.Path.Homotopic.concat_hcomp (n := k)
      (fun i => γ.extend ((t i : I) : ℝ)) F G' hFG'
  have hConcat_G'_G :
      (concatTrans (p := fun i => γ.extend ((t i : I) : ℝ)) G' : _root_.Path _ _)
        = (_root_.Path.concat (fun i => γ (t i : I)) G).cast (hpEq 0) (hpEq (Fin.last k)) := by
    have hpEq' : ∀ i : Fin (k + 1), γ (t i : I) = γ.extend ((t i : I) : ℝ) :=
      fun i => (hpEq i).symm
    have := Path_concat_cast_eq (k := k)
      (p := fun i => γ (t i : I))
      (p' := fun i => γ.extend ((t i : I) : ℝ))
      hpEq' G
    simpa only [concatTrans, hG'def] using this
  have hConcat_G_subpath :
      (_root_.Path.concat (fun i => γ (t i : I)) G).Homotopic
        (γ.subpath (t 0) (t (Fin.last k))) := by
    have := _root_.Path.Homotopic.concat_subpath γ t
    simpa only [hGdef, Function.comp_def] using this
  have h0 : a = γ.extend ((t 0 : I) : ℝ) := by rw [ht0]; simp
  have hk : b = γ.extend ((t (Fin.last k) : I) : ℝ) := by rw [htlast]; simp
  have h0' : a = γ (t 0 : I) := by rw [ht0]; simp
  have hk' : b = γ (t (Fin.last k) : I) := by rw [htlast]; simp
  have step4 :
      ((γ.subpath (t 0) (t (Fin.last k))).cast h0' hk' : _root_.Path a b) = γ := by
    apply _root_.Path.ext
    ext s
    rw [_root_.Path.cast_coe]
    change γ (Icc.convexComb (t 0 : I) (t (Fin.last k) : I) s) = γ s
    congr 1
    apply Subtype.ext
    simp [ht0, htlast]
  have step1 :
      ((concatTrans (p := fun i => γ.extend ((t i : I) : ℝ)) F).cast h0 hk).Homotopic
        ((concatTrans (p := fun i => γ.extend ((t i : I) : ℝ)) G').cast h0 hk) :=
    _root_.Path.Homotopic.pathCast hConcat_FG' h0 hk
  have step2 :
      ((concatTrans (p := fun i => γ.extend ((t i : I) : ℝ)) G').cast h0 hk : _root_.Path a b)
        = (_root_.Path.concat (fun i => γ (t i : I)) G).cast h0' hk' := by
    apply _root_.Path.ext
    ext s
    rw [hConcat_G'_G]
    simp [_root_.Path.cast_coe]
  have step3 :
      ((_root_.Path.concat (fun i => γ (t i : I)) G).cast h0' hk').Homotopic
        ((γ.subpath (t 0) (t (Fin.last k))).cast h0' hk') :=
    _root_.Path.Homotopic.pathCast hConcat_G_subpath h0' hk'
  have chain1 :
      ((concatTrans (p := fun i => γ.extend ((t i : I) : ℝ)) F).cast h0 hk).Homotopic
        ((_root_.Path.concat (fun i => γ (t i : I)) G).cast h0' hk') := by
    rw [← step2]; exact step1
  have chain2 :
      ((concatTrans (p := fun i => γ.extend ((t i : I) : ℝ)) F).cast h0 hk).Homotopic
        ((γ.subpath (t 0) (t (Fin.last k))).cast h0' hk') :=
    chain1.trans step3
  have step4_h :
      ((γ.subpath (t 0) (t (Fin.last k))).cast h0' hk').Homotopic γ := by
    rw [step4]
  have chain3 :
      ((concatTrans (p := fun i => γ.extend ((t i : I) : ℝ)) F).cast h0 hk).Homotopic γ :=
    chain2.trans step4_h
  exact chain3.symm

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Path
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Path.trans_truncate_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Path.trans_truncate_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Path.trans_truncate_homotopic ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Path.trans_truncate_homotopic

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
