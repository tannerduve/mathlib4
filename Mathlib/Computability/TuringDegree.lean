/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/

import Mathlib.Tactic.Cases
import Mathlib.Tactic.NormNum
import Aesop
import Mathlib.Computability.RecursiveIn

/-!
# Turing Reducibility and Turing Degrees

This file defines Turing reducibility and Turing equivalence in terms of oracle computability,
as well as the notion of Turing degrees as equivalence classes under mutual reducibility.

## Main Definitions

* `TuringReducible f g`:
  The function `f` is Turing reducible to `g` if `f` is recursive in the singleton set `{g}`.
* `TuringEquivalent f g`:
  Functions `f` and `g` are Turing equivalent if they are mutually Turing reducible.
* `TuringDegree`:
  The type of Turing degrees, given by the quotient of `ℕ →. ℕ` under `TuringEquivalent`.

## Notation

* `f ≤ᵀ g`: `f` is Turing reducible to `g`.
* `f ≡ᵀ g`: `f` is Turing equivalent to `g`.

## Implementation Notes

We define `TuringDegree` as the `Antisymmetrization` of the preorder of partial functions under
Turing reducibility. This gives a concrete representation of degrees as equivalence classes.

## References

* [Odifreddi1989] Odifreddi, Piergiorgio.
  *Classical Recursion Theory: The Theory of Functions and Sets of Natural Numbers*, Vol. I.

## Tags

Computability, Turing Degrees, Reducibility, Equivalence Relation
-/

open Std

/--
`f` is Turing reducible to `g` if `f` is partial recursive given access to the oracle `g`
-/
abbrev TuringReducible (f g : ℕ →. ℕ) : Prop :=
  RecursiveIn {g} f

/--
`f` is Turing equivalent to `g` if `f` is reducible to `g` and `g` is reducible to `f`.
-/
abbrev TuringEquivalent (f g : ℕ →. ℕ) : Prop :=
  AntisymmRel TuringReducible f g

@[inherit_doc] scoped[Computability] infix:50 " ≤ᵀ " => TuringReducible
@[inherit_doc] scoped[Computability] infix:50 " ≡ᵀ " => TuringEquivalent

open scoped Computability

variable {f g h : ℕ →. ℕ}

protected theorem TuringReducible.refl (f : ℕ →. ℕ) : f ≤ᵀ f := .oracle _ <| by simp
protected theorem TuringReducible.rfl : f ≤ᵀ f := .refl _

instance : Refl TuringReducible where refl _ := .rfl

theorem TuringReducible.trans (hg : f ≤ᵀ g) (hh : g ≤ᵀ h) : f ≤ᵀ h := by
  induction hg with
  | zero | succ | left | right => constructor
  | oracle g' hg' =>
    rw [Set.mem_singleton_iff] at hg'
    rw [hg']
    exact hh
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
  | rfind _ ih => exact .rfind ih

instance : IsTrans (ℕ →. ℕ) TuringReducible :=
  ⟨@TuringReducible.trans⟩

instance : IsPreorder (ℕ →. ℕ) TuringReducible where
  refl := .refl

theorem TuringEquivalent.equivalence : Equivalence TuringEquivalent :=
  (AntisymmRel.setoid _ _).iseqv

@[refl]
protected theorem TuringEquivalent.refl (f : ℕ →. ℕ) : f ≡ᵀ f :=
  Equivalence.refl equivalence f

@[symm]
theorem TuringEquivalent.symm {f g : ℕ →. ℕ} (h : f ≡ᵀ g) : g ≡ᵀ f :=
  Equivalence.symm equivalence h

@[trans]
theorem TuringEquivalent.trans (f g h : ℕ →. ℕ) (h₁ : f ≡ᵀ g) (h₂ : g ≡ᵀ h) : f ≡ᵀ h :=
  Equivalence.trans equivalence h₁ h₂

/--
Instance declaring that `RecursiveIn` is a preorder.
-/
instance : IsPreorder (ℕ →. ℕ) TuringReducible where
  refl := TuringReducible.refl
  trans := @TuringReducible.trans

/--
Turing degrees are the equivalence classes of partial functions under Turing equivalence.
-/
abbrev TuringDegree :=
  Antisymmetrization _ TuringReducible

private instance : Preorder (ℕ →. ℕ) where
  le := TuringReducible
  le_refl := .refl
  le_trans _ _ _ := TuringReducible.trans

instance TuringDegree.instPartialOrder : PartialOrder TuringDegree :=
  instPartialOrderAntisymmetrization

open scoped Computability
open Encodable

/-!
## Turing join on partial functions

We define the join \(f ⊕ g\) by coding answers from `f` as even numbers and answers from `g` as odd
numbers:

- on even inputs `2*n`, query `f n` and return `2 * y`
- on odd inputs `2*n+1`, query `g n` and return `2 * y + 1`
-/

def turingJoin (f g : ℕ →. ℕ) : ℕ →. ℕ :=
  fun n =>
    cond n.bodd ( (g n.div2).map (fun y => 2 * y + 1) ) ( (f n.div2).map (fun y => 2 * y) )
infix :50 " ⊕ " => turingJoin

@[simp] lemma turingJoin_even (f g : ℕ →. ℕ) (n : ℕ) :
    (f ⊕ g) (2 * n) = (f n).map (fun y => 2 * y) := by
  simp [turingJoin]

@[simp] lemma turingJoin_odd (f g : ℕ →. ℕ) (n : ℕ) :
    (f ⊕ g) (2 * n + 1) = (g n).map (fun y => 2 * y + 1) := by
  simp [turingJoin, Nat.bodd_mul]

lemma left_le_join (f g : ℕ →. ℕ) : f ≤ᵀ (f ⊕ g) := by
  set j : ℕ →. ℕ := f ⊕ g
  have hj : RecursiveIn {j} j := RecursiveIn.oracle j (by simp)
  have hdouble : RecursiveIn {j} (fun n : ℕ => (2 * n : ℕ)) := by
    refine RecursiveIn.of_primrec (Primrec.nat_iff.1 ?_)
    simpa using (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
  have hdiv2 : RecursiveIn {j} (fun n : ℕ => (Nat.div2 n : ℕ)) := by
    refine RecursiveIn.of_primrec (Primrec.nat_iff.1 ?_)
    simpa using (Primrec.nat_div2 : Primrec Nat.div2)
  have hquery : RecursiveIn {j} (fun n => j (2 * n)) := by
    refine RecursiveIn.of_eq (RecursiveIn.comp hj hdouble) ?_
    intro n
    simp [Part.bind_some]
  have hdecode : RecursiveIn {j} (fun n => j (2 * n) >>= fun m => (Nat.div2 m : ℕ)) :=
    RecursiveIn.comp hdiv2 hquery
  have hf' : RecursiveIn {j} f := by
    refine RecursiveIn.of_eq hdecode ?_
    intro n
    have hcomp : (Nat.div2 ∘ fun y : ℕ => 2 * y) = (fun y => y) := by
      funext y
      simp [Function.comp, Nat.div2_bit0]
    simpa [j, turingJoin, Part.bind_some_eq_map, Part.map_map, Function.comp, hcomp] using
      (Part.map_id' (f := fun y : ℕ => y) (fun y => rfl) (f n))
  simpa [TuringReducible, j] using hf'

lemma right_le_join (f g : ℕ →. ℕ) : g ≤ᵀ (f ⊕ g) := by
  set j : ℕ →. ℕ := f ⊕ g
  have hj : RecursiveIn {j} j := RecursiveIn.oracle j (by simp)
  have hdouble1 : RecursiveIn {j} (fun n : ℕ => (2 * n + 1 : ℕ)) := by
    refine RecursiveIn.of_primrec (Primrec.nat_iff.1 ?_)
    simpa using
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 1))
  have hdiv2 : RecursiveIn {j} (fun n : ℕ => (Nat.div2 n : ℕ)) := by
    refine RecursiveIn.of_primrec (Primrec.nat_iff.1 ?_)
    simpa using (Primrec.nat_div2 : Primrec Nat.div2)
  have hquery : RecursiveIn {j} (fun n => j (2 * n + 1)) := by
    refine RecursiveIn.of_eq (RecursiveIn.comp hj hdouble1) ?_
    intro n
    simp [Part.bind_some]
  have hdecode : RecursiveIn {j} (fun n => j (2 * n + 1) >>= fun m => (Nat.div2 m : ℕ)) :=
    RecursiveIn.comp hdiv2 hquery
  have hg' : RecursiveIn {j} g := by
    refine RecursiveIn.of_eq hdecode ?_
    intro n
    have hcomp : (Nat.div2 ∘ fun y : ℕ => 2 * y + 1) = (fun y => y) := by
      funext y
      simp [Function.comp]
    simpa [j, turingJoin, Part.bind_some_eq_map, Part.map_map, Function.comp, hcomp] using
      (Part.map_id' (f := fun y : ℕ => y) (fun y => rfl) (g n))
  simpa [TuringReducible, j] using hg'

theorem RecursiveIn_cond_const {O : Set (ℕ →. ℕ)} {c : ℕ → Bool} {f : ℕ →. ℕ} (hc : Computable c)
 (hf : RecursiveIn O f) (k : ℕ) :
    RecursiveIn O (fun n => bif (c n) then f n else (Part.some k)) := by
  have hid : RecursiveIn O (fun n : ℕ => n) := by
    exact Nat.Partrec.recursiveIn (O := O) ((Partrec.nat_iff).1 (Computable.id.partrec))
  have hcode : RecursiveIn O (fun n : ℕ => encode (c n)) := by
    have hcomp : Computable (fun n : ℕ => encode (c n)) := (Computable.encode.comp hc)
    exact Nat.Partrec.recursiveIn (O := O) ((Partrec.nat_iff).1 hcomp.partrec)
  let pairFn : ℕ →. ℕ := fun n =>
  Nat.pair <$> (show Part ℕ from n) <*> (show Part ℕ from encode (c n))
  have hpair : RecursiveIn O pairFn := by
    simpa [pairFn] using (RecursiveIn.pair hid hcode)
  let base : ℕ →. ℕ := fun _ : ℕ => (k : ℕ)
  have hbase : RecursiveIn O base := by
    exact Nat.Partrec.recursiveIn (O := O) ((Partrec.nat_iff).1 (by
      simpa [base] using ((Computable.const k).partrec)))
  let step : ℕ →. ℕ := fun p : ℕ => (Nat.unpair p).1 >>= f
  have hstep : RecursiveIn O step := by
    simpa [step] using (RecursiveIn.comp hf RecursiveIn.left)
  let precFn : ℕ →. ℕ :=
    fun p : ℕ =>
      let (a, n) := Nat.unpair p
      n.rec (base a) (fun y IH => do
        let i ← IH
        step (Nat.pair a (Nat.pair y i)))
  have hprec : RecursiveIn O precFn := by
    simpa [precFn] using (RecursiveIn.prec hbase hstep)
  let mainFn : ℕ →. ℕ := fun n => pairFn n >>= precFn
  have hmain : RecursiveIn O mainFn := by
    simpa [mainFn] using (RecursiveIn.comp hprec hpair)
  have hEq : mainFn = (fun n => bif (c n) then f n else Part.some k) := by
    funext n
    cases h : c n <;>
      simp [mainFn, pairFn, precFn, base, step, h, Seq.seq, Nat.unpair_pair]
  simpa [hEq] using hmain


def eq01 : ℕ →. ℕ := fun p => Part.some (if (Nat.unpair p).1 = (Nat.unpair p).2 then 0 else 1)

theorem eq01_natPartrec : Nat.Partrec eq01 := by
  have hcomp :
      Computable (fun p : ℕ => if (Nat.unpair p).1 = (Nat.unpair p).2 then (0 : ℕ) else 1) := by
    have hEq : Computable (fun q : ℕ × ℕ => decide (q.1 = q.2)) := by
      have hprim : Primrec (fun q : ℕ × ℕ => decide (q.1 = q.2)) := by
        simpa using
          (PrimrecPred.decide (p := fun q : ℕ × ℕ => q.1 = q.2)
            (Primrec.eq : PrimrecPred fun q : ℕ × ℕ => q.1 = q.2))
      exact Primrec.to_comp hprim
    have hdec : Computable (fun p : ℕ => decide ((Nat.unpair p).1 = (Nat.unpair p).2)) :=
      Computable.comp hEq Computable.unpair
    have hcond :
        Computable
        (fun p : ℕ => cond (decide ((Nat.unpair p).1 = (Nat.unpair p).2)) (0 : ℕ) 1) := by
      have h0 : Computable (fun _ : ℕ => (0 : ℕ)) := Computable.const 0
      have h1 : Computable (fun _ : ℕ => (1 : ℕ)) := Computable.const 1
      simpa using
        (Computable.cond (c := fun p : ℕ => decide ((Nat.unpair p).1 = (Nat.unpair p).2))
          (f := fun _ : ℕ => (0 : ℕ)) (g := fun _ : ℕ => (1 : ℕ)) hdec h0 h1)
    refine Computable.of_eq hcond ?_
    intro p
    by_cases h : (Nat.unpair p).1 = (Nat.unpair p).2 <;> simp [h]
  have hpart : _root_.Partrec eq01 := by
    refine _root_.Partrec.of_eq (Computable.partrec hcomp) ?_
    intro p
    by_cases h : (Nat.unpair p).1 = (Nat.unpair p).2 <;> simp [eq01, h]
  exact (Partrec.nat_iff).1 hpart

theorem eq01_recursiveIn (O : Set (ℕ →. ℕ)) : RecursiveIn O eq01 := by
  exact Nat.Partrec.recursiveIn (O := O) eq01_natPartrec

theorem eq01_rfind_none :
    Nat.rfind
        (fun k =>
          (fun m : ℕ => m = 0) <$>
            ((Nat.pair <$> (Part.none : Part ℕ) <*> Part.some k) >>= eq01)) =
      (Part.none : Part ℕ) := by
  refine Nat.rfind_zero_none
    (p := fun k => (fun m : ℕ => m = 0) <$>
      ((Nat.pair <$> (Part.none : Part ℕ) <*> Part.some k) >>= eq01)) ?_
  simp [Seq.seq]

theorem eq01_rfind_some (n : ℕ) :
    Nat.rfind
        (fun k =>
          (fun m : ℕ => m = 0) <$>
            ((Nat.pair <$> (Part.some n : Part ℕ) <*> Part.some k) >>= eq01)) =
      Part.some n := by
  let p : ℕ →. Bool := fun k =>
    (fun m : ℕ => m = 0) <$>
      ((Nat.pair <$> (Part.some n : Part ℕ) <*> Part.some k) >>= eq01)
  refine Part.mem_right_unique ?_ (Part.mem_some n)
  refine (Nat.mem_rfind).2 ?_
  constructor
  · simp [eq01, Nat.unpair_pair, Seq.seq]
  · intro m hm
    have hne : n ≠ m := Nat.ne_of_gt hm
    simp [eq01, Nat.unpair_pair, Seq.seq, hne]

theorem eq01_rfind (v : Part ℕ) :
    Nat.rfind (fun k => (fun m : ℕ => m = 0) <$>
    ((Nat.pair <$> v <*> Part.some k) >>= eq01)) = v := by
  refine Part.induction_on v ?_ ?_
  · simpa using eq01_rfind_none
  · intro n; simpa using eq01_rfind_some (n := n)
