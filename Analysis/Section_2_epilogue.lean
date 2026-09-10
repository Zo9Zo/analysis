import Mathlib.Tactic
import Analysis.Section_2_3

/-!
# Analysis I, Chapter 2 epilogue: Isomorphism with the Mathlib natural numbers

In this (technical) epilogue, we show that the "Chapter 2" natural numbers {name}`Chapter2.Nat` are
isomorphic in various senses to the standard natural numbers {lean}`ℕ`.

After this epilogue, {name}`Chapter2.Nat` will be deprecated, and we will instead use the standard
natural numbers {lean}`ℕ` throughout.  In particular, one should use the full Mathlib API for {lean}`ℕ` for
all subsequent chapters, in lieu of the {name}`Chapter2.Nat` API.

Filling the sorries here requires both the {name}`Chapter2.Nat` API and the Mathlib API for the standard
natural numbers {lean}`ℕ`.  As such, they are excellent exercises to prepare you for the aforementioned
transition.

In second half of this section we also give a fully axiomatic treatment of the natural numbers
via the Peano axioms. The treatment in the preceding three sections was only partially axiomatic,
because we used a specific construction {name}`Chapter2.Nat` of the natural numbers that was an inductive
type, and used that inductive type to construct a recursor.  Here, we give some exercises to show
how one can accomplish the same tasks directly from the Peano axioms, without knowing the specific
implementation of the natural numbers.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

/-- Converting a Chapter 2 natural number to a Mathlib natural number. -/
abbrev Chapter2.Nat.toNat (n : Chapter2.Nat) : ℕ := match n with
  | zero => 0
  | succ n' => n'.toNat + 1

lemma Chapter2.Nat.zero_toNat : (0 : Chapter2.Nat).toNat = 0 := rfl

lemma Chapter2.Nat.succ_toNat (n : Chapter2.Nat) : (n++).toNat = n.toNat + 1 := rfl

/-- The conversion is a bijection. Here we use the existing capability (from Section 2.1) to map
the Mathlib natural numbers to the Chapter 2 natural numbers. -/
abbrev Chapter2.Nat.equivNat : Chapter2.Nat ≃ ℕ where
  toFun := toNat
  invFun n := (n:Chapter2.Nat)
  left_inv n := by
    induction' n with n hn; rfl
    simp [hn]
    rw [succ_eq_add_one]
  right_inv n := by
    induction' n with n hn; rfl
    simp [←succ_eq_add_one, hn]

/-- The conversion preserves addition. -/
abbrev Chapter2.Nat.map_add : ∀ (n m : Nat), (n + m).toNat = n.toNat + m.toNat := by
  intro n m
  induction' n with n hn
  · rw [show zero = 0 from rfl, zero_add, _root_.Nat.zero_add]
  rw [succ_add, succ_toNat, succ_toNat, hn]
  abel

/-- The conversion preserves multiplication. -/
abbrev Chapter2.Nat.map_mul : ∀ (n m : Nat), (n * m).toNat = n.toNat * m.toNat := by
  intro n m
  induction' n with n hn
  . rw [show zero = 0 from rfl, zero_mul, _root_.Nat.zero_mul]
  rw [succ_mul, map_add, hn, succ_toNat, _root_.Nat.add_mul]
  simp

/-- The conversion preserves order. -/
abbrev Chapter2.Nat.map_le_map_iff : ∀ {n m : Nat}, n.toNat ≤ m.toNat ↔ n ≤ m := by
  intro n m
  induction' n with n hn
  . rw [show zero.toNat = 0 from rfl, show zero = 0 from rfl]
    simp
    tauto
  rw [succ_toNat]
  constructor
  . intro hl
    have hnsucc : n.toNat ≤ n.toNat + 1 := by
      simp
    have hnm : n.toNat ≤ m.toNat := by
      order
    rw [hn] at hnm
    have hnnem : n ≠ m := by
      intro hc
      rw [hc] at hl
      simp at hl
    have hnltm : n < m := by tauto
    rw [← lt_iff_succ_le]
    exact hnltm
  intro hnm
  have hnltm : n < m := by
    rw [lt_iff_succ_le]
    exact hnm
  have hnlem : n ≤ m := by order
  rw [← hn] at hnlem
  by_cases hncm : n.toNat + 1 = m.toNat + 1
  . simp at hncm
    have hnem : n = m := equivNat.injective hncm
    rw [hnem]
    order
  simp at hncm
  simp
  order

abbrev Chapter2.Nat.equivNat_ordered_ring : Chapter2.Nat ≃+*o ℕ where
  toEquiv := equivNat
  map_add' := map_add
  map_mul' := map_mul
  map_le_map_iff' := map_le_map_iff

/-- The conversion preserves exponentiation. -/
lemma Chapter2.Nat.pow_eq_pow (n m : Chapter2.Nat) :
    n.toNat ^ m.toNat = (n^m).toNat := by
  induction' m with m hm
  . rw [show zero.toNat = 0 from rfl, show zero = 0 from rfl, pow_zero, _root_.Nat.pow_zero]
  rw [succ_toNat, pow_succ, _root_.Nat.pow_add_one, hm, map_mul]

/-- The Peano axioms for an abstract type {name}`Nat` -/
@[ext]
structure PeanoAxioms where
  Nat : Type
  zero : Nat -- Axiom 2.1
  succ : Nat → Nat -- Axiom 2.2
  succ_ne : ∀ n : Nat, succ n ≠ zero -- Axiom 2.3
  succ_cancel : ∀ {n m : Nat}, succ n = succ m → n = m -- Axiom 2.4
  induction : ∀ (P : Nat → Prop),
    P zero → (∀ n : Nat, P n → P (succ n)) → ∀ n : Nat, P n -- Axiom 2.5

namespace PeanoAxioms

/-- The Chapter 2 natural numbers obey the Peano axioms. -/
def Chapter2_Nat : PeanoAxioms where
  Nat := Chapter2.Nat
  zero := Chapter2.Nat.zero
  succ := Chapter2.Nat.succ
  succ_ne := Chapter2.Nat.succ_ne
  succ_cancel := Chapter2.Nat.succ_cancel
  induction := Chapter2.Nat.induction

/-- The Mathlib natural numbers obey the Peano axioms. -/
def Mathlib_Nat : PeanoAxioms where
  Nat := ℕ
  zero := 0
  succ := Nat.succ
  succ_ne := Nat.succ_ne_zero
  succ_cancel := Nat.succ_inj.mp
  induction _ := Nat.rec

/-- One can map the Mathlib natural numbers into any other structure obeying the Peano axioms. -/
abbrev natCast (P : PeanoAxioms) : ℕ → P.Nat := fun n ↦ match n with
  | Nat.zero => P.zero
  | Nat.succ n => P.succ (natCast P n)

/-- One can start the proof here with {syntax tactic}`unfold Function.Injective`, although it is not strictly necessary. -/
theorem natCast_injective (P : PeanoAxioms) : Function.Injective P.natCast := by
  unfold Function.Injective
  intro a b hab
  by_contra! hc
  by_cases hacb : a < b
  . rw [lt_iff_exists_pos_add] at hacb
    obtain ⟨k, hk⟩ := hacb
    have hkpos := hk.left
    have hakb := hk.right
    rw [← hakb] at hab
    have han : ∀ n, P.natCast n = P.natCast (n + k) → k = 0 := by
      intro n
      induction' n with n hn
      . simp
        intro hp
        by_contra! hnez
        have hec : ∃ c, k = c + 1 := by
          simp
          order
        obtain ⟨m, hm⟩ := hec
        rw [hm] at hp
        change P.zero = P.succ (P.natCast m) at hp
        have hpsucc := P.succ_ne
        tauto
      intro hp
      change P.succ (P.natCast n) = _ at hp
      have hps : P.succ (P.natCast n) = P.natCast (n + k + 1) := by
        rw [hp]
        abel_nf
      change P.succ (P.natCast n) = P.succ (P.natCast (n + k)) at hps
      apply P.succ_cancel at hps
      apply hn at hps
      exact hps
    specialize han a
    apply han at hab
    order
  have hblta : b < a := by order
  rw [lt_iff_exists_pos_add] at hblta
  obtain ⟨k, hk⟩ := hblta
  have hkpos := hk.left
  have hakb := hk.right
  rw [← hakb] at hab
  have han : ∀ (n : ℕ), P.natCast (n + k) = P.natCast n → k = 0 := by
    intro n
    induction' n with n hn
    . simp
      intro hp
      by_contra! hnez
      have hec : ∃ c, k = c + 1 := by
        simp
        order
      obtain ⟨m, hm⟩ := hec
      rw [hm] at hp
      change P.succ (P.natCast m) = P.zero at hp
      have hpsucc := P.succ_ne
      tauto
    intro hp
    change _ = P.succ (P.natCast n) at hp
    have hps : P.succ (P.natCast n) = P.natCast (n + k + 1) := by
      rw [← hp]
      abel_nf
    change P.succ (P.natCast n) = P.succ (P.natCast (n + k)) at hps
    apply P.succ_cancel at hps
    symm at hps
    apply hn at hps
    exact hps
  specialize han b
  apply han at hab
  order

/-- One can start the proof here with {syntax tactic}`unfold Function.Surjective`, although it is not strictly necessary. -/
theorem natCast_surjective (P : PeanoAxioms) : Function.Surjective P.natCast := by
  unfold Function.Surjective
  let Q (b : P.Nat) : Prop := ∃ a, P.natCast a = b
  have hQ (b : P.Nat) : Q b ↔ ∃ a, P.natCast a = b := by rfl
  have hQz : Q P.zero := by
    rw [hQ]
    use 0
  have hQs : ∀ b : P.Nat, Q b → Q (P.succ b) := by
    intro b hb
    rw [hQ] at hb
    obtain ⟨a, ha⟩ := hb
    rw [hQ]
    use (a + 1)
    change P.succ (P.natCast a) = P.succ b
    rw [ha]
  apply P.induction
  . rw [← hQ]
    exact hQz
  tauto

/-- The notion of an equivalence between two structures obeying the Peano axioms.
    The symbol {kw (of := «term_≃_»)}`≃` is an alias for Mathlib's {name}`Equiv` class; for instance {lean}`P.Nat ≃ Q.Nat` is
    an alias for {lean}`_root_.Equiv P.Nat Q.Nat`. -/
class Equiv (P Q : PeanoAxioms) where
  equiv : P.Nat ≃ Q.Nat
  equiv_zero : equiv P.zero = Q.zero
  equiv_succ : ∀ n : P.Nat, equiv (P.succ n) = Q.succ (equiv n)

/-- This exercise will require application of Mathlib's API for the {name}`Equiv` class.
    Some of this API can be invoked automatically via the {tactic}`simp` tactic. -/
abbrev Equiv.symm {P Q: PeanoAxioms} (equiv : Equiv P Q) : Equiv Q P where
  equiv := equiv.equiv.symm
  equiv_zero := by
    have heq := equiv.equiv_zero
    rw [← heq]
    simp
  equiv_succ n := by
    have heq := equiv.equiv_succ
    specialize heq (equiv.equiv.symm n)
    simp at heq
    rw [← heq]
    simp

/-- This exercise will require application of Mathlib's API for the {name}`Equiv` class.
    Some of this API can be invoked automatically via the {tactic}`simp` tactic. -/
abbrev Equiv.trans {P Q R: PeanoAxioms} (equiv1 : Equiv P Q) (equiv2 : Equiv Q R) : Equiv P R where
  equiv := equiv1.equiv.trans equiv2.equiv
  equiv_zero := by
    have heq1 := equiv1.equiv_zero
    have heq2 := equiv2.equiv_zero
    rw [← heq1] at heq2
    rw [← heq2]
    simp
  equiv_succ n := by
    have heq1 := equiv1.equiv_succ
    have heq2 := equiv2.equiv_succ
    specialize heq1 n
    specialize heq2 (equiv1.equiv n)
    rw [← heq1] at heq2
    simp
    rw [← heq2]

/-- Useful Mathlib tools for inverting bijections include {name}`Function.surjInv` and {name}`Function.invFun`. -/
noncomputable abbrev Equiv.fromNat (P : PeanoAxioms) : Equiv Mathlib_Nat P where
  equiv := {
    toFun := P.natCast
    invFun := P.natCast.invFun
    left_inv := by
      apply Function.leftInverse_invFun P.natCast_injective
    right_inv := by
      apply Function.rightInverse_invFun P.natCast_surjective
  }
  equiv_zero := by
    simp
    tauto
  equiv_succ n := by
    simp
    tauto

/-- The task here is to establish that any two structures obeying the Peano axioms are equivalent. -/
noncomputable abbrev Equiv.mk' (P Q : PeanoAxioms) : Equiv P Q := by
  have hNQ : Equiv Mathlib_Nat Q := Equiv.fromNat Q
  have hNP : Equiv Mathlib_Nat P := Equiv.fromNat P
  apply symm at hNP
  exact hNP.trans hNQ

/-- There is only one equivalence between any two structures obeying the Peano axioms. -/
theorem Equiv.uniq {P Q : PeanoAxioms} (equiv1 equiv2 : PeanoAxioms.Equiv P Q) :
    equiv1 = equiv2 := by
  obtain ⟨equiv1, equiv_zero1, equiv_succ1⟩ := equiv1
  obtain ⟨equiv2, equiv_zero2, equiv_succ2⟩ := equiv2
  congr
  ext n
  let F (n : P.Nat) : Prop := equiv1 n = equiv2 n
  have hF (n : P.Nat) : F n ↔ equiv1 n = equiv2 n := by rfl
  have hFz : F P.zero := by
    rw [hF]
    rw [equiv_zero1, equiv_zero2]
  have hFs : ∀ n : P.Nat, F n → F (P.succ n) := by
    intro m hm
    rw [hF] at hm
    rw [hF]
    specialize equiv_succ1 m
    specialize equiv_succ2 m
    rw [equiv_succ1, equiv_succ2]
    tauto
  revert n
  apply P.induction
  . tauto
  tauto

/-- A sample result: recursion is well-defined on any structure obeying the Peano axioms -/
theorem Nat.recurse_uniq {P : PeanoAxioms} (f: P.Nat → P.Nat → P.Nat) (c: P.Nat) :
    ∃! (a: P.Nat → P.Nat), a P.zero = c ∧ ∀ n, a (P.succ n) = f n (a n) := by
  have hN (f: Chapter2.Nat → Chapter2.Nat → Chapter2.Nat) (c: Chapter2.Nat) :
    ∃! (a: Chapter2.Nat → Chapter2.Nat), a 0 = c ∧ ∀ n, a (n++) = f n (a n) := Chapter2.Nat.recurse_uniq f c
  have hequiv : Equiv Chapter2_Nat P := Equiv.mk' Chapter2_Nat P
  obtain ⟨equiv, equiv_zero, equiv_succ⟩ := hequiv
  let fP (n : Chapter2.Nat) (m : Chapter2.Nat) : Chapter2.Nat :=
    equiv.symm (f (equiv n) (equiv m))
  let cP := equiv.symm c
  specialize hN fP cP
  obtain ⟨a, ha⟩ := hN
  simp at ha
  let aP (n : P.Nat) : P.Nat :=
    equiv (a (equiv.invFun n))
  use aP
  simp
  have hl : (aP P.zero = c ∧ ∀ (n : P.Nat), aP (P.succ n) = f n (aP n)) := by
    have hal := ha.left
    have hll : aP P.zero = c := by
      have hall := hal.left
      dsimp [aP]
      dsimp [cP] at hall
      have hpz : equiv.symm P.zero = (0 : Chapter2.Nat) := by
        rw [← equiv_zero]
        simp
        tauto
      rw [hpz, hall]
      simp
    have hlr : ∀ (n : P.Nat), aP (P.succ n) = f n (aP n) := by
      have halr := hal.right
      intro n
      specialize halr (equiv.symm n)
      dsimp [fP] at halr
      simp at halr
      dsimp [aP]
      specialize equiv_succ (equiv.symm n)
      simp at equiv_succ
      rw [← equiv_succ]
      simp
      have hsucc : Chapter2_Nat.succ (equiv.symm n) = equiv.symm n++ := by tauto
      rw [hsucc, halr]
      simp
    exact ⟨hll, hlr⟩
  have hr : ∀ (y : P.Nat → P.Nat), y P.zero = c → (∀ (n : P.Nat), y (P.succ n) = f n (y n)) → y = aP := by
    have har := ha.right
    intro y hy
    let yP (n : Chapter2.Nat) : Chapter2.Nat :=
      equiv.invFun (y (equiv n))
    specialize har yP
    dsimp [yP] at har
    rw [← equiv_zero, show Chapter2_Nat.zero = (0 : Chapter2.Nat) from rfl] at hy
    rw [hy] at har
    dsimp [cP] at har
    simp at har
    intro himp
    have hf : (fun n ↦ equiv.symm (y (equiv n))) = a := by
      apply har
      intro n
      let nP : P.Nat := equiv n
      specialize himp nP
      dsimp [nP] at himp
      specialize equiv_succ n
      rw [← equiv_succ] at himp
      dsimp [fP]
      simp
      rw [← himp]
      tauto
    dsimp [aP]
    rw [← hf]
    simp
  exact ⟨hl, hr⟩

end PeanoAxioms
