-- Game axiomatics

import mynat.definition
import mynat.add
import mynat.mul
import mynat.pow
namespace mynat
def two_eq_succ_one : (2 : mynat) = succ 1 := rfl

-----------------------
-- World 1: Tutorial --
-----------------------

lemma example1 (x y z : mynat) : x * y + z = x * y + z := begin[nat_num_game]
  refl,
end

lemma example2 (x y : mynat) (h : y = x + 7) : 2 * y = 2 * (x + 7) := begin[nat_num_game]
  rwa h,
end

lemma example3 (a b : mynat) (h : succ a = b) : succ(succ(a)) = succ(b) := begin[nat_num_game]
  rwa h,
end

lemma add_succ_zero (a : mynat) : a + succ(0) = succ(a) := begin[nat_num_game]
  rwa [add_succ, add_zero],
end

-----------------------
-- World 2: Addition --
-----------------------

lemma zero_add (n : mynat) : 0 + n = n := begin[nat_num_game]
  induction n,
  rwa add_zero,
  rwa [add_succ, n_ih],
end

lemma add_assoc (a b c : mynat) : (a + b) + c = a + (b + c) := begin[nat_num_game]
  induction c,
  rwa [add_zero, add_zero],
  rwa [add_succ, add_succ, add_succ, c_ih],
end

lemma succ_add (a b : mynat) : succ a + b = succ (a + b) := begin[nat_num_game]
  induction b,
  rwa [add_zero, add_zero],
  rwa [add_succ, add_succ, b_ih],
end

lemma add_comm (a b : mynat) : a + b = b + a := begin[nat_num_game]
  induction b,
  rwa [add_zero, zero_add],
  rwa [add_succ, succ_add, b_ih],
end

theorem succ_eq_add_one (n : mynat) : succ n = n + 1 := begin[nat_num_game]
  induction n,
  rwa [one_eq_succ_zero, add_succ, add_zero],
  rwa [succ_add, n_ih],
end

lemma add_right_comm (a b c : mynat) : a + b + c = a + c + b := begin[nat_num_game]
  rwa [add_assoc, add_assoc, add_comm(b)],
end

-----------------------------
-- World 3: Multiplication --
-----------------------------

lemma zero_mul (m : mynat) : 0 * m = 0 := begin[nat_num_game]
  induction m,
  rwa mul_zero,
end

lemma mul_one (m : mynat) : m * 1 = m := begin[nat_num_game]
  induction m,
  rwa zero_mul,
  rwa [one_eq_succ_zero, mul_succ, mul_zero, zero_add],
end

lemma one_mul (m : mynat) : 1 * m = m := begin[nat_num_game]
  induction m,
  rwa mul_zero,
  rwa [mul_succ, succ_eq_add_one, m_ih],
end

lemma mul_add (t a b : mynat) : t * (a + b) = t * a + t * b := begin[nat_num_game]
  induction a,
  rwa [mul_zero, zero_add, zero_add],
  rwa [mul_succ, succ_add, mul_succ, a_ih, add_right_comm],
end

lemma mul_assoc (a b c : mynat) : (a * b) * c = a * (b * c) := begin[nat_num_game]
  induction c,
  refl,
  rwa [mul_succ, mul_succ, mul_add, c_ih],
end

lemma succ_mul (a b : mynat) : succ a * b = a * b + b := begin[nat_num_game]
  induction b,
  rwa [add_zero, mul_zero, mul_zero],
  rwa [mul_succ, mul_succ, b_ih, add_succ, add_succ, add_right_comm],
end

lemma add_mul (a b t : mynat) : (a + b) * t = a * t + b * t := begin[nat_num_game]
  induction t,
  rwa [mul_zero, mul_zero, mul_zero, add_zero],
  rwa [
    mul_succ, mul_succ, mul_succ, t_ih,
    add_assoc(a * t_n), add_assoc(a * t_n),
    add_comm(a), add_comm(a), add_assoc
  ],
end

lemma mul_comm (a b : mynat) : a * b = b * a := begin[nat_num_game]
  induction b,
  rwa [mul_zero, zero_mul],
  rwa [mul_succ, succ_mul, b_ih],
end

lemma mul_left_comm (a b c : mynat) : a * (b * c) = b * (a * c) := begin[nat_num_game]
  induction c,
  rwa [mul_zero, mul_zero, mul_zero],
  rwa [
    mul_succ, mul_succ, mul_add, mul_add, c_ih,
    mul_comm(b), mul_comm(b)
  ],
end

--------------------
-- World 4: Power --
--------------------

lemma zero_pow_zero : (0 : mynat) ^ (0 : mynat) = 1 := begin[nat_num_game]
  rwa pow_zero,
end

lemma zero_pow_succ (m : mynat) : (0 : mynat) ^ (succ m) = 0 := begin[nat_num_game]
  rwa [pow_succ, mul_zero],
end

lemma pow_one (a : mynat) : a ^ (1 : mynat) = a := begin[nat_num_game]
  rwa [one_eq_succ_zero, pow_succ, pow_zero, one_mul],
end

lemma one_pow (m : mynat) : (1 : mynat) ^ m = 1 := begin[nat_num_game]
  induction m,
  rwa pow_zero,
  rwa [pow_succ, mul_one],
end

lemma pow_add (a m n : mynat) : a ^ (m + n) = a ^ m * a ^ n := begin[nat_num_game]
  induction n,
  rwa [pow_zero, add_zero, mul_one],
  rwa [add_succ, pow_succ, pow_succ, n_ih, mul_assoc],
end

lemma mul_pow (a b n : mynat) : (a * b) ^ n = a ^ n * b ^ n := begin[nat_num_game]
  induction n,
  rwa [pow_zero, pow_zero, pow_zero, mul_one],
  rwa [
    pow_succ, pow_succ, pow_succ, n_ih,
    mul_assoc(a ^ n_n), mul_assoc(a ^ n_n), mul_comm(a), mul_comm(a), mul_assoc
  ],
end

lemma pow_pow (a m n : mynat) : (a ^ m) ^ n = a ^ (m * n) := begin[nat_num_game]
  induction n,
  rwa [mul_zero, pow_zero, pow_zero],
  rwa [mul_succ, pow_add, pow_succ, n_ih],
end

lemma add_squared (a b : mynat) :
    (a + b) ^ (2 : mynat) = a ^ (2 : mynat) + b ^ (2 : mynat) + 2 * a * b := begin[nat_num_game]
  rwa [
    two_eq_succ_one, one_eq_succ_zero,
    pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_succ,
    pow_zero, pow_zero, pow_zero,
    one_mul, one_mul, one_mul,
    succ_mul, succ_mul,
    zero_mul, zero_add,
    add_mul, add_mul,
    mul_add, mul_add,
    add_assoc, add_assoc,
    add_comm(b*b), add_assoc, mul_comm(b)
  ],
end

-----------------------
-- World 5: Function --
-----------------------

example (P Q : Type) (p : P) (h : P → Q) : Q := begin[nat_num_game]
  exact h p,
end

example : mynat → mynat := begin[nat_num_game]
  intro p,
  exact 3 * p + 2,
end

example (P Q R S T U: Type) (p : P) (h : P → Q) (i : Q → R) (j : Q → T) (k : S → T) (l : T → U) : U := begin[nat_num_game]
  apply l ∘ j ∘ h,
  exact p,
end

example (P Q : Type) : P → (Q → P) := begin[nat_num_game]
  intros p _,
  exact p,
end

example (P Q R : Type) : (P → (Q → R)) → ((P → Q) → (P → R)) := begin[nat_num_game]
  intros f g p,
  apply f p,
  apply g p,
end

example (P Q F : Type) : (P → Q) → ((Q → F) → (P → F)) := begin[nat_num_game]
  intros g h,
  apply h ∘ g,
end

example (P Q : Type) : (P → Q) → ((Q → empty) → (P → empty)) := begin[nat_num_game]
  intros f g,
  exact g ∘ f,
end

example (A B C D E F G H I J K L : Type)
    (f1 : A → B) (f2 : B → E) (f3 : E → D) (f4 : D → A) (f5 : E → F) (f6 : F → C) (f7 : B → C) (f8 : F → G)
    (f9 : G → J) (f10 : I → J) (f11 : J → I) (f12 : I → H) (f13 : E → H) (f14 : H → K) (f15 : I → L)
    : A → L := begin[nat_num_game]
  apply f15 ∘ f11 ∘ f9 ∘ f8 ∘ f5 ∘ f2 ∘ f1,
end

--------------------------
-- World 6: Proposition --
--------------------------

example (P Q : Prop) (p : P) (h : P → Q) : Q := begin[nat_num_game]
  exact h p,
end

lemma imp_self (P : Prop) : P → P := begin[nat_num_game]
  intro p,
  exact p,
end

lemma maze (P Q R S T U: Prop) (p : P) (h : P → Q) (i : Q → R) (j : Q → T) (k : S → T) (l : T → U) : U := begin[nat_num_game]
  apply l ∘ j ∘ h,
  exact p,
end

example (P Q : Prop) : P → (Q → P) := begin[nat_num_game]
  intros p _,
  exact p,
end

example (P Q R : Prop) : (P → (Q → R)) → ((P → Q) → (P → R)) := begin[nat_num_game]
  intros f g p,
  apply f p,
  apply g p,
end

lemma imp_trans (P Q R : Prop) : (P → Q) → ((Q → R) → (P → R)) := begin[nat_num_game]
  intros fpq fqr,
  apply fqr ∘ fpq,
end

lemma contrapositive (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) := begin[nat_num_game]
  intros pq nq,
  apply nq ∘ pq,
end

example (A B C D E F G H I J K L : Prop)
    (f1 : A → B) (f2 : B → E) (f3 : E → D) (f4 : D → A) (f5 : E → F) (f6 : F → C) (f7 : B → C) (f8 : F → G)
    (f9 : G → J) (f10 : I → J) (f11 : J → I) (f12 : I → H) (f13 : E → H) (f14 : H → K) (f15 : I → L)
    : A → L := begin[nat_num_game]
  apply f15 ∘ f11 ∘ f9 ∘ f8 ∘ f5 ∘ f2 ∘ f1,
end

-----------------------------------
-- World 7: Advanced Proposition --
-----------------------------------

example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := begin[nat_num_game]
  split,
  exact p,
  exact q,
end

lemma and_symm (P Q : Prop) : P ∧ Q → Q ∧ P := begin[nat_num_game]
  intro r, cases r,
  split, exact r_right, exact r_left,
end

lemma and_trans (P Q R : Prop) : P ∧ Q → Q ∧ R → P ∧ R := begin[nat_num_game]
  intros pq qr, cases pq, cases qr,
  split, exact pq_left, exact qr_right,
end

lemma iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := begin[nat_num_game]
  intros iff_pq iff_qr, cases iff_pq, cases iff_qr,
  split, apply iff_qr_mp ∘ iff_pq_mp, apply iff_pq_mpr ∘ iff_qr_mpr,
end

example (P Q : Prop) : Q → (P ∨ Q) := begin[nat_num_game]
  intro q,
  right,
  exact q,
end

lemma or_symm (P Q : Prop) : P ∨ Q → Q ∨ P := begin[nat_num_game]
  intro pq, cases pq,
  right, exact pq,
  left, exact pq,
end

lemma and_or_distrib_left (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := begin[nat_num_game]
  split, {
    intro h, cases h, cases h_right, {
      left, split, exact h_left, exact h_right
    }, {
      right, split, exact h_left, exact h_right
    }
  }, {
    intro h, cases h, {
      cases h, split,
      exact h_left, { left, exact h_right }
    }, {
      cases h, split,
      exact h_left, { right, exact h_right }
    }
  }
end

lemma contra (P Q : Prop) : (P ∧ ¬ P) → Q := begin[nat_num_game]
  intro either, cases either, exfalso,
  apply either_right either_left,
end

lemma contrapositive2 (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) := begin[nat_num_game]
  by_cases p: P; by_cases q: Q, repeat {cc},
end

--------------------------------
-- World 8: Advanced Addition --
--------------------------------

theorem succ_inj' {a b : mynat} (hs : succ(a) = succ(b)) :  a = b := begin[nat_num_game]
  exact succ_inj hs,
end

theorem succ_succ_inj {a b : mynat} (h : succ(succ(a)) = succ(succ(b))) : a = b := begin[nat_num_game]
  apply succ_inj ∘ succ_inj,
  exact h,
end

theorem succ_eq_succ_of_eq {a b : mynat} : a = b → succ(a) = succ(b) := begin[nat_num_game]
  intro h,
  rwa h,
end

theorem succ_eq_succ_iff (a b : mynat) : succ a = succ b ↔ a = b := begin[nat_num_game]
  split,
  exact succ_inj,
  exact succ_eq_succ_of_eq,
end

theorem add_right_cancel (a t b : mynat) : a + t = b + t → a = b := begin[nat_num_game]
  intro h,
  induction t,
  rwa add_zero at h, {
    apply t_ih,
    rwa [add_succ, add_succ] at h,
    cc
  }
end

theorem add_left_cancel (t a b : mynat) : t + a = t + b → a = b := begin[nat_num_game]
  rw [add_comm t, add_comm t],
  apply add_right_cancel,
end

theorem add_right_cancel_iff (t a b : mynat) :  a + t = b + t ↔ a = b := begin[nat_num_game]
  split,
  apply add_right_cancel, {
    intro h,
    rwa h,
  }
end

lemma eq_zero_of_add_right_eq_self {a b : mynat} : a + b = a → b = 0 := begin[nat_num_game]
  intros h,
  induction a, {
    rw zero_add at h,
    apply h
  }, {
    apply a_ih,
    rw succ_add at h,
    apply succ_inj h
  }
end

theorem succ_ne_zero (a : mynat) : succ a ≠ 0 := begin[nat_num_game]
  symmetry,
  apply zero_ne_succ,
end

lemma add_left_eq_zero {{a b : mynat}} (H : a + b = 0) : b = 0 := begin[nat_num_game]
  cases b,
  refl, {
    exfalso,
    rw add_succ at H,
    apply succ_ne_zero,
    apply H
  }
end

lemma add_right_eq_zero {a b : mynat} : a + b = 0 → a = 0 := begin[nat_num_game]
  rw add_comm,
  apply add_left_eq_zero,
end

theorem add_one_eq_succ (d : mynat) : d + 1 = succ d := begin[nat_num_game]
  symmetry,
  apply succ_eq_add_one,
end

lemma ne_succ_self (n : mynat) : n ≠ succ n := begin[nat_num_game]
  induction n,
  apply zero_ne_succ, {
    intro h,
    apply n_ih,
    apply succ_inj,
    apply h
  }
end

--------------------------------------
-- World 9: Advanced Multiplication --
--------------------------------------

theorem mul_pos (a b : mynat) : a ≠ 0 → b ≠ 0 → a * b ≠ 0 := begin[nat_num_game]
  intros anz bnz f,
  cases b, {
    apply bnz,
    refl
  }, {
    rw mul_succ at f,
    apply anz,
    induction a,
    refl, {
      apply add_left_eq_zero,
      rwa f,
    }
  }
end

theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : mynat) (h : a * b = 0) : a = 0 ∨ b = 0 := begin[nat_num_game]
  induction b, {
    right,
    refl
  }, {
    left,
    rw mul_succ at h,
    apply add_left_eq_zero,
    apply h
  }
end

theorem mul_eq_zero_iff (a b : mynat): a * b = 0 ↔ a = 0 ∨ b = 0 := begin[nat_num_game]
  split,
  apply eq_zero_or_eq_zero_of_mul_eq_zero, {
    intro or_eq_zero,
    cases or_eq_zero,
    rwa [or_eq_zero, zero_mul],
    rwa [or_eq_zero, mul_zero],
  }
end

theorem mul_left_cancel (a b c : mynat) (ha : a ≠ 0) : a * b = a * c → b = c := begin[nat_num_game]
  induction c generalizing b, {
    rw mul_zero,
    intro h,
    cases eq_zero_or_eq_zero_of_mul_eq_zero _ _ h, {
      exfalso,
      exact ha h_1
    }, exact h_1
  }, {
    intro eq,
    cases b, {
      rw mul_zero at eq,
      exfalso,
      apply ha,
      symmetry at eq,
      cases eq_zero_or_eq_zero_of_mul_eq_zero _ _ eq,
      exact h, {
        exfalso,
        exact succ_ne_zero _ h,
      }
    },{
      have hyp : b = c_n, {
        apply c_ih,
        rw mul_succ at eq,
        rw mul_succ at eq,
        apply add_right_cancel _ _ _ eq,
      },
      rwa hyp,
    }
  }
end

end mynat
