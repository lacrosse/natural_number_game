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
  rwa [zero_mul],
  rwa [one_eq_succ_zero, mul_succ, mul_zero, zero_add],
end

lemma one_mul (m : mynat) : 1 * m = m := begin[nat_num_game]
  induction m,
  rwa [mul_zero],
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
  rwa [pow_zero],
end

lemma zero_pow_succ (m : mynat) : (0 : mynat) ^ (succ m) = 0 := begin[nat_num_game]
  rwa [pow_succ, mul_zero],
end

lemma pow_one (a : mynat) : a ^ (1 : mynat) = a := begin[nat_num_game]
  rwa [one_eq_succ_zero, pow_succ, pow_zero, one_mul],
end

lemma one_pow (m : mynat) : (1 : mynat) ^ m = 1 := begin[nat_num_game]
  induction m,
  rwa [pow_zero],
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
    (f9 : G → J) (f10 : I → J) (f11 : J → I) (f12 : I → H) (f13 : E → H) (f14 : H → K) (f15 : I → L) :
    A → L := begin[nat_num_game]
  apply f15 ∘ f11 ∘ f9 ∘ f8 ∘ f5 ∘ f2 ∘ f1,
end

end mynat
