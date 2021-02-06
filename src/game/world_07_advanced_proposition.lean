import game.world_06_proposition
namespace mynat

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

end mynat
