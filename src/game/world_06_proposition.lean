import game.world_05_function
namespace mynat

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

end mynat
