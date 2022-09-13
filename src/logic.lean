
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro P,
  intro NoP,
  have boom : false := NoP P,
  exact boom,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro h,
  by_contradiction g,
  contradiction,
  
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  intro h,
  by_contradiction p,
  have boom: false := h p,
  contradiction,
  intro g,
  intro t,
  contradiction,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro pouq,
  cases pouq with p q,
  right,
  exact p,
  left,
  exact q,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro h,
  cases h with u v,
  split,
  exact v,
  exact u,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro Nopq,
  intro p,
  cases Nopq with np q,
  have boom: false := np p,
  contradiction,
  exact q,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro pouq,
  intro Nop,
  cases pouq with p q,
  have boom: false := Nop p,
  contradiction,
  exact q,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro PimpQ,
  intro NoQ,
  intro P,
  have Q: Q := PimpQ P,
  have boom: false := NoQ Q,
  exact boom,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro u,
  intro p,
  by_contra,
  have jj: ¬P := u h,
  contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
split,
apply impl_as_contrapositive,
apply impl_as_contrapositive_converse,

  
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro h,
  have g: (P∨¬P),
  right,
  intro j,
  have ll: (P∨¬P),
  left,
  exact j,
  contradiction,
  contradiction,

  
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro h,
  intro g,
  have hh: (P → Q),
  intro b,
  contradiction,
  have kj: P := h hh,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro h,
  intro g,
  cases h with p q,
  cases g with nop noq,
  have boom: false := nop p,
  contradiction,
  cases g with nop noq,
  have boom: false := noq q,
  exact boom,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro h,
  intro g,
  cases h with p q,
  cases g with nop noq,
  contradiction,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro h,
  split,
  intro g,
  have pq: (P∨Q),
  left,
  exact g,
  have boom: false:= h pq,
  contradiction,
  intro pp,
  have bom: (P∨Q),
  right,
  exact pp,
  contradiction,
  
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro h,
  intro g,
  cases h with nop noq,
  cases g with p q,
  contradiction,
  contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro h,
  by_cases df: Q,
  right,
  intro gg,
  have nb: P ∧ Q,
  split,
  exact gg,
  exact df,
  have boom: false := h nb,
  contradiction,
  left,
  exact df,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro h,
  intro g,
  cases g with u v,
  cases h with t o,
  contradiction,
  contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  apply demorgan_conj,
  apply demorgan_conj_converse,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  apply demorgan_disj,
  apply demorgan_disj_converse,

end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro p,
  cases p with u v,
  cases v with pp mm,
  left,
  split,
  exact u,
  exact pp,
  right,
  split,
  exact u,
  exact mm,
   
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro h,
  split,
  cases h with p q,
  cases p with pp f,
  exact pp,
  cases q with qq rr,
  exact qq,
  cases h with u v,
  cases u with t y,
  left,
  exact y,
  cases v with k l,
  right,
  exact l,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro h,
  cases h with u v,
  split,
  left,
  exact u,
  left,
  exact u,
  split,
  cases v with w e,
  right,
  exact w,
  right,
  cases v with bb nn,
  exact nn,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro f,
  cases f with d e,
  cases d with yy pp,
  cases e with gg kk,
  left,
  exact yy,
  left,
  exact yy,
  cases e with tt uu,
  left,
  exact tt,
  right,
  split,
  exact pp,
  exact uu,
  
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro h,
  intro g,
  intro f,
  have k: P ∧ Q,
  split,
  exact g,
  exact f,
  have pp: R := h k,
  exact pp,
  
  
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro h,
  intro g,
  cases g with p q,
  have qr: Q → R := h p,
  have r: R := qr q,
  exact r,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro h,
  exact h,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro h,
  left,
  exact h,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro h,
  right,
  exact h,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro h,
  cases h with u v,
  exact u,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro h,
  cases h with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro h,
  cases h with p hp,
  exact p,
  intro d,
  split,
  exact d,
  exact d,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro h,
  cases h with p hp,
  exact p,
  exact hp,
  intro g,
  left,
  exact g,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro h,
  intro x,
  intro p,
  apply h,
  existsi x,
  exact p,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro h,
  intro g,
  cases g with x e,
  have boom: ¬P x := h x,
  contradiction,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  rw contrapositive_law,
  rw doubleneg_law,
  intro h,
  intro x,
  by_cases j: P x,
  exact j,
  have: ∃ (x : U), ¬P x,
  existsi x,
  exact j,
  contradiction,
  
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro h,
  intro g,
  cases h with x e,
have boom: P x := g x,
contradiction,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  apply demorgan_forall,
  apply demorgan_forall_converse,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
split,
apply demorgan_exists,
apply demorgan_exists_converse,  
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro h,
  intro g,
  cases h with x e,
  have boom: ¬P x := g x,
  contradiction,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro h,
  intro g,
  cases g with x e,
  have tt: P x := h x,
  contradiction,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro h,
  intro x,
  have bt: ¬P x,
  intro pp,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  apply exists_as_neg_forall,

end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro h,
  cases h with x l,
  cases l with j m,
  split,
  existsi x,
  exact j,
  existsi x,
  exact m,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro h,
  cases h with x l,
  cases l with u v,
  left,
  existsi x,
  exact u,
  right,
  existsi x,
  exact v,
  
  
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro h,
  cases h with e k,
  cases e with x m,
  existsi x,
  left,
  exact m,
  cases k with d f,
  existsi d,
  right,
  exact f,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro h,
  split,
  intro x,
  have m: P x ∧ Q x := h x,
  cases m with t c,
  exact t,
  intro xx,
  have mm: P xx ∧ Q xx := h xx,
  cases mm with ee rr,
  exact rr,

end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  sorry,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  sorry,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
