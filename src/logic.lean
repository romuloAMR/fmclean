
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro : P → ¬¬P  :=
begin
  intro p,
  intro np,
  exact np p,
end

theorem doubleneg_elim : ¬¬P → P  :=
begin
  intro nnp,
  by_cases P,
  exact h,
  exfalso,
  exact nnp h, 
end

theorem doubleneg_law : ¬¬P ↔ P  :=
begin
  split,
  exact doubleneg_elim P,
  exact doubleneg_intro P,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm : (P ∨ Q) → (Q ∨ P)  :=
begin
  intro pq,
  cases pq,
  right,
  exact pq,
  left,
  exact pq,
end

theorem conj_comm : (P ∧ Q) → (Q ∧ P)  :=
begin
  intro pq,
  cases pq with p q,
  split,
  exact q,
  exact p,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse : (¬P ∨ Q) → (P → Q)  :=
begin
  intro np_q,
  intro p,
  cases np_q with np q,
  exfalso,
  exact np p,
  exact q,
end

theorem disj_as_impl : (P ∨ Q) → (¬P → Q)  :=
begin
  intro p_q,
  intro np,
  cases p_q with p q,
  exfalso,
  exact np p,
  exact q,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive : (P → Q) → (¬Q → ¬P)  :=
begin
  intro h,
  intro nq,
  intro p,
  exact nq (h p),
end

theorem impl_as_contrapositive_converse : (¬Q → ¬P) → (P → Q)  :=
begin
  intro a,
  intro p,
  by_cases Q,
  exact h,
  have r := a h,
  exfalso,
  exact r p,
end

theorem contrapositive_law : (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  exact impl_as_contrapositive P Q,
  exact impl_as_contrapositive_converse P Q,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable : ¬¬(P∨¬P)  :=
begin
  intro h,
  apply h,
  right,
  intro p,
  apply h,
  left,
  exact p,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak : ((P → Q) → P) → ¬¬P  :=
begin
  intro h,
  intro np,
  apply np,
  apply h,
  intro p,
  exfalso,
  exact np p,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj : P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro h,
  intro hi,
  cases hi with np nq,
  cases h,
  exact np h,
  exact nq h,
end

theorem conj_as_negdisj : P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro h,
  cases h with p q,
  intro hi,
  cases hi,
  exact hi p,
  exact hi q,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj : ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro h,
  split,
  intro p,
  apply h,
  left,
  exact p,
  intro q,
  apply h,
  right,
  exact q,
end

theorem demorgan_disj_converse : (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro h,
  intro hi,
  cases h with np nq,
  cases hi,
  exact np hi,
  exact nq hi,
end

theorem demorgan_conj : ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  sorry,
end

theorem demorgan_conj_converse : (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro i,
  intro pq,
  cases pq,
  cases i,
  exact i pq_right,
  exact i pq_left,
end

theorem demorgan_conj_law : ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  sorry,
end

theorem demorgan_disj_law : ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  exact demorgan_disj P Q,
  exact demorgan_disj_converse P Q,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj : P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro i,
  cases i with p h,
  cases h,
  left,
  split,
  exact p,
  exact h,
  right,
  split,
  exact p,
  exact h,
end

theorem distr_conj_disj_converse : (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro i,
  split,
  cases i,
  cases i,
  exact i_left,
  cases i,
  exact i_left,
  cases i,
  cases i,
  left,
  exact i_right,
  cases i,
  right,
  exact i_right,
end

theorem distr_disj_conj : P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro i,
  split,
  cases i,
  left,
  exact i,
  cases i,
  right,
  exact i_left,
  cases i,
  left,
  exact i,
  cases i,
  right,
  exact i_right,
end

theorem distr_disj_conj_converse : (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro i,
  cases i with l r,
  cases l,
  left,
  exact l,
  cases r,
  left,
  exact r,
  right,
  split,
  exact l,
  exact r,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop : ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro i,
  intro p,
  intro q,
  apply i,
  split,
  exact p,
  exact q,
end

theorem uncurry_prop : (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro i,
  intro pq,
  cases pq with p q,
  apply i,
  exact p,
  exact q,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl : P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right : P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left : Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right : (P∧Q) → P  :=
begin
  intro pq,
  cases pq with p q,
  exact p,
end

theorem weaken_conj_left : (P∧Q) → Q  :=
begin
  intro pq,
  cases pq with p q,
  exact q,
end

theorem conj_idempot : (P∧P) ↔ P :=
begin
  split,
  intro pp,
  cases pp with p p,
  exact p,
  intro p,
  split,
  exact p,
  exact p,
end

theorem disj_idempot : (P∨P) ↔ P  :=
begin
  split,
  intro pp,
  cases pp,
  exact pp,
  exact pp,
  intro p,
  left,
  exact p,
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
  intro i,
  intro x,
  intro px,
  apply i,
  existsi x,
  exact px,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro i,
  intro h,
  cases h with u pu,
  have r := i u,
  apply r,
  exact pu,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro i,
  intro h,
  cases i with u pu,
  have r := h u,
  exact pu r,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  exact demorgan_exists U P,
  exact demorgan_exists_converse U P,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  sorry,
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
  sorry,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  sorry,
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
