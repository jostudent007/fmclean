
section propositional

variables P Q R : Prop

-- Usando {} pra formatar o cases e by_cases
------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intros p hp,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro hp,
  by_cases p:P,
  {
    exact p,
  },
  {
    exfalso,
    exact hp p,
  }
  end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  apply doubleneg_elim,
  apply doubleneg_intro,
end

------------------------------------------------
-- Comutatividade dos ∨,∧: 
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro pq,
  cases pq with p q,
  {
    right,
    exact p,
  },
  {
    left,
    exact q,
  }
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro pq,
  split,
  exact pq.2,
  exact pq.1,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intros npq p,
  cases npq with np q,
  {
    exfalso,
    exact np p,
  },
 exact q,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intros pq np,
  cases pq with p q,
  {
    exfalso,
    exact np p,
  },
  exact q,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intros pq nq np,
  exact nq (pq np),
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intros h p,
  by_cases q : Q,
  {
    exact q,
  },
  exfalso,
  apply h q,
  exact p,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  exact impl_as_contrapositive P Q,
  exact impl_as_contrapositive_converse P Q,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
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

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intros pqp nnp,
  apply nnp,
  apply pqp,
  intro p,
  exfalso,
  exact nnp p,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intros pq npq,
  cases pq with p q,
  {
    exact npq.1 p,
  },
  {
    exact npq.2 q,
  }
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intros pq npq,
  cases npq with np nq,
  {
    exact np pq.1,
  },
  {
    exact nq pq.2,
  }
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro npq,
  split,
  intro p,
  apply npq,
  left,
  exact p,
  intro q,
  apply npq,
  right,
  exact q,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intros npq pq,
  have h : false := disj_as_negconj P Q pq npq,
  exact h,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro npq,
  by_cases p : P,
  {
    left,
    intro q,
    apply npq,
    split,
    {
      exact p,
    },
    {
      exact q,
    }
  },
  {
    right,
    exact p,
  }
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intros h pq,
  cases h with nq np,
  {
    exact nq pq.2,
  },
  {
    exact np pq.1,
  }
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
  intros h,
  have p : P := h.1,
  have qr : Q ∨ R := h.2,
  cases qr with q r,
  {
    left,
    split,
    {
      exact p,
    },
    {
      exact q,
    }
  },
  {
    right,
    split,
    {
      exact p,
    },
    {
      exact r,
    }
  }
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro h,
  cases h with pq pr,
  {
    split,
    {
      exact pq.1,
    },
    {
      left,
      exact pq.2,
    }
  },
  {
    split,
    {
      exact pr.1,
    },
    {
      right,
      exact pr.2,
    }
  }
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
   intro h,
  cases h with p qr,
  {
    split,
    {
      left,
      exact p,
    },
    {
      left,
      exact p,
    }
  },
  {
    split,
    {
      right,
      exact qr.1,
    },
    {
      right,
      exact qr.2,
    }
  }
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro h,
  have pq : P ∨ Q := h.1,
  have pr : P ∨ R := h.2,
  cases pq with p q,
  {
    left,
    exact p,
  },
  {
    cases pr with p r,
    {
      left,
      exact p,
    },
    {
      right,
      split,
      {
        exact q,
      },
      {
        exact r,
      }
    }
  } 
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intros h p q,
  apply h,
  split,
  {
    exact p,
  },
  {
    exact q,
  }
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros h pq,
  have qr : Q → R := h pq.1,
  have r : R := qr pq.2,
  exact r,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro h,
  exact h.1,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro h,
  exact h.2,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro p,
  exact p.1,
  intro p,
  split,
  {
    exact p,
  },
  {
    exact p,
  }
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  {
    intro h,
    cases h with p p,
    {
      exact p,
    },
    {
      exact p,
    }
  },
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
  intros h u hu,
  apply h,
  existsi u,
  exact hu,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intros h hu,
  cases hu with n hn,
  have nhn := h n,
  apply nhn,
  exact hn,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro h,
  by_contra hj,
  apply h,
  intro u,
  by_contra hpj,
  apply hj,
  existsi u,
  exact hpj,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intros h hp,
  cases h with u pu,
  have pv : P u := hp u,
  exact pu pv,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  exact demorgan_forall U P,
  exact demorgan_forall_converse U P,
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
  intros h hp,
  cases h with u hu,
  have nhu : ¬P u := hp u,
  exact nhu hu,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intros h hp,
  cases hp with u nhu,
  have hu : P u := h u,
  exact nhu hu,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intros h u,
  by_contra hu,
  apply h,
  existsi u,
  exact hu,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro h,
  by_contra hu,
  apply h,
  intros u pu,
  apply hu,
  existsi u,
  exact pu,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  apply forall_as_neg_exists U P,
  apply forall_as_neg_exists_converse U P,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  apply exists_as_neg_forall U P,
  apply exists_as_neg_forall_converse U P,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro h,
  cases h with u hu,
  split,
  {
    existsi u,
    exact hu.1,
  },
  {
    existsi u,
    exact hu.2,
  }
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro h,
  cases h with u hu,
  cases hu with p q,
  {
    left,
    existsi u,
    exact p,
  },
  {
    right,
    existsi u,
    exact q,
  }
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro h,
  cases h with p q,
  {
    cases p with u p,
    existsi u,
    left,
    exact p,
  },
  {
    cases q with u q,
    existsi u,
    right,
    exact q,
  }
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro h,
  split,
  {
    intro u,
    have hu : P u ∧ Q u := h u,
    exact hu.1
  },
  {
    intro u,
    have hu : P u ∧ Q u := h u,
    exact hu.2
  }
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intros h u,
  split,
  {
    have p : P u := h.1 u,
    exact p,
  },
  {
    have q : Q u := h.2 u,
    exact q,
  }
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intros h u,
  cases h with hp hq,
  {
    left,
    have p : P u := hp u,
    exact p,
  },
  {
    right,
    have q : Q u := hq u,
    exact q,
  }
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
