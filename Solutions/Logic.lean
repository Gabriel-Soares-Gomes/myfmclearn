section propositional

variable (P Q R : Prop)


------------------------------------------------
-- Double negation
------------------------------------------------

theorem doubleneg_intro :
  P → ¬ ¬ P  := by
  intro hp
  intro hnp
  apply hnp hp

theorem doubleneg_elim :
  ¬ ¬ P → P  := by
  intro notnotP
  by_cases lem : P
  case pos =>
    exact lem
  case neg =>
    contradiction

theorem doubleneg_law :
  ¬ ¬ P ↔ P  := by
  constructor
  case mp =>
    intro notnotP
    by_cases lem : P
    case pos =>
      exact lem
    case neg =>
      contradiction

  case mpr =>
    intro hp
    intro notp
    contradiction



------------------------------------------------
-- Commutativity of ∨,∧
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  := by
  intro PorQ
  rcases PorQ with ( h1 | h2)
  case inl =>
    right
    exact h1

  case inr =>
    left
    exact h2


theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  := by
  intro PeQ
  rcases PeQ with ⟨h1, h2⟩
  constructor
  case intro.left =>
    exact h2
  case intro.right =>
    exact h1


------------------------------------------------
-- Interdefinability of →,∨
------------------------------------------------

theorem impl_as_disj_converse :
  (¬ P ∨ Q) → (P → Q)  := by
  intro notPorQ
  rcases notPorQ with (h1 | h2)
  case inl =>
    intro hp
    contradiction
  case inr =>
    intro hp
    exact h2


theorem disj_as_impl :
  (P ∨ Q) → (¬ P → Q)  := by
  intro PouQ
  rcases PouQ with (h1 | h2)
  case inl =>
    intro notP
    contradiction
  case inr =>
    intro notP
    exact h2


------------------------------------------------
-- Contrapositive
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬ Q → ¬ P)  := by
  intro PimpQ
  intro notQ
  intro hp
  have hq := PimpQ hp
  apply notQ hq

theorem impl_as_contrapositive_converse :
  (¬ Q → ¬ P) → (P → Q)  := by
  intro naoQimpnaoP
  intro p
  by_cases lem : Q
  case pos =>
    exact lem
  case neg =>
    have notP := naoQimpnaoP lem
    contradiction

theorem contrapositive_law :
  (P → Q) ↔ (¬ Q → ¬ P)  := by
  constructor
  case mp =>
    intro PimpQ
    intro notQ
    intro p
    have q := PimpQ p
    contradiction

  case mpr =>
    intro NotQimpNotP
    intro p
    by_cases lem : Q
    case pos =>
      exact lem
    case neg =>
      have notP := NotQimpNotP lem
      contradiction


------------------------------------------------
-- Irrefutability of LEM[P]
------------------------------------------------

theorem lem_irrefutable :
  ¬ ¬ (P ∨ ¬ P)  := by
  intro naoPORQ
  apply naoPORQ
  by_cases lem : P
  case pos =>
    left
    exact lem
  case neg =>
    right
    exact lem



------------------------------------------------
-- Peirce's law
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬ ¬ P  := by
  intro hpqp
  intro notP
  by_cases lem : P
  case pos =>
    contradiction
  case neg =>
    apply notP
    apply hpqp
    intro p
    contradiction


------------------------------------------------
-- Linearity of →
------------------------------------------------

theorem impl_linear :
  (P → Q) ∨ (Q → P)  := by
    by_cases lem : Q
    case pos =>
      left
      intro p
      exact lem
    case neg =>
      right
      intro q
      contradiction

------------------------------------------------
-- Interdefinability of ∨,∧
------------------------------------------------

theorem disj_as_negconj :
  P ∨ Q → ¬ (¬ P ∧ ¬ Q)  := by
  intro PorQ
  intro NPeNQ
  cases NPeNQ with
  | intro notP notQ =>
    rcases PorQ with (h1 | h2)
    case intro.inl =>
      contradiction
    case intro.inr =>
      contradiction

theorem conj_as_negdisj :
  P ∧ Q → ¬ (¬ P ∨ ¬ Q)  := by
  intro PeQ
  intro NaoPeNaoQ
  cases PeQ with
  | intro p q =>
    rcases NaoPeNaoQ with (h1 | h2)
    case intro.inl =>
      contradiction
    case intro.inr =>
      contradiction


------------------------------------------------
-- De Morgan laws for ∨,∧
------------------------------------------------

theorem demorgan_disj :
  ¬ (P ∨ Q) → (¬ P ∧ ¬ Q)  := by
  intro denyPouQ
  constructor
  case left =>
    intro p
    have PouQ : P ∨ Q := by
      left
      exact p
    contradiction
  case right =>
    intro q
    have PouQ : P ∨ Q := by
      right
      exact q
    contradiction

theorem demorgan_disj_converse :
  (¬ P ∧ ¬ Q) → ¬ (P ∨ Q)  := by
  intro nPandnQ
  intro PorQ
  cases nPandnQ with
  | intro nP nQ =>
  rcases PorQ with (h1 | h2)
  case intro.inl =>
    contradiction
  case intro.inr =>
    contradiction

theorem demorgan_conj :
  ¬ (P ∧ Q) → (¬ Q ∨ ¬ P)  := by
  intro denyPandQ
  by_cases lemp : P
  case pos =>
    by_cases lemq : Q
    case pos =>
      have PeQ : P ∧ Q := by
        constructor
        case left =>
          exact lemp
        case right =>
          exact lemq
      contradiction
    case neg =>
      left
      exact lemq
  case neg =>
    right
    exact lemp



theorem demorgan_conj_converse :
  (¬ Q ∨ ¬ P) → ¬ (P ∧ Q)  := by
  intro nQornP
  intro PandQ
  cases PandQ with
  | intro p q =>
    rcases nQornP with (h1 | h2)
    case intro.inl =>
      contradiction
    case intro.inr =>
      contradiction



theorem demorgan_conj_law :
  ¬ (P ∧ Q) ↔ (¬ Q ∨ ¬ P)  := by
  constructor
  case mp =>
    intro denyPandQ
    by_cases lemp : P
    case pos =>
      by_cases lemq : Q
      case pos =>
        have PandQ : P ∧ Q := by
          constructor
          case left =>
            exact lemp
          case right =>
            exact lemq
        contradiction

      case neg =>
        left
        exact lemq

    case neg =>
      right
      exact lemp

  case mpr =>
    intro nQornP
    intro PandQ
    cases PandQ with
    | intro p q
    rcases nQornP with (h1 | h2)
    case intro.inl =>
      apply h1 q
    case intro.inr =>
      apply h2 p





theorem demorgan_disj_law :
  ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q)  := by
  constructor
  case mp =>
    intro denyPorQ
    constructor
    case left =>
      intro p
      have PorQ : P ∨ Q := by
        left
        exact p
      contradiction
    case right =>
      intro q
      have PorQ : P ∨ Q := by
        right
        exact q
      contradiction

  case mpr =>
    intro nPandnQ
    intro PorQ
    rcases PorQ with (h1 | h2)
    case inl =>
      cases nPandnQ with
      |intro nP nQ =>
        apply nP h1

    case inr =>
      cases nPandnQ with
        |intro nP nQ =>
          apply nQ h2


------------------------------------------------
-- Distributivity laws between ∨,∧
------------------------------------------------

theorem distr_conj_disj :
  P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)  := by
  intro h
  cases h with
  |intro p QorR =>
    rcases QorR with (q | r)
    case intro.inl =>
      left
      constructor
      case h.left =>
        exact p
      case h.right =>
        exact q

    case intro.inr =>
      right
      constructor
      case h.left =>
        exact p
      case h.right =>
        exact r




theorem distr_conj_disj_converse :
  (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)  := by
  intro hor
  rcases hor with (PeQ | PeR)
  case inl =>
    cases PeQ with
    | intro p q =>
    constructor
    case intro.left =>
      exact p
    case intro.right =>
      left
      exact q

  case inr =>
    cases PeR with
    | intro p r =>
    constructor
    case intro.left =>
      exact p
    case intro.right =>
      right
      exact r


theorem distr_disj_conj :
  P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)  := by
  intro h
  rcases h with (p | QeR)
  case inl =>
    constructor
    case left =>
      left
      exact p
    case right =>
      left
      exact p

  case inr =>
    cases QeR with
    | intro q r =>
    constructor
    case intro.left =>
      right
      exact q
    case intro.right =>
      right
      exact r


theorem distr_disj_conj_converse :
  (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)  := by
  intro h
  cases h with
  |intro PorQ PorR =>
  rcases PorQ with (p | q)
  case intro.inl =>
    left
    exact p

  case intro.inr =>
    rcases PorR with (p | r)
    case inl =>
      left
      exact p
    case inr =>
      right
      constructor
      case h.left =>
        exact q
      case h.right =>
        exact r



------------------------------------------------
-- Currying
------------------------------------------------

theorem curry_prop :
  ((P ∧ Q) → R) → (P → (Q → R))  := by
  intro h
  intro p
  intro q
  have PeQ : P ∧ Q := by
    constructor
    case left =>
      exact p
    case right =>
      exact q
  apply h PeQ

theorem uncurry_prop :
  (P → (Q → R)) → ((P ∧ Q) → R)  := by
  intro h
  intro PeQ
  rcases PeQ with ⟨p, q⟩
  have QimpR : Q → R := h p
  apply QimpR q


------------------------------------------------
-- Reflexivity of →
------------------------------------------------

theorem impl_refl :
  P → P  := by
  intro p
  exact p


------------------------------------------------
-- Weakening and contraction
------------------------------------------------

theorem weaken_disj_right :
  P → (P ∨ Q)  := by
  intro p
  left
  exact p

theorem weaken_disj_left :
  Q → (P ∨ Q)  := by
  intro q
  right
  exact q

theorem weaken_conj_right :
  (P ∧ Q) → P  := by
  intro PeQ
  rcases PeQ with ⟨p, q⟩
  exact p

theorem weaken_conj_left :
  (P ∧ Q) → Q  := by
  intro PeQ
  rcases PeQ with ⟨p, q⟩
  exact q


------------------------------------------------
-- Idempotence of ∨,∧
------------------------------------------------

theorem disj_idem :
  (P ∨ P) ↔ P  := by
  constructor
  case mp =>
    intro PorP
    rcases PorP with (p1 | p2)
    case inl =>
      exact p1
    case inr =>
      exact p2

  case mpr =>
    intro p
    right
    exact p

theorem conj_idem :
  (P ∧ P) ↔ P := by
  constructor
  case mp =>
    intro PeP
    rcases PeP with ⟨p1, p2⟩
    exact p1

  case mpr =>
    intro p
    constructor
    case left =>
      exact p
    case right =>
      exact p



------------------------------------------------
-- Bottom, Top
------------------------------------------------

theorem false_bottom :
  False → P := by
  intro falso
  contradiction

theorem true_top :
  P → True  := by
  intro p
  trivial


end propositional

----------------------------------------------------------------

section predicate

variable (U : Type)
variable (P Q : U → Prop)


------------------------------------------------
-- De Morgan laws for ∃,∀
------------------------------------------------

theorem demorgan_exists :
  ¬ (∃ x, P x) → (∀ x, ¬ P x)  := by
  intro h
  intro x
  intro hpx
  apply h
  exists x

theorem demorgan_exists_converse :
  (∀ x, ¬ P x) → ¬ (∃ x, P x)  := by
  intro h
  intro eXtqPx
  obtain ⟨x, px⟩ := eXtqPx
  have nPx := h x
  contradiction

theorem demorgan_forall :
  ¬ (∀ x, P x) → (∃ x, ¬ P x)  := by
  intro h
  apply Classical.byContradiction
  intro h2
  apply h
  intro x
  apply Classical.not_not.mp
  intro hnpx
  apply h2
  exists x



theorem demorgan_forall_converse :
  (∃ x, ¬ P x) → ¬ (∀ x, P x)  := by
  intro h_exnpx
  intro h_ptxpx
  obtain ⟨x, px⟩ := h_exnpx
  have h_px := h_ptxpx x
  contradiction



theorem demorgan_forall_law :
  ¬ (∀ x, P x) ↔ (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_law :
  ¬ (∃ x, P x) ↔ (∀ x, ¬ P x)  := by
  constructor
  case mp =>
    intro h_nexpx
    intro x
    intro px
    apply h_nexpx
    apply Exists.intro x px

  case mpr =>
    intro paratdXpx
    intro existeXtqpx
    obtain ⟨x, px⟩ := existeXtqpx
    have npx := paratdXpx x
    contradiction


------------------------------------------------
-- Interdefinability of ∃,∀
------------------------------------------------

theorem exists_as_neg_forall :
  (∃ x, P x) → ¬ (∀ x, ¬ P x)  := by
  intro existeXtqPx
  intro paratdXnPx
  obtain ⟨x, px⟩ := existeXtqPx
  have npx := paratdXnPx x
  contradiction

theorem forall_as_neg_exists :
  (∀ x, P x) → ¬ (∃ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists_converse :
  ¬ (∃ x, ¬ P x) → (∀ x, P x)  := by
  sorry

theorem exists_as_neg_forall_converse :
  ¬ (∀ x, ¬ P x) → (∃ x, P x)  := by
  sorry

theorem forall_as_neg_exists_law :
  (∀ x, P x) ↔ ¬ (∃ x, ¬ P x)  := by
  sorry

theorem exists_as_neg_forall_law :
  (∃ x, P x) ↔ ¬ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
--  Distributivity between quantifiers
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists :
  (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists_converse :
  (∃ x, P x) ∨ (∃ x, Q x) → (∃ x, P x ∨ Q x)  := by
  sorry

theorem forall_conj_as_conj_forall :
  (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x)  := by
  sorry

theorem forall_conj_as_conj_forall_converse :
  (∀ x, P x) ∧ (∀ x, Q x) → (∀ x, P x ∧ Q x)  := by
  sorry

theorem forall_disj_as_disj_forall_converse :
  (∀ x, P x) ∨ (∀ x, Q x) → (∀ x, P x ∨ Q x)  := by
  sorry


end predicate

------------------------------------------------

section bonus

------------------------------------------------
--  Drinker's paradox
------------------------------------------------

variable (D : U → Prop)

-- There is a person p such that:
-- if p drinks, then everybody drinks
-- p: «person»
-- D x: «x drinks»
theorem drinker :
  ∃ p, (D p → ∀ x, D x)  := by
  sorry

------------------------------------------------
--  Russell's paradox
------------------------------------------------

variable (S : U → U → Prop)

-- It is impossible to have a barber b such that
-- b shaves exactly those people who do not shave themselves
-- b: «barber»
-- S x y: «x shaves y»
theorem russell :
  ¬ ∃ b, ∀ x, (S b x ↔ ¬ S x x)  := by
  sorry


end bonus


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)  := by
  sorry

theorem exists_conj_as_conj_exists_converse :
  (∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x)  := by
  sorry

---------------------------------------------- -/
