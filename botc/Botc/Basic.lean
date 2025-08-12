import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.ApplyAt

inductive Alignment
  | good
  | evil
  deriving DecidableEq, Nonempty

inductive Class
  | townsfolk
  | outsider
  | minion
  | demon
  deriving DecidableEq, Nonempty

namespace Class

def defaultAlignment : Class → Alignment
  | .townsfolk
  | .outsider => .good
  | .minion
  | .demon => .evil


-- instance (c : Class) (a : Alignment) : Decidable (c.defaultAlignment = a) := by
--   rw [defaultAlignment.eq_def]
--   cases c <;> cases a <;> first
--     | right; trivial;
--     | left; simp only [reduceCtorEq, not_false_eq_true]

end Class

inductive Role
  | virgin
  | noble
  | artist
  | slayer
  | nightwatchman
  | washerwoman
  | golem
  | recluse
  | poisoner
  | scarletwoman
  | spy
  | boffin
  | kazali
  deriving DecidableEq, Nonempty

def Role.class : Role → Class
  | .virgin
  | .noble
  | .artist
  | .slayer
  | .nightwatchman
  | .washerwoman => .townsfolk
  | .golem
  | .recluse => .outsider
  | .poisoner
  | .scarletwoman
  | .spy
  | .boffin => .minion
  | .kazali => .demon

-- instance (r : Role) (c : Class) : Decidable (r.class = c) := by
--   rw [Role.class.eq_def]
--   cases r <;> cases c <;> first
--     | simp; right; trivial;
--     | left; simp

namespace Role


def defaultAlignment (r : Role) := r.class.defaultAlignment

theorem roleClassDefaultAlignment {r : Role} {a : Alignment} (h : r.defaultAlignment = a) :
  (r.class.defaultAlignment = a) := by
    rw [Role.defaultAlignment] at h
    exact h

-- instance (r : Role) (a : Alignment) : Decidable (r.defaultAlignment = a) := by
--   rw [Role.defaultAlignment, Role.class.eq_def, Class.defaultAlignment.eq_def]
--   cases r <;> cases a <;> first
--     | simp only [reduceCtorEq]; right; trivial;
--     | left; simp only [reduceCtorEq, not_false_eq_true]

end Role

structure Player where
  droisoned : Bool
  alignment : Alignment
  role : Role
  deriving DecidableEq

-- def _ : Member

namespace Player

-- abbrev

def isDefaultAlignment (p : Player) := p.alignment = p.role.defaultAlignment

instance instIsDefaultAlignment (p : Player) : Decidable (isDefaultAlignment p) :=
  instDecidableEqAlignment p.alignment p.role.defaultAlignment


def isGood (p : Player) := p.alignment = .good

instance (p : Player) : Decidable (p.isGood) := by
  simp [Player.isGood]
  cases p.alignment <;> first
    | right; rfl
    | left; simp only [reduceCtorEq, not_false_eq_true]



def isEvil (p : Player) := p.alignment = .evil

instance (p : Player) : Decidable (p.isEvil) := by
  simp [Player.isEvil]
  cases p.alignment <;> first
    | right; rfl
    | left; simp only [reduceCtorEq, not_false_eq_true]


theorem isGoodIffnIsEvil (p : Player) : (p.isGood ↔ ¬p.isEvil) := by
  rewrite [isGood, isEvil]
  cases p.alignment with simp

def exactlyNone (ps : List Player) (cond : Player → Prop) := (¬ (∃ p ∈ ps, cond p))

@[simp]
theorem exactlyNoneOfNone {ps : List Player}
  {h : ps = []}
  {cond : Player → Prop} :
  (exactlyNone ps cond) = True := by
  rw [exactlyNone, h]

  simp only [List.not_mem_nil, false_and, exists_false, not_false_eq_true]

@[simp]
theorem exactlyNoneOfOne {x : Player}
  {cond : Player → Prop} :
  exactlyNone [x] cond = ¬ cond x := by

  rw [exactlyNone]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_left]


def instExactlyNone (ps : List Player) (cond : Player → Prop) [inst : DecidablePred cond]
  : Decidable (exactlyNone ps cond) := by
  rw [exactlyNone]
  have tmp := by exact ps.decidableBEx cond
  cases tmp <;> first
    | right; assumption
    | left; simp; assumption

def exactlyOne (ps : List Player) (cond : Player → Prop) [inst : DecidablePred cond] :=
  match ps with
  | .nil => False
  | .cons p ps => if ¬ cond p then exactlyOne ps cond else exactlyNone ps cond


@[simp]
theorem exactlyOneOfNone
  {cond : Player → Prop}
  [inst : DecidablePred cond] : (exactlyOne [] cond) = False := by
  rw [exactlyOne.eq_def]

@[simp]
theorem exactlyOneOfOne
  {x : Player}
  {cond : Player → Prop}
  [inst : DecidablePred cond] : (exactlyOne [x] cond) = (cond x) := by
  rw [exactlyOne.eq_def]

  simp only [exactlyOneOfNone, exactlyNoneOfNone, ite_not, if_false_right, and_true]

@[simp]
theorem exactlyOneOfCons {p : Player}
  {ps : List Player}
  {cond : Player → Prop}
  (h : ¬ cond p)
  [inst : DecidablePred cond] : (exactlyOne (p :: ps) cond) = (exactlyOne (ps) cond) := by
  rw [exactlyOne.eq_def]
  simp only [h, not_false_eq_true, ↓reduceIte]


theorem exactlyOneImpliesExists
  {ps : List Player}
  {cond : Player → Prop}
  [inst : DecidablePred cond]
  (h : exactlyOne ps cond) :
  ∃ p ∈ ps, cond p := by
  induction ps with
    | nil => trivial
    | cons p ps ih =>
      by_cases h₂ : cond p <;> simp [h₂]
      exact (exactlyOneOfCons h₂).mp h |> ih

@[simp]
theorem exactlyOneOfTwo
  {p₁ p₂ : Player}
  {cond : Player → Prop}
  [inst : DecidablePred cond] : (exactlyOne ([p₁, p₂]) cond) = ¬ (cond p₁ ↔ cond p₂) := by
  rw [exactlyOne]
  by_cases h : cond p₁
  · simp only [h, not_true_eq_false, ↓reduceIte, exactlyNoneOfOne, true_iff]
  simp only [h, not_false_eq_true, ↓reduceIte, exactlyOneOfOne, false_iff, Decidable.not_not]


-- def instExactlyOne (ps : List Player) (cond : Player →  Prop) [inst : DecidablePred cond]
--   : Decidable (exactlyOne ps cond) := by
--   rw [exactlyOne]

--   have tmp := by exact ps.decidableBEx cond




-- def exactlyOne (ps : List Player) (cond : Player → Prop) [DecidablePred cond] := match ps with
--   | .nil => False
--   | .cons p ps => if cond p then exactlyNone ps cond else exactlyOne ps cond

def atMostOne (ps : List Player) (cond : Player → Prop) [inst : DecidablePred cond] :=
   exactlyNone ps cond ∨ exactlyOne ps cond



def diesToVirginAbility (p : Player) := p.role.class = .townsfolk ∨ (p.role = .spy ∧ ¬p.droisoned)

-- demon can't mis
def diesToGolemAbility (p : Player) := p.role.class ≠ .demon

def diesToSlayerAbility (p : Player) := p.role.class = .demon ∨ (p.role = .recluse ∧ ¬p.droisoned)

instance instDecidablePlayerInPlayers (ps : List Player) (p : Player) :
  Decidable (p ∈ ps) := match ps with
  | .nil => isFalse <| by simp only [List.not_mem_nil, not_false_eq_true]

  | .cons p₂ ps₂ => match instDecidableEqPlayer p p₂ with
    | isTrue h => isTrue <| by
      repeat rewrite [List.mem_cons]
      exact Or.inl h
    | isFalse h => match instDecidablePlayerInPlayers ps₂ p with
      | isTrue h₂ => isTrue <| by
        repeat rewrite [List.mem_cons]
        exact Or.inr h₂

      | isFalse h₂ => isFalse <| by
        repeat rewrite [List.mem_cons, not_or]
        exact ⟨h, h₂⟩

end Player

def exactlyN {α}
   (xs : List α)
   (n : ℕ)
   (cond : α → Prop)
   [inst : DecidablePred cond] := match xs, n with
  | .nil, 0 => True
  | .nil, _ => False
  | .cons x xs', n =>
    if ¬ cond x then
      exactlyN xs' n cond
    else if n > 0 then
      exactlyN xs' n.pred cond
    else
      False

def atMostN {α}
   (xs : List α)
   (n : ℕ)
   (cond : α → Prop)
   [inst : DecidablePred cond] := match xs, n with
   | _, 0 => ¬ ∃ x ∈ xs, cond x
   | .nil, _ => True
   | .cons x xs', n => if cond x then
       atMostN xs' n.pred cond
     else
       atMostN xs' n cond

@[simp]
theorem atMostNConsFalse {α}
  {x₀ : α}
  {cond : α → Prop}
  (h₀ : ¬ cond x₀)
  (xs : List α)
  (n : ℕ)
  [inst : DecidablePred cond]
  : atMostN (x₀ :: xs) n cond ↔ atMostN xs n cond := by
  rw [atMostN.eq_def]

  cases n with
    | zero =>
      simp [h₀];
      rw [atMostN.eq_def];
      simp
    | succ n =>
      simp [h₀]

@[simp]
theorem atMostNConsTrue {α}
  {x₀ : α}
  {cond : α → Prop}
  (h₀ : cond x₀)
  (xs : List α)
  (n : ℕ)
  [inst : DecidablePred cond]
  : atMostN (x₀ :: xs) n.succ cond ↔ (atMostN xs n cond) := by
  rw [atMostN.eq_def]

  cases n with
    | zero => simp [h₀]
    | succ n =>
      simp [h₀]

theorem atMostSuccN {α}
  {xs : List α}
  {cond : α → Prop}
  {n : ℕ}
  [inst : DecidablePred cond]
  (h : atMostN xs n cond)
  : atMostN xs (n + 1) cond := by
  induction xs generalizing n with
    | nil =>
      rw [atMostN]
      repeat simp
    | cons hn t ih =>
      cases n with
        | zero =>
          have h₂ : ¬ cond hn := by
            rw [atMostN] at h
            simp at h
            exact h.left

          rw [atMostNConsFalse h₂] at h
          rw [atMostNConsFalse h₂]
          exact ih h
        | succ n =>
          by_cases h₂ : cond hn
          · rw [atMostNConsTrue h₂] at h
            rw [atMostNConsTrue h₂]
            exact ih h
          rw [atMostNConsFalse h₂] at h
          rw [atMostNConsFalse h₂]
          exact ih h

theorem atMostNOfN {α}
  (xs : List α)
  (n : ℕ)
  (hLen : xs.length <= n)
  (cond : α → Prop)
  [inst : DecidablePred cond]
  : (atMostN xs n cond)
  := by
  induction xs generalizing n with
    | nil =>
      simp at hLen
      rw [atMostN.eq_def]
      simp
      cases n with
        | zero => simp
        | succ n => simp
    | cons h t ih =>
      simp at hLen

      by_cases h₂ : cond h

      · cases n with
        | zero =>
          simp at hLen
        | succ n =>
        simp at hLen
        have tmp := ih n hLen



        rw [atMostNConsTrue h₂]
        exact tmp

      rw [atMostNConsFalse h₂]

      cases n with
        | zero =>
          simp at hLen
        | succ n =>
          simp at hLen
          have tmp := ih n hLen
          exact atMostSuccN tmp

theorem atMost1Of2 {α}
  {a b : α}
  {cond : α → Prop}
  [inst : DecidablePred cond]
  (h : atMostN [a, b] 1 cond)
  : ¬ (cond a ∧ cond b) := by
  simp
  simp [atMostN] at h
  trivial


def allDefaultAlignment (ps : List Player) := ∀ (p : Player), p ∈ ps → p.isDefaultAlignment

instance instAllDefaultAlignment (ps : List Player) :
  Decidable (∀ (p : Player), p ∈ ps → p.isDefaultAlignment) :=
  ps.decidableBAll Player.isDefaultAlignment

def allUniqueRoles (ps : List Player) := ps.Pairwise (·.role ≠ ·.role)

theorem aliceBobDefaultAlignment (a : Player) (b : Player)
  (ha : a.isDefaultAlignment) (hb : b.isDefaultAlignment)
  : (allDefaultAlignment [a, b]) := by

  rewrite [allDefaultAlignment]

  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]

  exact ⟨ha, hb⟩




-- def Tmp := Quot

-- def allDefaultAlignment : Prop := (ps : Subset Player)
