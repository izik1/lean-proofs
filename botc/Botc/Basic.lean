import Mathlib.Init

set_option linter.style.longLine true

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

def good (c : Class) := c = .townsfolk ∨ c = .outsider

@[simp]
theorem defaultAlignmentIffGood {c : Class} : c.defaultAlignment = .good ↔ c.good := by
  rw [defaultAlignment.eq_def, good.eq_def]

  cases c <;> decide

def evil (c : Class) := c = .minion ∨ c = .demon

@[simp]
theorem defaultAlignmentIffEvil {c : Class} : c.defaultAlignment = .evil ↔ c.evil := by
  rw [defaultAlignment.eq_def, evil.eq_def]
  cases c <;> decide

-- instance (c : Class) (a : Alignment) : Decidable (c.defaultAlignment = a) := by
--   rw [defaultAlignment.eq_def]
--   cases c <;> cases a <;> first
--     | right; trivial;
--     | left; simp only [reduceCtorEq, not_false_eq_true]

end Class

inductive Role
  | artist
  | virgin
  | noble
  | savant
  | slayer
  | nightwatchman
  | washerwoman
  | drunk
  | golem
  | recluse
  | boffin
  | goblin
  | poisoner
  | scarletwoman
  | spy
  | kazali
  | leviathan
  deriving DecidableEq, Nonempty

def Role.class : Role → Class
  | .artist
  | .virgin
  | .noble
  | .savant
  | .slayer
  | .nightwatchman
  | .washerwoman => .townsfolk
  | .drunk
  | .golem
  | .recluse => .outsider
  | .boffin
  | .goblin
  | .poisoner
  | .scarletwoman
  | .spy => .minion
  | .kazali
  | .leviathan => .demon

-- instance (r : Role) (c : Class) : Decidable (r.class = c) := by
--   rw [Role.class.eq_def]
--   cases r <;> cases c <;> first
--     | simp; right; trivial;
--     | left; simp

namespace Role


def demon (r : Role) : Prop := r = .kazali ∨ r = .leviathan

def minion (r : Role) : Prop := r ∈ [.boffin, .goblin, .poisoner, .scarletwoman, .spy]

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

def diesToVirginAbility (p : Player) := p.role.class = .townsfolk ∨ (p.role = .spy ∧ ¬p.droisoned)

-- demon can't misregister
def diesToGolemAbility (p : Player) := p.role.class ≠ .demon

def diesToSlayerAbility (p : Player) := p.role.class = .demon ∨ (p.role = .recluse ∧ ¬p.droisoned)

instance instDecidablePlayerInPlayers (ps : List Player) (p : Player) :
  Decidable (p ∈ ps) := match ps with
  | [] => isFalse <| by simp only [List.not_mem_nil, not_false_eq_true]

  | p₂::ps₂ => match instDecidableEqPlayer p p₂ with
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
   (n : Nat)
   (cond : α → Prop)
   [inst : DecidablePred cond] := match xs, n with
  | [], 0 => True
  | [], _ => False
  | x::xs', n =>
    if ¬ cond x then
      exactlyN xs' n cond
    else if n > 0 then
      exactlyN xs' n.pred cond
    else
      False


@[simp]
theorem exactlyNNilIff
  {α}
  {n : Nat}
  {cond : α → Prop}
  [inst : DecidablePred cond]
  : exactlyN [] n cond ↔ n = 0
  := by
  by_cases h : n = 0
  <;> simp [h]

  <;> rw [exactlyN]
  · trivial
  · trivial
  simp [h]

@[simp]
theorem exactlyNZeroIff
  {α}
  {xs : List α}
  {cond : α → Prop}
  [inst : DecidablePred cond]
  : exactlyN xs 0 cond ↔ ∀ (x : α), x ∈ xs → ¬cond x
  := by
  induction xs with
    | nil => simp only [exactlyNNilIff, List.not_mem_nil, false_implies, implies_true]
    | cons x xs ih =>
      rw [exactlyN]
      simp only [ih, gt_iff_lt, Nat.lt_irrefl, ↓reduceIte, ite_not, if_false_left, List.mem_cons,
        forall_eq_or_imp]


-- slightly lower priority than the specialized "zero" ones
@[simp 998]
theorem exactlyNConsFalseIff
  {α}
  {xs : List α}
  {x : α}
  {n : Nat}
  {cond : α → Prop}
  (ha : ¬ cond x)
  [inst : DecidablePred cond]
  : exactlyN (x::xs) n cond ↔ exactlyN xs n cond
  := by
  rw [exactlyN]
  simp [ha]

@[simp]
theorem exactlyNConsSuccTrueIff
  {α}
  {xs : List α}
  {x : α}
  {n : Nat}
  {cond : α → Prop}
  (ha : cond x)
  [inst : DecidablePred cond]
  : exactlyN (x::xs) (n + 1) cond ↔ exactlyN xs n cond
  := by
  rw [exactlyN]
  simp [ha]

theorem exactlyNImpliesLeLength
  {α}
  {xs : List α}
  {n : Nat}
  {cond : α → Prop}
  [inst : DecidablePred cond]
  (h : exactlyN xs n cond)
  : n ≤ xs.length := by
  cases n with
    | zero => apply Nat.zero_le
    | succ n => induction xs with
      | nil => simp at h
      | cons x xs ih =>
        simp
        by_cases hx : cond x
        <;> simp [hx] at h
        · exact exactlyNImpliesLeLength h

        simp [h] at ih
        exact Nat.le_of_add_right_le ih

theorem exactlyNNonZeroImpliesExists
  {α}
  {xs : List α}
  {n : Nat}
  {cond : α → Prop}
  [inst : DecidablePred cond]
  (h : exactlyN xs (n + 1) cond)
  : ∃ x ∈ xs, cond x
  := by
    induction xs with
    | nil => trivial
    | cons p ps ih =>
      by_cases h₂ : cond p <;> simp [h₂]

      exact (exactlyNConsFalseIff h₂).mp h |> ih

def atMostN {α}
   (xs : List α)
   (n : Nat)
   (cond : α → Prop)
   [inst : DecidablePred cond] := match xs, n with
   | _, 0 => ¬ ∃ x ∈ xs, cond x
   | [], _ => True
   | x::xs', n => if cond x then
       atMostN xs' n.pred cond
     else
       atMostN xs' n cond

@[simp]
theorem atMostNConsFalse {α}
  {x₀ : α}
  {cond : α → Prop}
  (h₀ : ¬ cond x₀)
  (xs : List α)
  (n : Nat)
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
  {xs : List α}
  {n : Nat}
  [inst : DecidablePred cond]
  : atMostN (x₀ :: xs) (n + 1) cond ↔ (atMostN xs n cond) := by
  rw [atMostN.eq_def]

  cases n with
    | zero => simp [h₀]
    | succ n =>
      simp [h₀]

theorem atMostSuccN {α}
  {xs : List α}
  {cond : α → Prop}
  {n : Nat}
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
  (n : Nat)
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
