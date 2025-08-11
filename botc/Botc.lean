import Botc.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.ApplyAt

namespace Puzzle

section p51

def hasBoffin (ps : List Player) := ∃ p ∈ ps, p.role = .boffin ∧ ¬ p.droisoned

theorem hNoBoffinNotHasBoffin (players : List Player)
  (hNoBoffin : ¬ ∃ p ∈ players, p.role = .boffin)
  : (¬ hasBoffin players) := by
  rw [hasBoffin.eq_def]
  simp only [Bool.not_eq_true, not_exists, not_and, Bool.not_eq_false]
  induction players with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true]
  | cons p ps ih =>
    simp only [List.mem_cons, forall_eq_or_imp]
    simp only [List.mem_cons, exists_eq_or_imp, not_or, not_exists, not_and] at hNoBoffin
    have pNotBoffin := hNoBoffin.left
    simp only [pNotBoffin, false_implies, true_and]
    simp only [not_false_eq_true, true_and, pNotBoffin] at hNoBoffin

    by_contra h
    simp only [h, imp_false, not_exists, not_and, not_forall, Decidable.not_not, exists_prop] at ih
    contrapose ih
    simp only [not_exists, not_and]
    exact hNoBoffin

theorem minionRoles
  {mr : Role}
  (hmr : mr.class = .minion)
  : (∃ r ∈ [Role.poisoner, .boffin, .scarletwoman, .spy], r = mr) := by
  by_contra h
  simp at h
  rw [Role.class.eq_def] at hmr
  cases mr <;> simp only [reduceCtorEq] at hmr <;> simp at h

theorem roleEqImplClassEq₁ {r₁ r₂ : Role} (h : r₁ = r₂) : r₁.class = r₂.class := by
   cases r₁ <;> cases r₂ <;> simp only [Role.class, reduceCtorEq] <;> trivial

theorem implOfEq {α β} {p : α → β} {a b : α} (h : a = b) : (p a = p b) := by
   rw [h]

theorem existsImplOfEq {α β} {b : α} {p : α → Prop} {q : α → β} (h : ∃ a : α, p a ∧ (a = b)) :
  ∃ a : α, p a ∧ (q a = q b) := by

  cases h with
    | intro w h

  refine not_forall_not.mp ?x
  by_contra h₂
  have tmp := h₂ w
  simp [h.right] at tmp
  rw [h.right] at h
  have tmp₂ := h.left
  contradiction

theorem existsImplOfEq₂ {α β κ} {b : α} {p : κ → Prop} {q : α → β} {r : κ → α}
   (h : ∃ a : κ, p a ∧ (r a = b)) :
  ∃ a : κ, p a ∧ (q (r a) = q b) := by

  cases h with
    | intro w h

  refine not_forall_not.mp ?x
  by_contra h₂
  have tmp := h₂ w
  simp [h.right] at tmp
  rw [h.right] at h
  have tmp₂ := h.left
  contradiction


theorem roleInClassExistsImplClassExists
  {mr : Role}
  {players : List Player}
  (h : ∃ p ∈ players, p.role = mr)
  : ∃ p ∈ players, p.role.class = mr.class := by
  exact existsImplOfEq₂ h


theorem droisonedMeansDroisonedExists
  {p : Player}
  (players : List Player)
  (hPlayer : p ∈ players)
  (hPoisoned : p.droisoned)
  : ∃ p ∈ players, p.droisoned := by exists p

theorem classExclusivity
  {mr₁ mr₂ : Role}
  {c : Class}
  (players : List Player)
  (hClass : Player.exactlyOne players (fun p ↦ p.role.class = c))
  (m₁ : ∃ p ∈ players, p.role = mr₁)
  (m₂ : ∃ p ∈ players, p.role = mr₂)
  (hmr₁ : mr₁.class = c)
  (hmr₂ : mr₂.class = c)
  (hmrNe₁₂ : mr₁ ≠ mr₂)
  : False := by
  induction players with
    | nil => trivial
    | cons p ps ih =>


      rw [Player.exactlyOne.eq_def] at hClass
      simp at m₁ m₂ hClass

      have {droisoned, alignment, role} := p
      clear p

      simp at m₁ m₂ hClass

      have hNe₁ : role ≠ mr₁ := by
        by_contra hEq₁
        rw [hEq₁, hmr₁] at hClass
        rw [hEq₁] at m₂

        simp at hClass
        rw [Player.exactlyNone] at hClass
        simp only [hmrNe₁₂, false_or] at m₂
        have h := roleInClassExistsImplClassExists m₂
        rw [hmr₂] at h

        contradiction

      simp [hNe₁] at m₁

      have hNe₂ : role ≠ mr₂ := by
        by_contra hEq₂

        have h := roleInClassExistsImplClassExists m₁
        rw [hmr₁] at h

        rw [hEq₂, hmr₂] at hClass

        simp at hClass
        rw [Player.exactlyNone] at hClass
        contradiction

      simp [hNe₂] at m₂

      clear hNe₁ hNe₂

      have hNotClass : role.class ≠ c := by
        by_contra h

        simp [h] at hClass
        rw [Player.exactlyNone] at hClass
        have h := roleInClassExistsImplClassExists m₁
        rw [hmr₁] at h
        contradiction

      simp [hNotClass] at hClass
      exact ih hClass m₁ m₂

theorem allDefaultImplAlignmentEqDefaultAlignment
  {ps : List Player}
  (h : allDefaultAlignment ps)
  {p : Player}
  : p ∈ ps → (p.alignment = p.role.class.defaultAlignment)
  := by
    by_cases h₂:  p ∈ ps
    <;> simp [h₂]
    rw [allDefaultAlignment] at h

    have pDefaultAlignment : p.isDefaultAlignment := by
      exact h p h₂

    rw [Player.isDefaultAlignment, Role.defaultAlignment] at pDefaultAlignment
    rw [← pDefaultAlignment]

theorem allDefaultImplGoodIffDefaultGood
  {ps : List Player}
  (h : allDefaultAlignment ps)
  {p : Player}
  : p ∈ ps → (p.isGood ↔ p.role.class.defaultAlignment = .good)
  := by
    rw [Player.isGood]
    exact fun a ↦ Eq.congr (h p a) rfl

theorem allDefaultImplEvilIffDefaultEvil {ps : List Player}
  (h : allDefaultAlignment ps)
  {p : Player}
  : p ∈ ps → (p.isEvil ↔ p.role.class.defaultAlignment = .evil)
  := by
    rw [Player.isEvil]
    exact fun a ↦ Eq.congr (h p a) rfl


variable (you oscar sarah fraser dan hannah tim josh)
variable (players : List Player)

def allowedRoles : List Role := [
  .virgin,
  .noble,
  .artist,
  .slayer,
  .nightwatchman,
  .washerwoman,
  .golem,
  .recluse,
  .poisoner,
  .scarletwoman,
  .spy,
  .boffin,
  .kazali
]

def nobleAbility (p₁ p₂ p₃ : Player) :=
  let maxEvil := if ∃ p ∈ [p₁, p₂, p₃], p.role = .spy then 2 else 1
  let hEvil := atMostN [p₁, p₂, p₃] maxEvil Player.isEvil
  hEvil ∧ if ∃ p ∈ [p₁, p₂, p₃], p.role = .recluse then
    True
  else ∃ p ∈ [p₁, p₂, p₃], p.isEvil


-- oh gods is this terrifying
-- here's all the thingsd that can happen
-- 1. Noble can be poisoned
-- 2. Noble can get perfectly normal information (2 goods, 1 evil)
-- 3. Recluse can show up as evil despite being good (+1 good, -1 evil)
-- 4. Spy can show up as good despite being evil (+1 evil, -1 good)
-- this means anywhere from 0-2 players can be evil,
def nobleInfo (n p₁ p₂ p₃ : Player) := n.isGood → n.droisoned ∨ nobleAbility p₁ p₂ p₃

@[simp]
theorem nobleNotDroisoned (n p₁ p₂ p₃ : Player) (h : ¬ n.droisoned) :
  nobleInfo n p₁ p₂ p₃ ↔ n.isGood → nobleAbility p₁ p₂ p₃ := by
  rw [nobleInfo]
  simp only [h, Bool.false_eq_true, false_or]


theorem puzzle51
  (hPlayers : players = [you, oscar, sarah, fraser, dan, hannah, tim, josh])
  (hUnique : allUniqueRoles players)
  (hAllDefaultAlignment : allDefaultAlignment players)
  (hMinion : Player.exactlyOne players (fun p ↦ p.role.class = .minion))
  (hRoleRestriction : ∀ (p : Player), p ∈ players → p.role ∈ allowedRoles)
  -- if there's a poison cycle (a loop of players poisoning the next)
  -- they're all poisoned until the shortest duration ends
  (hPoisonSource : (∃ p ∈ players, p.droisoned) ↔ (∃ p ∈ players, p.role = .poisoner))
  (hMaxPoison : Player.atMostOne players (fun p ↦ p.droisoned))
  (hDemon : ∃ p ∈ players, p.role = .kazali)
  (hMaxDemon : Player.exactlyOne players (fun p ↦ p.role.class = .demon))

  (hDemonNotDroisoned : ∀ (p : Player), p ∈ players ∧ p.role.class = .demon → ¬p.droisoned)
  (hDemonNotDead : (¬ ∃ p ∈ players, p.role = .scarletwoman) →
    ¬ ∃ p ∈ [you, sarah, tim, hannah], p.role.class = .demon)
  -- the scarlet woman _really_ can't be dead, if she exists
  -- I'm not _100%_ this can't aopply to hannah,
  -- but in the context of a puzzle:
  --  I don't see why the demon would KYS with no minion ever.
  (hScarletwomanNotDead : ¬ ∃ p ∈ [you, sarah, tim, hannah], p.role = .scarletwoman)
  (hHannah : hannah.isGood ↔ hannah.role = .noble)
  (hHannahInfo : nobleInfo hannah sarah tim josh)
  (hTim : tim.isGood ↔ tim.role = .artist)
  (hTimInfo : tim.isGood → (¬josh.droisoned ∧ josh.role = .nightwatchman) ∨
     (josh.role.class = .demon ∧ hasBoffin players))
  (hTimInfo₂ : tim.isGood → tim.droisoned ∨ hannah.role ≠ .boffin)
  (hYou : you.isGood ↔ you.role = .washerwoman)
  (hYouInfo : you.isGood → you.droisoned ∨
    (Player.exactlyOne [hannah, tim] (fun p ↦ p.role = .artist)))
  (hOscar : oscar.isGood ↔ oscar.role = .slayer)
  (hOscarHasAbility : oscar.role = .slayer → ¬oscar.droisoned)
  (hOscarHasSlayerAbility : oscar.role = .slayer ∨ (oscar.role.class = .demon ∧ hasBoffin players))
  (hOscarInfo : sarah.diesToSlayerAbility)
  (hSarah : sarah.isGood ↔ (¬ sarah.droisoned ∧ sarah.role = .recluse))
  (hFraser : fraser.isGood ↔ fraser.role = .golem)
  (hFraserHasAbility : fraser.role = .golem → ¬fraser.droisoned)
  (hFraserHasGolemAbility : fraser.role = .golem ∨ (fraser.role.class = .demon ∧ hasBoffin players))
  (hTimFraser : tim.diesToGolemAbility)
  (hJosh : josh.isGood ↔ josh.role = .nightwatchman)
  -- if josh is evil, either there's a boffin, or tim is lying (and therefore evil).
  (hJoshTim : josh.isEvil ↔ ((josh.role.class = .demon ∧ hasBoffin players) ∨ tim.isEvil))
  (hDan : dan.isGood ↔ dan.role = .virgin)
  (hDanHasAbility : ¬ dan.droisoned)
  (hDanHasVirginAbility : dan.role = .virgin ∨ (dan.role.class = .demon ∧ hasBoffin players))
  (hDanInfo : you.diesToVirginAbility)
  : you.role = .washerwoman := by
  rw [Player.diesToSlayerAbility] at hOscarInfo
  rw [Player.diesToGolemAbility] at hTimFraser
  have hGoodIffDefaultGood := @allDefaultImplGoodIffDefaultGood players hAllDefaultAlignment
  have hHannahNotArtist : hannah.role ≠ .artist := by
    by_contra h
    have hannahGood : hannah.isGood := by
      rw [@hGoodIffDefaultGood hannah (by simp [hPlayers]), h, Role.class, Class.defaultAlignment]

    replace hHannah : hannah.role = .noble := by exact hHannah.mp hannahGood
    rw [hHannah] at h
    contradiction


  simp only [Player.exactlyOne, hHannahNotArtist, not_false_eq_true, ↓reduceIte, Player.exactlyNone,
    List.not_mem_nil, false_and, exists_false, ite_not, if_false_right, and_true] at hYouInfo

  have hNoPoisoner : ¬ ∃ p ∈ players, p.role = .poisoner := by
    by_contra hPoisoner
    have hPoisoned := hPoisonSource.mpr hPoisoner
    simp [Player.atMostOne, hPlayers, Player.exactlyOne, Player.exactlyNone] at hMaxPoison

    have hNoBoffin : ¬ ∃ p ∈ players, p.role = .boffin := by
      by_contra hExists

      exact classExclusivity
        players
        hMinion
        hPoisoner
        hExists
        (by decide)
        (by decide)
        (by decide)

    -- we already know there's no boffin
    clear hTimInfo₂
    have hNoBoffin₂ := by exact hNoBoffinNotHasBoffin players hNoBoffin
    simp only [Bool.not_eq_true, hNoBoffin₂, and_false, or_false,
      false_or]
      at hTimInfo hOscarHasAbility hOscarHasSlayerAbility hFraserHasAbility
        hFraserHasGolemAbility hJoshTim hDanHasAbility hDanHasVirginAbility

    have hNoSpy : ¬ ∃ p ∈ players, p.role = .spy := by
      by_contra hExists

      exact classExclusivity
        players
        hMinion
        hPoisoner
        hExists
        (by decide)
        (by decide)
        (by decide)

    have hNoScarletwoman : ¬ ∃ p ∈ players, p.role = .scarletwoman := by
      by_contra hExists

      exact classExclusivity
        players
        hMinion
        hPoisoner
        hExists
        (by decide)
        (by decide)
        (by decide)

    clear hScarletwomanNotDead
    replace hDemonNotDead := by exact hDemonNotDead hNoScarletwoman

    rw [Player.diesToVirginAbility] at hDanInfo

    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, reduceCtorEq,
      exists_eq_left, false_or, not_or, hPlayers, hOscarHasSlayerAbility, hFraserHasGolemAbility,
      hDanHasVirginAbility] at hNoBoffin hNoSpy

    replace hDan := hDanHasVirginAbility
    replace hOscar := hOscarHasSlayerAbility
    replace hFraser := hFraserHasGolemAbility
    clear hDanHasVirginAbility hOscarHasSlayerAbility hFraserHasGolemAbility
    simp only [hOscar, forall_const] at hOscarHasAbility
    simp only [hFraser, forall_const] at hFraserHasAbility

    replace hDanInfo : you.role.class = .townsfolk := by
      simp [hNoSpy] at hDanInfo
      exact hDanInfo

    replace hDanInfo : you.isGood := by
      rw [Player.isGood]
      rw [allDefaultAlignment] at hAllDefaultAlignment
      rw [hAllDefaultAlignment, Role.defaultAlignment, hDanInfo]
      decide
      rw [hPlayers]
      simp only [List.mem_cons, List.not_mem_nil, or_false, true_or]

    replace hYou : you.role = .washerwoman := by exact hYou.mp hDanInfo
    replace hYouInfo := by exact hYouInfo hDanInfo

    simp [hPlayers, hYou, hDan, hOscar, hFraser] at hPoisoner

    have hSarahNotDemon : sarah.role.class ≠ .demon := by
      by_contra h
      simp [h] at hDemonNotDead

    simp [hSarahNotDemon] at hOscarInfo
    replace hSarah := hOscarInfo.left


    simp only [hPlayers, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      hOscarHasAbility, Bool.false_eq_true, hOscarInfo.right, hFraserHasAbility, hDanHasAbility,
      exists_eq_left, false_or] at hPoisoned

    simp [hOscarHasAbility, hOscarInfo.right, hFraserHasAbility, hDanHasAbility] at hMaxPoison

    clear hOscarHasAbility hFraserHasAbility hDanHasAbility

    simp only [reduceCtorEq, not_false_eq_true, true_and, hYou, hOscarInfo] at hNoBoffin hNoSpy
    have hHannahNotDroisoned : ¬hannah.droisoned := by
      by_contra h

      simp only [h, Bool.true_eq_false, false_and, and_false, ↓reduceIte, if_false_left,
        Bool.not_eq_true, false_or] at hMaxPoison

      clear hHannahInfo
      clear hDanInfo

      simp only [hMaxPoison.left, Bool.false_eq_true, false_or] at hYouInfo

      clear hHannahNotArtist

      replace hYouInfo : tim.isGood := by
        rw [allDefaultAlignment] at hAllDefaultAlignment
        rw [Player.isGood, hAllDefaultAlignment, Role.defaultAlignment, hYouInfo]
        decide
        rw [hPlayers]
        simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]

      replace hTim := hTim.mp hYouInfo
      replace hTimInfo := (hTimInfo hYouInfo).right
      replace hJosh := hTimInfo

      replace hOscarInfo : sarah.role = .recluse := by
        by_contra h
        simp [h] at hOscarInfo

      replace hSarah := hOscarInfo

      clear hYouInfo hTimFraser hJoshTim hOscarInfo hSarahNotDemon
      simp only [hSarah, reduceCtorEq, hTim, hJosh, or_self, or_false, false_or] at hPoisoner
      simp only [hPlayers, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, hYou,
        reduceCtorEq, hOscar, hSarah, hFraser, hDan, hPoisoner, hTim, exists_eq_left, hJosh,
        or_self] at hDemon

    rw [nobleInfo, nobleAbility] at hHannahInfo

    simp only [hHannahNotDroisoned, Bool.false_eq_true, List.mem_cons, List.not_mem_nil, or_false,
      exists_eq_or_imp, hSarah, reduceCtorEq, hNoSpy, exists_eq_left, or_self, ↓reduceIte, true_or,
      and_true, false_or] at hHannahInfo



    simp only [hHannahNotDroisoned, Bool.false_eq_true, false_or, true_and,
      ↓reduceIte] at hPoisoned hMaxPoison


    have hSarahGood : sarah.isGood := by
      rw [Player.isGood]
      simp [hPlayers, Player.isDefaultAlignment, allDefaultAlignment] at hAllDefaultAlignment
      simp [hSarah, hAllDefaultAlignment, Role.defaultAlignment, Role.class, Class.defaultAlignment]

    have hJoshAndTimGood : josh.isGood ∧ tim.isGood := by
      by_contra h
      by_cases h₂ : josh.isGood
      simp [h₂] at h
      simp [Player.isGoodIffnIsEvil] at h
      have tmp := hJoshTim.mpr h
      simp [Player.isGoodIffnIsEvil] at h₂
      contradiction
      simp [Player.isGoodIffnIsEvil] at h₂
      have tmp := hJoshTim.mp h₂
      clear h hMaxPoison hPoisoned hSarahNotDemon hYouInfo

      have hHannahEvil : hannah.isEvil := by
        by_contra h
        simp [← Player.isGoodIffnIsEvil] at h
        simp [Player.isGoodIffnIsEvil] at hSarahGood
        have h₃ := hHannahInfo h
        simp [atMostN, hSarahGood] at h₃
        simp [h₂] at h₃

      rw [allDefaultAlignment] at hAllDefaultAlignment
      simp [hPlayers] at hAllDefaultAlignment

      have hTimJoshDefaultAlignment : tim.isDefaultAlignment ∧ josh.isDefaultAlignment := by
        exact hAllDefaultAlignment.right.right.right.right.right.right


      repeat rewrite [Player.isDefaultAlignment] at hTimJoshDefaultAlignment

      have timMinion : tim.role.class = .minion := by
        replace tmp : tim.role.defaultAlignment = .evil := by
          rw [Player.isEvil, hTimJoshDefaultAlignment.left] at tmp
          exact tmp

        cases tim with
          | mk tDroisoned tAlign tRole

        simp
        simp [Role.defaultAlignment, Role.class] at tmp

        cases tRole
        <;> simp [Role.class]
        <;> simp [Class.defaultAlignment] at tmp

        simp [Role.class] at hTimFraser


      have timPoisoner : tim.role = .poisoner := by
        by_contra h

        cases tim with
          | mk tDroisoned tAlign tRole

        cases tRole
        <;> simp [Role.class] at hTimFraser
        <;> simp at hNoSpy hNoBoffin
        <;> (try contradiction)
        simp [hPlayers] at hNoScarletwoman

      simp [hPlayers, timMinion, Player.exactlyOne, Player.exactlyNone] at hMinion

      have joshDemon : josh.role.class = .demon := by
        -- no minion slot left
        replace h₂ : josh.role.defaultAlignment = .evil := by
          rw [Player.isEvil, hTimJoshDefaultAlignment.right] at h₂
          exact h₂
        by_contra h

        cases josh with
          | mk jDroisoned jAlign jRole

        simp at h

        cases jRole
        <;> simp [Role.defaultAlignment, Role.class, Class.defaultAlignment] at h₂
        <;> simp [Role.class] at hMinion
        simp [Role.class] at h


      simp [hPlayers, joshDemon, Player.exactlyOne, Player.exactlyNone] at hMaxDemon

      have hannahDemonOrMinion : hannah.role.class = .minion ∨ hannah.role.class = .demon := by
        -- evil and default alignment
        have hHannahDefaultAlignment := hAllDefaultAlignment.right.right.right.right.right.left
        replace hHannahEvil : hannah.role.defaultAlignment = .evil := by
          rw [Player.isEvil, hHannahDefaultAlignment] at hHannahEvil
          exact hHannahEvil

        cases hannah with
          | mk hDroisoned hAlign hRole

        simp [Role.class]
        cases hRole
        <;> simp
        <;> simp [Role.defaultAlignment, Role.class, Class.defaultAlignment] at hHannahEvil

      contrapose! hannahDemonOrMinion
      simp

      exact ⟨
        hMinion.right.right.right.right.right.left,
        hMaxDemon.right.right.right.right.right.left
      ⟩

    replace hJosh := hJosh.mp hJoshAndTimGood.left
    replace hTim := hTim.mp hJoshAndTimGood.right

    simp [hSarah, hJosh, hTim] at hPoisoner
    replace hHannah := hPoisoner
    clear hPoisoner

    simp [hPlayers] at hDemon

    simp [hYou, hOscar, hSarah, hFraser, hDan, hHannah, hTim, hJosh] at hDemon

  simp [hNoPoisoner] at hPoisonSource
  simp [hPlayers] at hPoisonSource

  simp [hPoisonSource]
    at hHannahInfo hTimInfo hTimInfo₂ hOscarInfo
      hYouInfo hSarah hDanHasAbility hOscarHasAbility hFraserHasAbility

  clear hDanHasAbility hOscarHasAbility hFraserHasAbility hMaxPoison




  -- prove no scarletwoman next
  have hNoScarletwoman : ¬∃ p ∈ players, p.role = .scarletwoman := by
    by_contra hScarletwoman


    have hNoBoffin : ¬ ∃ p ∈ players, p.role = .boffin := by
      by_contra hExists

      exact classExclusivity
        players
        hMinion
        hScarletwoman
        hExists
        (by decide)
        (by decide)
        (by decide)

    -- we already know there's no boffin
    clear hTimInfo₂
    have hNoBoffin₂ := by exact hNoBoffinNotHasBoffin players hNoBoffin
    simp only [hNoBoffin₂, and_false, or_false, false_or]
      at hTimInfo hOscarHasSlayerAbility
        hFraserHasGolemAbility hJoshTim  hDanHasVirginAbility

    have hNoSpy : ¬ ∃ p ∈ players, p.role = .spy := by
      by_contra hExists

      exact classExclusivity
        players
        hMinion
        hScarletwoman
        hExists
        (by decide)
        (by decide)
        (by decide)


    rw [Player.diesToVirginAbility] at hDanInfo

    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, reduceCtorEq,
      exists_eq_left, false_or, not_or, hPlayers, hOscarHasSlayerAbility, hFraserHasGolemAbility,
      hDanHasVirginAbility] at hNoBoffin hNoSpy

    replace hDan := hDanHasVirginAbility
    replace hOscar := hOscarHasSlayerAbility
    replace hFraser := hFraserHasGolemAbility
    clear hDanHasVirginAbility hOscarHasSlayerAbility hFraserHasGolemAbility

    replace hDanInfo : you.role.class = .townsfolk := by
      simp [hNoSpy] at hDanInfo
      exact hDanInfo

    replace hDanInfo : you.isGood := by
      rw [Player.isGood]
      rw [allDefaultAlignment] at hAllDefaultAlignment
      rw [hAllDefaultAlignment, Role.defaultAlignment, hDanInfo]
      decide
      rw [hPlayers]
      simp only [List.mem_cons, List.not_mem_nil, or_false, true_or]

    replace hYou : you.role = .washerwoman := by exact hYou.mp hDanInfo
    replace hYouInfo := by exact hYouInfo hDanInfo

    replace hJosh : josh.role = .nightwatchman := by
      simp [hYouInfo] at hTim
      rw [Player.isGoodIffnIsEvil] at hTim
      simp [hTim] at  hJoshTim
      rw [← Player.isGoodIffnIsEvil] at hJoshTim
      exact hJosh.mp hJoshTim

    simp [hPlayers, hYou, hYouInfo, hDan, hOscar, hFraser, hJosh] at hScarletwoman
    simp at hScarletwomanNotDead
    simp [hScarletwomanNotDead] at hScarletwoman

  simp [hNoScarletwoman] at hDemonNotDead
  simp [hDemonNotDead] at hOscarInfo
  replace hSarah := hOscarInfo
  clear hOscarInfo hScarletwomanNotDead

  sorry


end   p51

end   Puzzle
