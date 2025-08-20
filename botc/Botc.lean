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
  simp at hNoBoffin
  simp
  intro p inPs hBoffin
  have hNotBoffin := hNoBoffin p inPs
  contradiction

theorem simpBoffinNoPoison
  {players : List Player}
  (hNoPoison : ¬ ∃ p ∈ players, p.droisoned)
  (hHasBoffin : ∃ p ∈ players, p.role = .boffin)
  : hasBoffin players
  := by
  rw [hasBoffin.eq_def]

  induction players with
  | nil => simp at hHasBoffin
  | cons p ps ih =>
    simp
    simp at hHasBoffin
    simp only [List.mem_cons, exists_eq_or_imp, not_or, Bool.not_eq_true] at hNoPoison
    by_cases h :  p.role = .boffin
    · left
      exact ⟨h, hNoPoison.left⟩



    simp only [h, false_and, false_or]
    simp only [h, false_or] at hHasBoffin

    simp only [Bool.not_eq_true] at ih

    exact ih hNoPoison.right hHasBoffin

theorem roleEqImplClassEq₁ {r₁ r₂ : Role} (h : r₁ = r₂) : r₁.class = r₂.class := by
  congr

theorem implOfEq {α β} {p : α → β} {a b : α} (h : a = b) : (p a = p b) := by
  congr

theorem existsImplOfEq₂ {α β κ} {b : α} {p : κ → Prop} {q : α → β} {r : κ → α}
   (h : ∃ a : κ, p a ∧ (r a = b)) :
  ∃ a : κ, p a ∧ (q (r a) = q b) := by

  let ⟨w, h⟩ := h

  exists w
  constructor
  · exact h.left
  congr
  exact h.right


theorem existsImplOfEq {α β} {b : α} {p : α → Prop} {q : α → β} (h : ∃ a : α, p a ∧ (a = b)) :
  ∃ a : α, p a ∧ (q a = q b) := by
  exact existsImplOfEq₂ h

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

theorem forallNotImp {α} {p q : α → Prop} :
  (∀ (x : α), p x → ¬ q x) ↔ ¬ ∃ x, p x ∧ q x := by simp

theorem classExclusivity
  {mr₁ mr₂ : Role}
  {c : Class}
  {players : List Player}
  (hClass : exactlyN players 1 (fun p ↦ p.role.class = c))
  (m₁ : ∃ p ∈ players, p.role = mr₁)
  (m₂ : ∃ p ∈ players, p.role = mr₂)
  (hmr₁ : mr₁.class = c)
  (hmr₂ : mr₂.class = c)
  (hmrNe₁₂ : mr₁ ≠ mr₂)
  : False := by
  induction players with
    | nil => trivial
    | cons p ps ih =>


      rw [exactlyN.eq_def] at hClass
      simp at m₁ m₂ hClass

      have {droisoned, alignment, role} := p
      clear p

      simp at m₁ m₂ hClass

      have hNe₁ : role ≠ mr₁ := by
        by_contra hEq₁
        rw [hEq₁, hmr₁] at hClass
        rw [hEq₁] at m₂


        simp only [hmrNe₁₂, false_or] at m₂
        have h := roleInClassExistsImplClassExists m₂
        rw [hmr₂] at h
        simp at hClass
        rw [forallNotImp] at hClass
        contradiction

      simp [hNe₁] at m₁

      have hNe₂ : role ≠ mr₂ := by
        by_contra hEq₂

        have h := roleInClassExistsImplClassExists m₁
        rw [hmr₁] at h

        rw [hEq₂, hmr₂] at hClass

        simp at hClass
        rw [forallNotImp] at hClass
        contradiction

      simp [hNe₂] at m₂

      clear hNe₁ hNe₂

      have hNotClass : role.class ≠ c := by
        by_contra h

        simp [h] at hClass
        have h := roleInClassExistsImplClassExists m₁
        rw [hmr₁] at h
        rw [forallNotImp] at hClass
        contradiction


      simp [hNotClass] at hClass
      exact ih hClass m₁ m₂

theorem classIffRole
  {p : Player}
  {r : Role}
  {players : List Player}
  (hRole : ∃ p ∈ players, p.role = r)
  (hMaxClass : exactlyN players 1 (fun p ↦ p.role.class = r.class))
  (hInPlayers : p ∈ players)
  (hUnique : allUniqueRoles players)
  : p.role.class = r.class ↔ p.role = r
  := by

  induction players with
    | nil => simp at hInPlayers
    | cons p' ps ih =>
      simp at hInPlayers
      simp at hRole
      rw [allUniqueRoles, List.pairwise_cons] at hUnique

      by_cases hp' : p'.role.class = r.class
      · simp only [exactlyN, hp', not_true_eq_false, ↓reduceIte, gt_iff_lt, Nat.lt_add_one,
        Nat.pred_eq_sub_one, Nat.sub_self, exactlyNZeroIff] at hMaxClass
        rw [forallNotImp] at hMaxClass

        by_cases hpp' : p = p'
        · rw [hpp', hp']
          simp

          clear hInPlayers

          by_contra hpnr

          simp [hpnr] at hRole
          have hDemonExists := roleInClassExistsImplClassExists hRole
          contradiction

        simp [hpp'] at hInPlayers

        have tmp := hUnique.left p hInPlayers

        have hpNotDemon : ¬p.role.class = r.class := by
          contrapose! hMaxClass
          exists p

        simp [hpNotDemon]

        by_cases hp'r : p'.role = r
        · rw [hp'r, ne_eq, eq_comm] at tmp
          trivial

        simp [hp'r] at hRole
        have hRoleExists := roleInClassExistsImplClassExists hRole
        contradiction

      simp [exactlyN, hp'] at hMaxClass

      have tmp := hUnique.left p

      have p'rolener : p'.role ≠ r := by
        by_contra p'roleEqr
        simp [p'roleEqr] at hp'

      simp [p'rolener] at hRole


      by_cases hpp' : p = p'
      · repeat rw [hpp']
        simp [p'rolener]
        exact hp'

      simp [hpp'] at hInPlayers
      simp [hInPlayers] at tmp
      exact ih hRole hMaxClass hInPlayers hUnique.right

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

def allowedGoodRoles : List Role := [
  .virgin,
  .noble,
  .artist,
  .slayer,
  .nightwatchman,
  .washerwoman,
  .golem,
  .recluse,
]

def allowedEvilRoles : List Role := [
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

def washerwomanAbility (p₁ p₂ : Player) (r : Role) :=
  let cond := fun p ↦ p.role = r
  if ∃ p ∈ [p₁, p₂], p.role = .spy then
    atMostN [p₁, p₂] 1 cond
  else
    exactlyN [p₁, p₂] 1 cond

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

@[simp]
theorem elimRoleCons
  {players : List Player}
  {x : Role}
  {xs : List Role}
  {hp : Player → Prop}
  (h : ¬ ∃ p ∈ players, p.role = x) :
  (∀ (p : Player), p ∈ players → (hp p ↔ p.role ∈ x::xs)) ↔
  (∀ (p : Player), p ∈ players → (hp p ↔ p.role ∈ xs)) := by
  simp at h
  conv =>
    lhs
    intro p inPs
    simp [h p inPs]

@[simp]
theorem elimRoleAppend
  {players : List Player}
  {x : Role}
  {xs₁ xs₂ : List Role}
  {hp : Player → Prop}
  (h : ¬ ∃ p ∈ players, p.role = x) :
  (∀ (p : Player), p ∈ players → (hp p ↔ p.role ∈  (xs₁ ++ x::xs₂))) ↔
  (∀ (p : Player), p ∈ players → (hp p ↔ p.role ∈ (xs₁ ++ xs₂))) := by
  simp at h
  simp
  conv =>
    lhs
    intro p inPs
    simp [h p inPs]


theorem puzzle51
  (hPlayers : players = [you, oscar, sarah, fraser, dan, hannah, tim, josh])
  (hUnique : allUniqueRoles players)
  (hAllDefaultAlignment : allDefaultAlignment players)
  (hMinion : exactlyN players 1 (fun p ↦ p.role.class = .minion))
  (hGoodRoles : ∀ (p : Player), p ∈ players → (p.isGood ↔ p.role ∈ allowedGoodRoles))
  (hEvilRoles : ∀ (p : Player), p ∈ players → (p.isEvil ↔ p.role ∈ allowedEvilRoles))
  -- if there's a poison cycle (a loop of players poisoning the next)
  -- they're all poisoned until the shortest duration ends
  (hPoisonSource : (∃ p ∈ players, p.droisoned) ↔ (∃ p ∈ players, p.role = .poisoner))
  (hMaxPoison : atMostN players 1 (fun p ↦ p.droisoned))
  (hDemon : ∃ p ∈ players, p.role = .kazali)
  (hMaxDemon : exactlyN players 1 (fun p ↦ p.role.class = .demon))

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
  (hYouInfo : you.isGood → you.droisoned ∨ washerwomanAbility hannah tim .artist)
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
  : [dan.role, hannah.role, tim.role, josh.role, you.role, oscar.role, sarah.role, fraser.role]
  = [.virgin, .noble, .spy, .kazali, .washerwoman, .slayer, .recluse, .golem]
  := by
  rw [Player.diesToSlayerAbility] at hOscarInfo
  rw [Player.diesToGolemAbility] at hTimFraser
  have hGoodIffDefaultGood := @allDefaultImplGoodIffDefaultGood players hAllDefaultAlignment
  have hEvilIffDefaultEvil := @allDefaultImplEvilIffDefaultEvil players hAllDefaultAlignment
  rw [allowedEvilRoles] at hEvilRoles
  have demonIffRole : ∀ (p : Player), p ∈ players → (p.role.class = .demon ↔ p.role = .kazali) := by
    intro p h
    exact (classIffRole hDemon hMaxDemon h hUnique)

  have hYouGood : you.role ≠ .spy → you.isGood := by
    intro h

    simp only [Player.diesToVirginAbility, h, Bool.not_eq_true, false_and, or_false] at hDanInfo

    rw [@hGoodIffDefaultGood you (by simp [hPlayers]), hDanInfo, Class.defaultAlignment]

  -- this is technically lossy, but in practice it's better.
  clear hDanInfo

  have hHannahNotArtist : hannah.role ≠ .artist := by
    by_contra h
    have hannahGood : hannah.isGood := by
      rw [@hGoodIffDefaultGood hannah (by simp [hPlayers]), h, Role.class, Class.defaultAlignment]

    rw [hHannah.mp hannahGood] at h
    contradiction


  simp  [washerwomanAbility, exactlyN, atMostN, hHannahNotArtist] at hYouInfo

  clear hHannahNotArtist


  have hNoPoisoner : ¬ ∃ p ∈ players, p.role = .poisoner := by
    by_contra hPoisoner
    have hPoisoned := hPoisonSource.mpr hPoisoner
    simp [atMostN, hPlayers] at hMaxPoison

    have hPoisonerMinion :
      ∀ p : Player, p ∈ players → (p.role.class = .minion ↔ p.role = .poisoner) := by
      intro p h
      exact (classIffRole hPoisoner hMinion h hUnique)


    have hNoBoffin : ¬ ∃ p ∈ players, p.role = .boffin := by
      by_contra hExists

      exact classExclusivity
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
        hMinion
        hPoisoner
        hExists
        (by decide)
        (by decide)
        (by decide)

    have hNoScarletwoman : ¬ ∃ p ∈ players, p.role = .scarletwoman := by
      by_contra hExists

      exact classExclusivity
        hMinion
        hPoisoner
        hExists
        (by decide)
        (by decide)
        (by decide)

    clear hScarletwomanNotDead
    replace hDemonNotDead := by exact hDemonNotDead hNoScarletwoman
    simp at hDemonNotDead
    -- simp [hDemonNotDead] at *

    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, reduceCtorEq,
      exists_eq_left, false_or, not_or, hPlayers, hOscarHasSlayerAbility, hFraserHasGolemAbility,
      hDanHasVirginAbility] at hNoBoffin hNoSpy

    replace hDan := hDanHasVirginAbility
    replace hOscar := hOscarHasSlayerAbility
    replace hFraser := hFraserHasGolemAbility
    clear hDanHasVirginAbility hOscarHasSlayerAbility hFraserHasGolemAbility
    simp only [hOscar, forall_const] at hOscarHasAbility
    simp only [hFraser, forall_const] at hFraserHasAbility
    simp [hNoSpy] at hYouGood

    replace hYou : you.role = .washerwoman := by exact hYou.mp hYouGood
    replace hYouInfo := by exact hYouInfo hYouGood

    clear hYouGood

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

      simp only [h, Bool.true_eq_false, false_and, ↓reduceIte, if_false_left,
        Bool.not_eq_true] at hMaxPoison

      clear hHannahInfo

      simp only [hMaxPoison.left, Bool.false_eq_true, false_or] at hYouInfo
      simp [hNoSpy] at hYouInfo

      replace hYouInfo : tim.isGood := by rw [
        @hGoodIffDefaultGood tim (by simp [hPlayers]),
        hYouInfo,
        Role.class,
        Class.defaultAlignment
      ]

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


    have hSarahGood : sarah.isGood := by rw [
      @hGoodIffDefaultGood sarah (by simp [hPlayers]),
      hSarah,
      Role.class,
      Class.defaultAlignment
    ]

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
        simp [h₂, tmp] at h₃

      rw [allDefaultAlignment] at hAllDefaultAlignment
      simp [hPlayers] at hAllDefaultAlignment

      have hTimJoshDefaultAlignment : tim.isDefaultAlignment ∧ josh.isDefaultAlignment := by
        exact hAllDefaultAlignment.right.right.right.right.right.right


      repeat rewrite [Player.isDefaultAlignment] at hTimJoshDefaultAlignment

      -- have timMinion : tim.role.class = .minion := by
      --   rw [Player.isEvil, hTimJoshDefaultAlignment.left] at tmp

      --   let ⟨_, _, tRole⟩ := tim

      --   simp
      --   simp [Role.defaultAlignment] at tmp

      --   cases tRole
      --   <;> simp [Role.class]
      --   <;> simp [Class.defaultAlignment] at tmp
      --   <;> simp at hTimFraser

      have timMinion : tim.role.class = .minion := by
        rw [Player.isEvil, hTimJoshDefaultAlignment.left, Role.defaultAlignment] at tmp
        simp [Class.evil] at tmp
        cases tmp with
          | inl h => trivial
          | inr h => contradiction

      have timPoisoner : tim.role = .poisoner := by
        exact (hPoisonerMinion tim (by simp [hPlayers])).mp timMinion

      simp [hPlayers, timMinion, exactlyN] at hMinion

        -- no minion slot left
      have joshDemon : josh.role.class = .demon := by
        rw [Player.isEvil, hTimJoshDefaultAlignment.right, Role.defaultAlignment] at h₂
        simp [Class.evil] at h₂
        cases h₂ with
          | inl h => rw [h] at hMinion; simp at hMinion
          | inr h => trivial

      simp [hPlayers, joshDemon, exactlyN] at hMaxDemon

      have hannahDemonOrMinion : hannah.role.class = .minion ∨ hannah.role.class = .demon := by
        -- evil and default alignment
        have hHannahDefaultAlignment := hAllDefaultAlignment.right.right.right.right.right.left
        rw [Player.isEvil, hHannahDefaultAlignment, Role.defaultAlignment] at hHannahEvil
        simp [Class.evil] at hHannahEvil
        trivial



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

  rw [elimRoleCons hNoPoisoner] at hEvilRoles
  have hNoPoison := hPoisonSource.not.mpr hNoPoisoner

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
        hMinion
        hScarletwoman
        hExists
        (by decide)
        (by decide)
        (by decide)

    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, reduceCtorEq,
      exists_eq_left, false_or, not_or, hPlayers, hOscarHasSlayerAbility, hFraserHasGolemAbility,
      hDanHasVirginAbility] at hNoBoffin hNoSpy

    replace hDan := hDanHasVirginAbility
    replace hOscar := hOscarHasSlayerAbility
    replace hFraser := hFraserHasGolemAbility
    clear hDanHasVirginAbility hOscarHasSlayerAbility hFraserHasGolemAbility

    simp [hNoSpy] at hYouGood

    replace hYou : you.role = .washerwoman := by exact hYou.mp hYouGood
    replace hYouInfo := by exact hYouInfo hYouGood

    replace hJosh : josh.role = .nightwatchman := by
      simp [hNoSpy] at hYouInfo
      simp [hYouInfo] at hTim
      rw [Player.isGoodIffnIsEvil] at hTim
      simp [hTim] at  hJoshTim
      rw [← Player.isGoodIffnIsEvil] at hJoshTim
      exact hJosh.mp hJoshTim

    simp [hPlayers, hYou, hDan, hOscar, hFraser, hJosh] at hScarletwoman
    simp at hScarletwomanNotDead
    simp [hScarletwomanNotDead] at hScarletwoman

  simp [hNoScarletwoman] at hDemonNotDead
  simp [hDemonNotDead] at hOscarInfo
  replace hSarah := hOscarInfo
  have hSarahGood : sarah.isGood := by
   have tmp := (@hGoodIffDefaultGood sarah)
   rw [hSarah, Role.class, Class.defaultAlignment] at tmp
   simp [hPlayers] at tmp
   exact tmp

  have hSarahNotEvil : ¬sarah.isEvil := by exact (sarah.isGoodIffnIsEvil).mp hSarahGood

  clear hOscarInfo hScarletwomanNotDead
  rw [elimRoleCons hNoScarletwoman] at hEvilRoles

  -- prove no boffin to force there to be a spy
  -- boffin is the 2rd biggest source of information chaos (after pois)
  -- but scarlet woman is just so much easier to disprove
  -- that it's nice to get it out of the way first.
  have hNoBoffin : ¬∃ p ∈ players, p.role = .boffin := by
    by_contra hBoffin

    have hHasBoffin := by exact simpBoffinNoPoison hNoPoison hBoffin
    simp only [hHasBoffin, and_true]
      at hOscarHasSlayerAbility hFraserHasGolemAbility hJoshTim hDanHasVirginAbility
        hTimInfo

    rw [demonIffRole] at hDanHasVirginAbility hTimInfo hFraserHasGolemAbility hOscarHasSlayerAbility

    have hNoSpy : ¬ ∃ p ∈ players, p.role = .spy := by
      by_contra hExists

      exact classExclusivity
        hMinion
        hBoffin
        hExists
        (by decide)
        (by decide)
        (by decide)

    rw [elimRoleCons hNoSpy] at hEvilRoles
    simp at hEvilRoles

    rw [nobleAbility] at hHannahInfo

    have hNoSpySubset : ¬ ∃ p ∈ [sarah, tim, josh], p.role = .spy := by
      simp [hPlayers] at hNoSpy
      simp [hNoSpy]

    simp only [hNoSpySubset] at hHannahInfo
    clear hNoSpySubset
    simp [atMostN, hSarahNotEvil, hSarah] at hHannahInfo

    simp only [hPlayers, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, not_or] at hNoSpy

    simp [hNoSpy] at hYouGood
    replace hYou : you.role = .washerwoman := by exact hYou.mp hYouGood
    replace hYouInfo := by exact hYouInfo hYouGood
    simp [hNoSpy] at hYouInfo

    rewrite [hYouInfo, eq_self, iff_true] at hTim


    have hTimNotEvil : ¬tim.isEvil := tim.isGoodIffnIsEvil.mp hTim

    simp [hTimNotEvil] at hHannahInfo
    simp [hTimNotEvil] at hJoshTim

    replace hTimInfo := hTimInfo hTim
    replace hTimInfo₂ := hTimInfo₂ hTim

    simp [hPlayers, hYou, hTimInfo₂] at hBoffin

    -- fixme: this is so easy to improve, just do better
    have easyNonBoffins : ¬ ∃ p ∈ [oscar, fraser, dan, josh], p.role = .boffin := by
      simp
      constructor
      by_contra h
      simp [h] at hOscarHasSlayerAbility
      constructor
      by_contra h
      simp [h] at hFraserHasGolemAbility
      constructor <;> by_contra h
      simp [h] at hDanHasVirginAbility
      simp [h] at hTimInfo

    simp at easyNonBoffins
    simp [easyNonBoffins, hSarah, hYouInfo] at hBoffin

    all_goals simp [hPlayers]

  have hNoBoffin₂ := by exact hNoBoffinNotHasBoffin players hNoBoffin
  simp only [hNoBoffin₂, and_false, or_false, false_or]
    at hTimInfo hOscarHasSlayerAbility
      hFraserHasGolemAbility hJoshTim  hDanHasVirginAbility

  simp [hDanHasVirginAbility] at hDan
  simp [hOscarHasSlayerAbility] at hOscar
  simp [hFraserHasGolemAbility] at hFraser

  simp [nobleAbility, hSarah] at hHannahInfo

  conv at hEvilRoles =>
    right
    right
    right
    left
    rw [←List.singleton_append]

  rw [elimRoleAppend hNoBoffin] at hEvilRoles
  simp only [List.singleton_append] at hEvilRoles

  have hMinionSpy : ∀ (p : Player), p ∈ players → (p.role.class = .minion ↔ p.role = Role.spy) := by
    intro p inPs
    constructor
    · intro hMinion
      have hPEvil : p.isEvil := by
        rw [hEvilIffDefaultEvil inPs]
        simp [Class.evil]
        left
        exact hMinion
      have pRoles := (hEvilRoles p inPs).mp hPEvil
      simp at pRoles
      cases pRoles with
        | inl h =>
          trivial
        | inr h =>
          rw [h, Role.class] at hMinion
          contradiction
    intro role
    rw [role]
    decide

  have hSpy : ∃ p ∈
  players, p.role = .spy := by
    -- exhaustive proof:
    -- no other minion role exists but there is a minion

    have hMinionExists : ∃ p ∈ players, p.role.class = .minion :=
      exactlyNNonZeroImpliesExists hMinion

    have pExists := hMinionExists.choose_spec

    have hSpy := (hMinionSpy hMinionExists.choose pExists.left).mp pExists.right

    exists hMinionExists.choose
    exact ⟨pExists.left, hSpy⟩

  have hHannahNotSpy : ¬hannah.role = .spy := by
    by_contra hHannahSpy

    have hOnlySpy : ¬ ∃ p ∈ [you, oscar, sarah, fraser, dan, tim, josh], p.role = .spy := by
      -- all unique roles, it can't be anybody else
      rw [allUniqueRoles, hPlayers] at hUnique
      simp at hUnique
      repeat rw [hHannahSpy] at hUnique
      simp
      simp [Eq.comm] at hUnique
      simp [Eq.comm, hUnique]

    simp at hOnlySpy
    simp [hOnlySpy] at hYouGood
    replace hYou := hYou.mp hYouGood
    clear hYouInfo


    have hannahMinion : hannah.role.class = .minion := by
      simp [hHannahSpy]
      decide


    simp [exactlyN, hannahMinion, hPlayers] at hMinion

    have hTimGood : tim.isGood := by
      rw [tim.isGoodIffnIsEvil]
      rw [hEvilIffDefaultEvil (by simp [hPlayers])]
      simp [Class.evil]
      exact ⟨hMinion.right.right.right.right.right.left, hTimFraser⟩

    replace hTim := hTim.mp hTimGood
    have hJoshGood := josh.isGoodIffnIsEvil.mpr
      (hJoshTim.not.mpr (tim.isGoodIffnIsEvil.mp hTimGood))

    simp [hJoshGood] at hJosh

    simp only [hPlayers, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, hYou,
      reduceCtorEq, hOscarHasSlayerAbility, hSarah, hFraserHasGolemAbility, hDanHasVirginAbility,
      hHannahSpy, hTim, exists_eq_left, hJosh, or_self] at hDemon

  have hHannahGood : hannah.isGood := by
    rw [hannah.isGoodIffnIsEvil]
    rw [hEvilIffDefaultEvil (by simp [hPlayers])]
    simp [Class.evil]
    constructor
    · exact (hMinionSpy hannah (by simp [hPlayers])).not.mpr hHannahNotSpy
    exact hDemonNotDead.right.right.right

  simp [hHannahGood] at hHannah hHannahInfo
  -- simp [atMostN] at hHannahInfo

  have hYouNotSpy : you.role ≠ .spy := by
    by_contra hYouSpy

    have hOnlySpy : ¬ ∃ p ∈ [hannah, oscar, sarah, fraser, dan, tim, josh], p.role = .spy := by
      -- all unique roles, it can't be anybody else
      rw [allUniqueRoles, hPlayers] at hUnique
      simp at hUnique
      repeat rw [hYouSpy] at hUnique
      simp
      simp [Eq.comm, hUnique]

    simp at hOnlySpy
    simp [hOnlySpy, atMostN, hSarahNotEvil] at hHannahInfo
    simp [hJoshTim] at hHannahInfo
    simp [hHannahInfo] at hJoshTim

    have hTimGood : tim.isGood := tim.isGoodIffnIsEvil.mpr hHannahInfo
    have hJoshGood : josh.isGood := josh.isGoodIffnIsEvil.mpr hJoshTim

    simp [hJoshGood] at hJosh
    simp [hTimGood] at hTim

    simp only [hPlayers, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, hYouSpy,
      reduceCtorEq, hOscarHasSlayerAbility, hSarah, hFraserHasGolemAbility, hDanHasVirginAbility,
      hHannah, hTim, exists_eq_left, hJosh, or_self] at hDemon

  simp [hYouNotSpy] at hYouGood
  simp [hYouGood] at hYou

  simp [hPlayers] at hSpy
  simp only [hYou, reduceCtorEq, hOscarHasSlayerAbility, hSarah, hFraserHasGolemAbility,
    hDanHasVirginAbility, hHannah, false_or] at hSpy

  simp [hSpy, atMostN, hSarahNotEvil] at hHannahInfo
  clear hHannahInfo

  have hTimSpy : tim.role = .spy := by
    by_contra hTimNotSpy
    simp [hTimNotSpy] at hSpy
    simp only [hPlayers, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, hYou,
      reduceCtorEq, hOscarHasSlayerAbility, hSarah, hFraserHasGolemAbility, hDanHasVirginAbility,
      hHannah, hSpy, exists_eq_left, false_or] at hDemon

    simp [hDemon, Role.class] at hTimFraser

  simp only [hPlayers, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, hYou,
    reduceCtorEq, hOscarHasSlayerAbility, hSarah, hFraserHasGolemAbility, hDanHasVirginAbility,
    hHannah, hTimSpy, exists_eq_left, false_or] at hDemon

  simp only [hDanHasVirginAbility, hHannah, hTimSpy, hDemon, hYou, hOscarHasSlayerAbility, hSarah,
    hFraserHasGolemAbility]

end   p51

end   Puzzle
