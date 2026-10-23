/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/JointGuard.lean
  Garde conjointe (2026-10-10, D-39) — papier 11 : plusieurs plafonds. Plan et trace :
  `cache/garde_conjointe_2026-10-10/` ; lecture critique qui la demande :
  `cache/lecture_critique_stochastique_multifrontieres_2026-10-10/lecture_critique.md` §2.1.

  Module neuf (D-30) : aucun module existant n'est modifié. Il n'importe que `LocalTraceLang`,
  pour la primitive `PAut` : la couche III reste indépendante des couches I et II.

  Portée. Un vecteur de charges `L : B → M`, un plafond `cap c` pour chaque coordonnée `c` d'un
  ensemble fini `G` (les coordonnées plafonnées ; les autres ne sont pas contrôlées), une
  émission `e a : B → M` par lettre contrôlable `a`, ajoutée à toutes les coordonnées, et un top
  `tick` qui agit sur le vecteur. `M` n'a qu'une addition et une relation `≤`, sans axiome : cela
  couvre ℕ et tout corps ordonné (D-13).
  - `jointGuard` : admettre `a` ssi chaque plafond tient encore après l'émission ;
  - `jointGuard_safe` : la garde conjointe est sûre si le top garde chaque coordonnée plafonnée
    sous son plafond et si le départ est sous les plafonds ;
  - `jointGuard_maximal` : pour tout top, toute règle sûre atteint moins de vecteurs que la garde
    conjointe et n'autorise, sur ses états atteignables, que ce que la garde autorise.
  Ce n'est pas un théorème neuf : les preuves sont celles de `GuardSupervisor.guard_safe` et
  `GuardSupervisor.guard_maximal` (une charge dans ℕ), coordonnée par coordonnée. Rien ici sur
  les lettres incontrôlables (réserve conjointe) ni sur l'atteignabilité par les mots (pas de
  version de `reach_iff_run`).
  Les `example` de la fin sont des témoins de non-vacuité, dans ℕ.
-/
import ThesePlanetaire.LocalTraceLang

namespace JointGuard

open LocalTraceLang (PAut)

section Joint

variable {α B M : Type*}

/-- Boucle fermée conjointe, en sémantique partielle : le top est toujours tirable ; une émission
ne l'est que si le superviseur l'autorise, et elle s'ajoute à toutes les coordonnées. -/
def closedLoopJ [Add M] (tick : (B → M) → (B → M)) (e : α → B → M) (S : (B → M) → α → Prop)
    [∀ L a, Decidable (S L a)] : PAut (B → M) (Option α)
  | L, none => some (tick L)
  | L, some a => if S L a then some (fun c => L c + e a c) else none

/-- Vecteurs de charges atteignables depuis `L₀` en boucle fermée. -/
inductive ReachJ [Add M] (tick : (B → M) → (B → M)) (e : α → B → M) (S : (B → M) → α → Prop)
    (L₀ : B → M) : (B → M) → Prop
  | init : ReachJ tick e S L₀ L₀
  | top {L : B → M} : ReachJ tick e S L₀ L → ReachJ tick e S L₀ (tick L)
  | emit {L : B → M} {a : α} : ReachJ tick e S L₀ L → S L a →
      ReachJ tick e S L₀ (fun c => L c + e a c)

/-- Sûreté : sur tout vecteur atteignable, chaque coordonnée plafonnée reste sous son plafond. -/
def SafeSupJ [Add M] [LE M] (tick : (B → M) → (B → M)) (e : α → B → M) (G : Finset B)
    (cap : B → M) (L₀ : B → M) (S : (B → M) → α → Prop) : Prop :=
  ∀ L, ReachJ tick e S L₀ L → ∀ c ∈ G, L c ≤ cap c

/-- La garde conjointe : autoriser `a` ssi chaque coordonnée plafonnée reste sous son plafond. -/
def jointGuard [Add M] [LE M] (G : Finset B) (cap : B → M) (e : α → B → M) :
    (B → M) → α → Prop :=
  fun L a => ∀ c ∈ G, L c + e a c ≤ cap c

instance [Add M] [LE M] [DecidableRel ((· ≤ ·) : M → M → Prop)] (G : Finset B) (cap : B → M)
    (e : α → B → M) (L : B → M) (a : α) : Decidable (jointGuard G cap e L a) :=
  inferInstanceAs (Decidable (∀ c ∈ G, L c + e a c ≤ cap c))

variable [Add M] [LE M] {tick : (B → M) → (B → M)} {e : α → B → M} {G : Finset B}
  {cap L₀ : B → M} {S : (B → M) → α → Prop}

/-- ★ La garde conjointe est sûre dès que le top garde chaque coordonnée plafonnée sous son
plafond. -/
theorem jointGuard_safe (htick : ∀ L, (∀ c ∈ G, L c ≤ cap c) → ∀ c ∈ G, tick L c ≤ cap c)
    (hL₀ : ∀ c ∈ G, L₀ c ≤ cap c) : SafeSupJ tick e G cap L₀ (jointGuard G cap e) := by
  intro L h
  induction h with
  | init => exact hL₀
  | top _ ih => exact htick _ ih
  | emit _ hS _ => exact hS

/-- ★ **Maximalité** (pour tout top) : toute règle sûre atteint moins de vecteurs que la garde
conjointe, et n'autorise, sur ses états atteignables, que ce que la garde conjointe autorise. -/
theorem jointGuard_maximal (hS : SafeSupJ tick e G cap L₀ S) :
    (∀ L, ReachJ tick e S L₀ L → ReachJ tick e (jointGuard G cap e) L₀ L) ∧
      ∀ L a, ReachJ tick e S L₀ L → S L a → jointGuard G cap e L a := by
  have h2 : ∀ L a, ReachJ tick e S L₀ L → S L a → jointGuard G cap e L a :=
    fun L a hL ha => hS _ (ReachJ.emit hL ha)
  refine ⟨fun L h => ?_, h2⟩
  induction h with
  | init => exact ReachJ.init
  | top _ ih => exact ReachJ.top ih
  | emit hL ha ih => exact ReachJ.emit ih (h2 _ _ hL ha)

end Joint

/-! ### Témoins de non-vacuité (ℕ, deux coordonnées plafonnées) -/

section Witnesses

/-- Dans ℕ, un top qui ne fait monter aucune charge vérifie l'hypothèse de `jointGuard_safe`. -/
example {B : Type*} (G : Finset B) (cap : B → ℕ) (tick : (B → ℕ) → (B → ℕ))
    (htick : ∀ L c, tick L c ≤ L c) :
    ∀ L, (∀ c ∈ G, L c ≤ cap c) → ∀ c ∈ G, tick L c ≤ cap c :=
  fun L hL c hc => le_trans (htick L c) (hL c hc)

/-- La garde conjointe refuse une émission qui tient sur la coordonnée 0 et pas sur la 1. -/
example : (0 : ℕ) + 1 ≤ 2 ∧
    ¬ jointGuard (Finset.univ : Finset (Fin 2)) ![2, 2] (fun (_ : Unit) => ![1, 2]) ![0, 1] () := by
  decide

/-- Une règle stricte (marge 1 sur chaque plafond) est sûre sous un top non croissant… -/
example {α B : Type*} (G : Finset B) (cap L₀ : B → ℕ) (e : α → B → ℕ) (tick : (B → ℕ) → (B → ℕ))
    (htick : ∀ L c, tick L c ≤ L c) (hL₀ : ∀ c ∈ G, L₀ c ≤ cap c) :
    SafeSupJ tick e G cap L₀ (fun L a => ∀ c ∈ G, L c + e a c + 1 ≤ cap c) := by
  intro L h
  induction h with
  | init => exact hL₀
  | top _ ih => exact fun c hc => le_trans (htick _ c) (ih c hc)
  | @emit L a _ hS _ =>
    intro c hc
    have := hS c hc
    show L c + e a c ≤ cap c
    omega

/-- … et refuse une émission que la garde conjointe admet. -/
example : jointGuard (Finset.univ : Finset (Fin 2)) ![2, 2] (fun (_ : Unit) => ![1, 1]) ![1, 1] () ∧
    ¬ ∀ c ∈ (Finset.univ : Finset (Fin 2)), ![1, 1] c + ![1, 1] c + 1 ≤ ![2, 2] c := by
  decide

end Witnesses

end JointGuard
