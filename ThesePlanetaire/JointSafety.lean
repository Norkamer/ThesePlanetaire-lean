/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/JointSafety.lean
  Sûreté conjointe (2026-10-11, D-41) — papier 15 : la sûreté d'une coalition à plusieurs
  plafonds, et le corollaire 1(c). Développé d'abord en `JointSafety_scratch.lean` (workflow du
  dépôt). Trace : `cache/surete_conjointe_2026-10-11/`.

  Module neuf (D-30) : aucun module existant n'est modifié. Il importe `AdhesionSafety`,
  `ClubWelfare` (papier 15) et `JointReserve` (papier 11).

  Portée. Dans ℕ. Un ensemble fini `G` de plafonds ; pour chaque plafond `c`, une mémoire
  `mem c`, un taux `r c`, un plafond `cap c` ; des émissions vectorielles (`enat n c`,
  `aP i μ c`, `aM i μ c`) ; un état `μ` commun ; un top **plafond par plafond**. Un non-membre
  émet l'un de ses deux plans, choisi à chaque occurrence (`pureSrc`) ; un membre émet `0`,
  comme dans `AdhesionSafety.Safe`.
  - `jsafe_iff_forall_safe` : la sûreté pour les plafonds de `G` (`JSafe`, définie par la
    viabilité à plans de `JointReserve`) est la sûreté `AdhesionSafety.Safe` pour chacun ;
    `jsafe_iff` : la condition de masse plafond par plafond ; `jsafe_mono` : elle est croissante.
  - `exists_stable_jsafe_iff`, `seeding_jsafe_iff` : instances de
    `ClubWelfare.exists_nash_iff_of_upward` et `ClubWelfare.seeding_iff_of_upward`.
  - `exists_stable_jsafe_iff_forall` : une coalition stable sûre pour tous les plafonds existe
    ssi, pour chaque plafond, une coalition stable sûre pour lui existe (le plus grand équilibre
    sert pour tous).
  - `critical_two_caps` : témoin à deux plafonds (exemple 8 du papier 15, second plafond).
  Nature : composition élémentaire de `JointReserve.viableC_iff`, `JointReserve.viableJ_nat_iff`,
  `AdhesionSafety.safe_iff` et du théorème 4 générique. Rien ici sur les réseaux (théorème 5(e)),
  la clause de sûreté du théorème 7(c)(vii), un corps ordonné, un top couplé ni un état inconnu.
-/

import ThesePlanetaire.AdhesionSafety
import ThesePlanetaire.ClubWelfare
import ThesePlanetaire.JointReserve

/-!
# Sûreté à plusieurs plafonds

Une coalition `X` est sûre pour les plafonds de `G` (`JSafe`) si un ensemble tenable non vide
existe pour la garde à plusieurs plafonds de `JointReserve`, quand la nature émet ses vecteurs,
chaque membre `0`, et chaque non-membre l'un de ses deux plans, choisi à chaque occurrence.

1. `tickOp_mono` : le top de `FeedbackClass` est croissant dans ℕ.
2. ★ `jsafe_iff_forall_safe`, `jsafe_iff` : la sûreté pour `G` est la sûreté pour chaque
   plafond, donc la condition de masse `Σ enat + M_{X,c} ≤ memBound` sur chaque plafond.
   `jsafe_mono` : elle est croissante.
3. ★ `exists_stable_jsafe_iff`, `seeding_jsafe_iff`, `exists_stable_jsafe_iff_forall`.
4. ★ `critical_two_caps`.
-/

namespace JointSafety

open AdhesionGame
open FeedbackClass (Memory tickOp)
open ReserveCoverage (srcEmit uncMass)
open AdhesionSafety (Safe finOf memBound safe_iff safe_mono finOf_coe)
open JointReserve (ViableC viableC_iff viableJ_nat_iff)

/-! ### §1. Le top est croissant -/

/-- Le top de période est croissant dans ℕ (soustraction tronquée comprise). -/
theorem tickOp_mono (m : Memory) (r : ℕ) : Monotone (tickOp m r) := by
  intro a b h
  cases m with
  | stock => exact h
  | regen => exact Nat.sub_le_sub_right h r
  | flow => exact le_rfl

/-! ### §2. Sûreté pour plusieurs plafonds -/

variable {V : Type*} [Fintype V] [DecidableEq V] {B K Un : Type*} [Fintype Un] [DecidableEq Un]

/-- Le substitut : sur chaque plafond, la source de `AdhesionSafety.Safe` pour ce plafond (nature,
`0` pour un membre, maximum des deux plans pour un non-membre). -/
def jointSrc (enat : Un → K → ℕ) (aP aM : V → B → K → ℕ) (A : Finset V) (μ : B) :
    Un ⊕ V → K → ℕ :=
  fun u c => srcEmit (fun n => enat n c) (fun i b => aP i b c) (fun i b => aM i b c) A μ u

/-- Les plans purs : la nature émet `enat n`, un membre `0`, un non-membre l'un de ses deux
plans, choisi à chaque occurrence. -/
def pureSrc (enat : Un → K → ℕ) (aP aM : V → B → K → ℕ) (A : Finset V) (μ : B) :
    Un ⊕ V → (K → ℕ) → Prop
  | .inl n, v => v = enat n
  | .inr i, v => if i ∈ A then v = 0 else v = aP i μ ∨ v = aM i μ

/-- Coalition sûre pour les plafonds de `G` : la garde à plusieurs plafonds tient chaque plafond
de `G` quand la nature et les non-membres échappent à la couverture, un non-membre émettant l'un
de ses deux plans à chaque occurrence. -/
def JSafe (G : Finset K) (mem : K → Memory) (r cap : K → ℕ) (enat : Un → K → ℕ)
    (aP aM : V → B → K → ℕ) (μ : B) (X : Set V) : Prop :=
  ViableC G (fun c => tickOp (mem c) (r c)) (pureSrc enat aP aM (finOf X) μ) cap

variable {G : Finset K} {mem : K → Memory} {r cap : K → ℕ} {enat : Un → K → ℕ}
  {aP aM : V → B → K → ℕ} {μ : B}

omit [Fintype V] [Fintype Un] [DecidableEq Un] in
/-- Chaque plan est sous le substitut, sur chaque plafond. -/
theorem pureSrc_le (A : Finset V) :
    ∀ u v, pureSrc enat aP aM A μ u v → ∀ c ∈ G, v c ≤ jointSrc enat aP aM A μ u c := by
  rintro (n | i) v hv c _
  · subst hv; exact le_rfl
  · simp only [pureSrc] at hv
    simp only [jointSrc, srcEmit]
    split_ifs at hv ⊢ with hi
    · subst hv; exact le_rfl
    · rcases hv with rfl | rfl
      · exact le_max_left _ _
      · exact le_max_right _ _

omit [Fintype V] [Fintype Un] [DecidableEq Un] in
/-- Sur chaque plafond, un plan atteint le substitut. -/
theorem pureSrc_attains (A : Finset V) :
    ∀ u, ∀ c ∈ G, ∃ v, pureSrc enat aP aM A μ u v ∧ jointSrc enat aP aM A μ u c ≤ v c := by
  rintro (n | i) c _
  · exact ⟨enat n, rfl, le_rfl⟩
  · by_cases hi : i ∈ A
    · exact ⟨0, by simp [pureSrc, hi], by simp [jointSrc, srcEmit, hi]⟩
    · rcases le_total (aM i μ c) (aP i μ c) with h | h
      · exact ⟨aP i μ, by simp [pureSrc, hi], by simp [jointSrc, srcEmit, hi, h]⟩
      · exact ⟨aM i μ, by simp [pureSrc, hi], by simp [jointSrc, srcEmit, hi, h]⟩

/-- ★ **Plafond par plafond.** Une coalition est sûre pour les plafonds de `G` ssi elle est sûre
(`AdhesionSafety.Safe`) pour chacun. -/
theorem jsafe_iff_forall_safe {X : Set V} :
    JSafe G mem r cap enat aP aM μ X ↔
      ∀ c ∈ G, Safe (mem c) (r c) (cap c) (fun n => enat n c) (fun i b => aP i b c)
        (fun i b => aM i b c) μ X := by
  rw [JSafe, viableC_iff (w := jointSrc enat aP aM (finOf X) μ)
    (fun c _ => tickOp_mono (mem c) (r c)) (pureSrc_le _) (pureSrc_attains _), viableJ_nat_iff]
  rfl

/-- ★ **Condition de masse**, sur chaque plafond de `G`. -/
theorem jsafe_iff {X : Set V} :
    JSafe G mem r cap enat aP aM μ X ↔
      ∀ c ∈ G, ∑ n, enat n c + uncMass (fun i b => aP i b c) (fun i b => aM i b c) (finOf X) μ ≤
        memBound (mem c) (r c) (cap c) := by
  rw [jsafe_iff_forall_safe]
  exact forall₂_congr fun _ _ => safe_iff

/-- La sûreté pour plusieurs plafonds est croissante. -/
theorem jsafe_mono {X Y : Set V} (h : X ⊆ Y) (hX : JSafe G mem r cap enat aP aM μ X) :
    JSafe G mem r cap enat aP aM μ Y := by
  rw [jsafe_iff_forall_safe] at hX ⊢
  exact fun c hc => safe_mono h (hX c hc)

/-! ### §3. Sûreté ∩ stabilité (corollaire 1(c)) -/

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {g : V → Set V → 𝕜}

omit [IsStrictOrderedRing 𝕜] in
/-- ★ Une coalition stable sûre pour les plafonds de `G` existe ssi le plus grand équilibre l'est
(théorème 4 avec `P = JSafe …`). -/
theorem exists_stable_jsafe_iff (hg : Supermodular g) :
    (∃ X, IsNash g X ∧ JSafe G mem r cap enat aP aM μ X) ↔
      JSafe G mem r cap enat aP aM μ (br g hg).gfp :=
  ClubWelfare.exists_nash_iff_of_upward hg fun _ _ h hX => jsafe_mono h hX

/-- ★ Un amorçage temporaire laisse une coalition stable sûre pour les plafonds de `G` ssi le plus
grand équilibre l'est. -/
theorem seeding_jsafe_iff (hg : Supermodular g) :
    (∃ H, 0 ≤ H ∧ JSafe G mem r cap enat aP aM μ (afterSeed g hg H)) ↔
      JSafe G mem r cap enat aP aM μ (br g hg).gfp :=
  ClubWelfare.seeding_iff_of_upward hg fun _ _ h hX => jsafe_mono h hX

omit [IsStrictOrderedRing 𝕜] in
/-- ★ Une coalition stable sûre pour tous les plafonds de `G` existe ssi, pour chaque plafond,
une coalition stable sûre pour lui existe. Les deux côtés valent ssi le plus grand équilibre est
sûr pour chaque plafond. -/
theorem exists_stable_jsafe_iff_forall (hg : Supermodular g) :
    (∃ X, IsNash g X ∧ JSafe G mem r cap enat aP aM μ X) ↔
      ∀ c ∈ G, ∃ X, IsNash g X ∧ Safe (mem c) (r c) (cap c) (fun n => enat n c)
        (fun i b => aP i b c) (fun i b => aM i b c) μ X := by
  rw [exists_stable_jsafe_iff hg, jsafe_iff_forall_safe]
  exact forall₂_congr fun _ _ => (AdhesionSafety.exists_stable_safe_iff hg).symm

/-! ### §4. Témoin -/

/-- Émissions `(8, 1, 1, 1, 1)` sur le plafond `0` et `(1, 1, 1, 1, 8)` sur le plafond `1`, dans
les deux plans. -/
def eTwo : Fin 5 → Unit → Fin 2 → ℕ := fun i _ c =>
  if c = 0 then (if i = 0 then 8 else 1) else (if i = 4 then 8 else 1)

/-- La coalition `A` est sûre pour les plafonds de `G` : `regen`, `r = cap = 4` sur chaque
plafond, sans nature, émissions `eTwo`. -/
def critSafe (G : Finset (Fin 2)) (A : Finset (Fin 5)) : Prop :=
  JSafe G (fun _ => .regen) (fun _ => 4) (fun _ => 4) (fun (_ : Empty) _ => 0) eTwo eTwo ()
    (A : Set (Fin 5))

/-- ★ **La masse critique se compte plafond par plafond** : `{0}` est sûre pour le plafond `0`
seulement, `{4}` pour le plafond `1` seulement, `{0, 4}` pour les deux (masses non couvertes
`4 | 11`, `11 | 4`, `3 | 3`, contre `min r cap = 4`). -/
theorem critical_two_caps :
    (critSafe {0} {0} ∧ ¬ critSafe {1} {0}) ∧ (¬ critSafe {0} {4} ∧ critSafe {1} {4}) ∧
      critSafe Finset.univ {0, 4} := by
  simp only [critSafe, jsafe_iff, finOf_coe]
  decide

end JointSafety
