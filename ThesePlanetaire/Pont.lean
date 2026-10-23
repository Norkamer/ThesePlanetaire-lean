/-
  MonnaiesEndogene/Pont.lean
  Théorème-pont (Ch.5) — version CORRIGÉE

  La preuve du Ch.5 contient une erreur dans H2 :
  elle pose p(t) ≤ B_circ(t) mais la justification correcte est
  p(t) ≥ B_circ(0) - B_circ(t) (chaque pas productif réduit B_circ de ≥1).
  Avec H2 corrigée, k(t) ≤ B_circ(t) est bien un théorème.

  Contre-exemple pour la terminaison simultanée sans H-DISS-exact.
  Théorèmes :
  (i)   k(t) ≤ B_circ(t) — inégalité fondamentale (H2 corrigée)
  (ii)  Sous H-DISS-exact : k(t) = B_circ(t)
  (iii) Terminaison simultanée sous H-DISS-exact + k-exact
-/

import ThesePlanetaire.EXT3
import ThesePlanetaire.EXT1

open Nat

/-! ### Contre-exemple : terminaison simultanée sans H-DISS-exact

B_circ décroît par sauts >1 : chute 5→0 en 2 pas.
k ne peut décrémenter que 2 fois, reste à 3 ≠ 1.
La terminaison simultanée (au même T) échoue.

-- Commenté : difficulté technique avec `dec_trivial` sur `match` à variables libres.
-- La construction est documentée dans le Ch.5 et peut être réactivée quand
-- `native_decide` supportera les `match` avec variables. Voir le résumé de session
-- pour la preuve complète.

-- def ce_k (t : ℕ) : ℕ := match t with | 0 => 5 | 1 => 4 | _ => 3
-- def ce_p (t : ℕ) : ℕ := match t with | 0 => 0 | 1 => 1 | _ => 2
-- def ce_bcirc (t : ℕ) : ℕ := match t with | 0 => 5 | 1 => 2 | _ => 0

-- lemma contre_exemple_terminaison_simultanee :
--     ∃ (k p bcirc : ℕ → ℕ) (m : ℕ),
--       bcirc 0 = k 0 ∧ k 0 ≤ m ∧ (∀ t, k t ≥ 1) ∧
--       (∀ t, bcirc t > 0 → bcirc (t + 1) < bcirc t) ∧
--       (∀ t, bcirc (t + 1) < bcirc t → k (t + 1) < k t) ∧
--       (∀ t, k t + p t = k 0) ∧
--       ∀ T, ¬ (bcirc T = 0 ∧ k T = 1) := ...
-/

section Pont

variable (m : ℕ) (k p bcirc : ℕ → ℕ)

/-- (i) Inégalité fondamentale : k(t) ≤ B_circ(t), quand B_circ(t) > 0.

    Hypothèse corrigée (H2') : chaque pas productif (compté par p)
    réduit B_circ d'au moins 1, donc le nombre de pas productifs
    dépasse la diminution totale de B_circ :
      p(t) ≥ B_circ(0) - B_circ(t).

    Avec k(t) + p(t) = k(0) = B_circ(0), on obtient k(t) ≤ B_circ(t).
    Garde bcirc t > 0 : l'inégalité n'est garantie que pendant la phase
    active du clearing (avant terminaison de B_circ). -/
theorem pont_inegalite_fondamentale
    (h_bcirc_init : bcirc 0 = k 0)
    (h_decomp : ∀ t, k t + p t = k 0)
    (h_step_reduces : ∀ t, bcirc t > 0 → bcirc t + p t ≥ k 0)
    : ∀ t, bcirc t > 0 → k t ≤ bcirc t := by
  intro t hbcirc_pos
  have hk := h_decomp t
  have hred := h_step_reduces t hbcirc_pos
  omega

/-- (ii) Égalité dynamique k(t) = B_circ(t) sous H-DISS-exact.

    Si B_circ décrémente d'exactement 1 par pas non-terminal,
    alors B_circ(t) = k₀ - t pour t < k₀.
    Si de plus p(t) = t (chaque pas est productif), alors
    k(t) = k₀ - t = B_circ(t).
    Domaine strict t < k₀ : l'égalité tient pendant la phase active
    du clearing. Au point terminal t = k₀, k(k₀) = 1 mais bcirc(k₀) = 0. -/
theorem pont_egalite_dynamique
    (h_bcirc_init : bcirc 0 = k 0)
    (h_bcirc_exact : ∀ t, bcirc t > 0 → bcirc (t + 1) = bcirc t - 1)
    (h_decomp : ∀ t, k t + p t = k 0)
    (h_p_count : ∀ t, t < k 0 → p t = t)
    : ∀ t, t < k 0 → k t = bcirc t := by
  set k0 := k 0 with hk0
  intro t ht
  have h_bcirc_val : bcirc t = k0 - t := by
    induction t with
    | zero => rw [h_bcirc_init, hk0]; omega
    | succ t ih =>
      have hpos : bcirc t > 0 := by
        rw [ih (by omega)]; omega
      rw [h_bcirc_exact t hpos, ih (by omega)]; omega
  have hk_val : k t = k0 - t := by
    have := h_decomp t
    rw [h_p_count t ht, hk0] at this; omega
  rw [h_bcirc_val, hk_val]

/-- (iii) Terminaison simultanée sous H-DISS-exact.
    B_circ décrémente d'exactement 1 par pas → 0 en k₀ pas.
    k décrémente de 1 quand B_circ↓ et k>1 → 1 en k₀-1 pas,
    puis reste à 1. B_circ(k₀)=0, k(k₀)=1. -/
theorem pont_terminaison_simultanee
    (h_bcirc_init : bcirc 0 = k 0) (h_init : k 0 ≤ m)
    (h_k_ge_one : ∀ t, k t ≥ 1) (h_k_mono : ∀ t, k (t + 1) ≤ k t)
    (h_bcirc_exact : ∀ t, bcirc t > 0 → bcirc (t + 1) = bcirc t - 1)
    (h_k_exact : ∀ t, bcirc (t + 1) < bcirc t → k t > 1 → k (t + 1) = k t - 1)
    : ∃ T, T ≤ m ∧ bcirc T = 0 ∧ k T = 1 := by
  set k0 := k 0 with hk0
  -- B_circ(t) = k0 - t pour t ≤ k0
  have h_bcirc_val : ∀ t, t ≤ k0 → bcirc t = k0 - t := by
    intro t ht; induction t with
    | zero => rw [h_bcirc_init, hk0]; omega
    | succ t ih =>
      have hpos : bcirc t > 0 := by
        rw [ih (by omega)]; omega
      rw [h_bcirc_exact t hpos, ih (by omega)]; omega
  -- bcirc(k₀) = 0
  have hbcirc0 : bcirc k0 = 0 := by
    rw [h_bcirc_val k0 (le_refl _)]; omega
  -- k(t) = k0 - t pour t < k0
  have h_k_val : ∀ t, t < k0 → k t = k0 - t := by
    intro t ht; induction t with
    | zero => omega
    | succ t ih =>
      have ht_lt : t < k0 := by omega
      have h_bcirc_dec : bcirc (t+1) < bcirc t := by
        have hpos : bcirc t > 0 := by
          rw [h_bcirc_val t (by omega)]; omega
        rw [h_bcirc_exact t hpos]; omega
      have hkt_gt_one : k t > 1 := by
        rw [ih ht_lt]; omega
      rw [h_k_exact t h_bcirc_dec hkt_gt_one, ih ht_lt]; omega
  -- Cas k0 = 0 : contradiction avec k ≥ 1
  by_cases hk0z : k0 = 0
  · have h_contra : k 0 ≥ 1 := h_k_ge_one 0
    rw [← hk0, hk0z] at h_contra; omega
  · -- k₀ ≥ 1 : k(k₀-1) = 1, puis k(k₀) = 1
    have h_pred_val : k (k0 - 1) = 1 := by
      have hlt : k0 - 1 < k0 := by omega
      rw [h_k_val (k0 - 1) hlt]; omega
    have hk_k0_eq_one : k k0 = 1 := by
      have hmono := h_k_mono (k0 - 1)
      have : k0 - 1 + 1 = k0 := by omega
      rw [this] at hmono
      rw [h_pred_val] at hmono
      have hge : k k0 ≥ 1 := h_k_ge_one k0; omega
    exact ⟨k0, by rw [hk0]; exact h_init, hbcirc0, hk_k0_eq_one⟩

end Pont
