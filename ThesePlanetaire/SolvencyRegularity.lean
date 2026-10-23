/-
  ThesePlanetaire/SolvencyRegularity.lean
  Promotion A1 (2026-07-11) : EUREKA tour 5, « La frontière de mémoire finie de
  la solvabilité » (`cache/eureka/r5/EUREKA5.md`, `07_proof.lean`).

  Ce fichier promeut au format macro du projet le résultat suivant : la
  vérifiabilité à mémoire finie de la solvabilité obéit au même critère
  d'assiette que l'idempotence, la localité et la finalité en une ronde
  (échelle des couplages, `EchelleCouplages.lean`) — un 4ᵉ invariant perdu
  au couplage par les entrées.

  (A) MÉMOIRE FINIE — assiette statique sorties-seules : le langage des
      séquences de clearing valides est reconnu par un automate pondéré dont
      l'espace d'états `ActivationState V` est un Fintype. Théorème DÉJÀ
      COMPILÉ de la thèse (`clearing_wfa_roundtrip`), réutilisé tel quel.
  (B) MÉMOIRE NON BORNÉE — assiette en flux net (« intégration organique »,
      les recettes créditent le solde) : le langage d'auto-financement sur
      le « huit comptable » (deux boucles partageant la trésorerie) n'est
      reconnu par AUCUN `BoolDFA` à espace d'états fini (∀-théorème,
      pigeonhole `Fintype.exists_ne_map_eq_of_card_lt`).

  Limites (voir `cache/eureka/r5/EUREKA5.md` §6, à respecter dans la prose
  LaTeX — motif F10 de la revue, ne pas sur-vendre le côté A) :
  1. Côté A mince en charge : `clearingToWFA` a `final _ := true`, sa force
     est le suivi d'état à espace fini, pas la richesse du langage accepté.
  2. Le pont institutionnel (assiette organique = créditer les recettes) est
     une modélisation argumentée, pas une dérivation axiomatique comptable.
  3. Impossibilité prouvée pour tout `BoolDFA` déterministe (Fintype) ;
     l'extension NFA n'est pas formalisée (les moniteurs à registres/compteurs
     reconnaissent évidemment L).
  4. Le « huit comptable » est UNE instance ; la loi générale « tout couplage
     non trivial est hors-régulier » n'est pas prouvée.
  5. `isSelfFinancing` quantifie sur toutes les listes (pas seulement les
     marches) ; le témoin n'utilise que de vraies marches.
  6. C-3 partiel : seule la face langagière de la conjecture est traitée.

  Origine des actifs cités — relus verbatim le 2026-07-11 :
  OrganicLP.lean:54-55,61-62 ; OrganicTEG.lean:35-37,53-58 ; Basic.lean:23-28 ;
  EndAnchor.lean:54-56,352-366 ; ClearingWFA.lean:38-41,68-71 ;
  LatticeClearing.lean:26.
-/

import ThesePlanetaire.OrganicLP
import ThesePlanetaire.EndAnchor
import ThesePlanetaire.ClearingWFA

open OrganicTEG OrganicLP EndAnchor

namespace SolvencyRegularity

/-! ### 1. Côté (A) — mémoire finie : réutilisation littérale du théorème de la thèse.

  Le langage des séquences de clearing valides (assiette statique) est décidé par
  un automate dont les états `ActivationState V = Finset (V × V)` forment un Fintype :
  la solvabilité séparable est vérifiable à mémoire finie. -/

theorem separable_finite_memory {V : Type*} [Fintype V] [DecidableEq V]
    (Φ : ClearingOperator V) (w : List (V × V)) :
    ClearingWFA.isValidClearingSequence Φ w ↔
    WeightedAutomaton.word_weight (ClearingWFA.clearingToWFA Φ) w = true :=
  ClearingWFA.clearing_wfa_roundtrip Φ w

/-- L'espace d'états du vérificateur séparable est FINI (le point « mémoire finie »). -/
example : Fintype (Finset (Fin 3 × Fin 3)) := inferInstance

/-! ### 2. Le « huit comptable » : deux boucles partageant la trésorerie (sommet 0).

  Boucle A = (0,1)(1,0) : génératrice (cash_flow(1) = +1) ;
  Boucle B = (0,2)(2,0) : consommatrice (cash_flow(2) = −1) ;
  cash_flow(0) = 0 (la trésorerie n'émet pas). -/

def huitTEG : OrganicTEG (Fin 3) where
  graph :=
    { edges := {((0 : Fin 3), (1 : Fin 3)), ((1 : Fin 3), (0 : Fin 3)),
                ((0 : Fin 3), (2 : Fin 3)), ((2 : Fin 3), (0 : Fin 3))}
      no_loops := by decide }
  cash_flow := fun v => if v = 1 then 1 else if v = 2 then -1 else 0
  guard := ⟨{((0 : Fin 3), (1 : Fin 3))}, ⟨_, Finset.mem_singleton_self _⟩⟩
  end_anchor := ⟨{((1 : Fin 3), (0 : Fin 3))}, ⟨_, Finset.mem_singleton_self _⟩⟩
  holding_time := fun _ _ => Z_max.ofInt 1

def Ablock : List (Fin 3 × Fin 3) := [(0, 1), (1, 0)]
def Bblock : List (Fin 3 × Fin 3) := [(0, 2), (2, 0)]

/-- A^i : i tours de la boucle génératrice (marche réelle : chaque bloc revient en 0). -/
def Apow : ℕ → List (Fin 3 × Fin 3)
  | 0 => []
  | n + 1 => Ablock ++ Apow n

/-- B^j : j tours de la boucle consommatrice. -/
def Bpow : ℕ → List (Fin 3 × Fin 3)
  | 0 => []
  | n + 1 => Bblock ++ Bpow n

/-! ### 3. Lemmes de compteur (fermes, par induction — pas de decide caché) -/

lemma cashFlowSum_append (teg : OrganicTEG (Fin 3)) (u v : List (Fin 3 × Fin 3)) :
    cashFlowSum teg (u ++ v) = cashFlowSum teg u + cashFlowSum teg v := by
  simp [cashFlowSum, List.map_append, List.sum_append]

lemma cashFlowSum_Ablock : cashFlowSum huitTEG Ablock = 1 := by decide

lemma cashFlowSum_Bblock : cashFlowSum huitTEG Bblock = -1 := by decide

lemma Apow_length (i : ℕ) : (Apow i).length = 2 * i := by
  induction i with
  | zero => rfl
  | succ n ih => simp [Apow, Ablock, ih]; omega

lemma cashFlowSum_Apow (i : ℕ) : cashFlowSum huitTEG (Apow i) = i := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [Apow, cashFlowSum_append, cashFlowSum_Ablock, ih]
    push_cast; ring

lemma cashFlowSum_Bpow (j : ℕ) : cashFlowSum huitTEG (Bpow j) = -j := by
  induction j with
  | zero => rfl
  | succ n ih =>
    rw [Bpow, cashFlowSum_append, cashFlowSum_Bblock, ih]
    push_cast; ring

/-- Tout préfixe de A^i garde un compteur ≥ 0 (la boucle génératrice ne descend jamais). -/
lemma Apow_take_nonneg (i n : ℕ) : 0 ≤ cashFlowSum huitTEG ((Apow i).take n) := by
  induction i generalizing n with
  | zero => simp [Apow, cashFlowSum]
  | succ m ih =>
    rw [Apow, List.take_append, cashFlowSum_append]
    have h₁ : 0 ≤ cashFlowSum huitTEG (Ablock.take n) := by
      match n with
      | 0 => decide
      | 1 => decide
      | (k + 2) =>
        have : Ablock.take (k + 2) = Ablock := List.take_of_length_le (by simp [Ablock])
        rw [this]; decide
    have h₂ := ih (n - Ablock.length)
    linarith

/-- Tout préfixe de B^j perd au plus j (chaque tour de boucle consomme 1, jamais plus vite). -/
lemma Bpow_take_ge (j n : ℕ) : -(j : ℤ) ≤ cashFlowSum huitTEG ((Bpow j).take n) := by
  induction j generalizing n with
  | zero => simp [Bpow, cashFlowSum]
  | succ m ih =>
    rw [Bpow, List.take_append, cashFlowSum_append]
    have h₁ : -1 ≤ cashFlowSum huitTEG (Bblock.take n) := by
      match n with
      | 0 => decide
      | 1 => decide
      | (k + 2) =>
        have : Bblock.take (k + 2) = Bblock := List.take_of_length_le (by simp [Bblock])
        rw [this]; decide
    have h₂ := ih (n - Bblock.length)
    push_cast
    linarith

/-! ### 4. Le langage : A^i B^j solvable ⟺ j ≤ i -/

/-- Sens accepté : j ≤ i ⟹ le mot A^i B^j est auto-financé (tous les préfixes ≥ 0). -/
theorem AB_accept (i j : ℕ) (hji : j ≤ i) :
    isSelfFinancing huitTEG (Apow i ++ Bpow j) := by
  intro n _
  rw [List.take_append, cashFlowSum_append]
  by_cases hn : n ≤ (Apow i).length
  · have hz : n - (Apow i).length = 0 := Nat.sub_eq_zero_of_le hn
    rw [hz]
    simp only [List.take_zero, cashFlowSum, List.map_nil, List.sum_nil, add_zero]
    exact Apow_take_nonneg i n
  · have hlen : (Apow i).length < n := Nat.lt_of_not_le hn
    have hfull : (Apow i).take n = Apow i := List.take_of_length_le (le_of_lt hlen)
    rw [hfull, cashFlowSum_Apow]
    have hB := Bpow_take_ge j (n - (Apow i).length)
    have hcast : (j : ℤ) ≤ (i : ℤ) := by exact_mod_cast hji
    linarith

/-- Sens rejeté : i < j ⟹ le mot A^i B^j viole la solvabilité (le mot ENTIER est
    un préfixe de lui-même, de somme i − j < 0). -/
theorem AB_reject (i j : ℕ) (hij : i < j) :
    ¬ isSelfFinancing huitTEG (Apow i ++ Bpow j) := by
  intro h
  have hmem : (Apow i ++ Bpow j).length ∈
      Finset.range ((Apow i ++ Bpow j).length + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_self _)
  have := h _ hmem
  rw [List.take_length, cashFlowSum_append, cashFlowSum_Apow, cashFlowSum_Bpow] at this
  have hcast : (i : ℤ) < (j : ℤ) := by exact_mod_cast hij
  linarith

/-! ### 5. Côté (B) — impossibilité : AUCUN automate fini ne reconnaît L.

  Pigeonhole : parmi les card(état)+1 préfixes A^0, …, A^card, deux atteignent le
  même état ; le suffixe B^k (k = le plus grand des deux indices) les sépare dans L
  (AB_accept k k vs AB_reject i k) — contradiction. -/

lemma run_append (dfa : EndAnchor.BoolDFA (Fin 3 × Fin 3))
    (u v : List (Fin 3 × Fin 3)) :
    dfa.run (u ++ v) = List.foldl dfa.trans (dfa.run u) v := by
  simp [EndAnchor.BoolDFA.run, List.foldl_append]

/-- Cœur du pigeonhole : une collision d'états entre A^i et A^k (i < k) est absurde. -/
lemma collision_absurd (dfa : EndAnchor.BoolDFA (Fin 3 × Fin 3))
    (h : ∀ w, dfa.dfa_accepts w ↔ isSelfFinancing huitTEG w)
    (i k : ℕ) (hik : i < k) (heq : dfa.run (Apow i) = dfa.run (Apow k)) : False := by
  have hacc : dfa.dfa_accepts (Apow k ++ Bpow k) :=
    (h _).mpr (AB_accept k k le_rfl)
  have hsame : dfa.dfa_accepts (Apow i ++ Bpow k) ↔
      dfa.dfa_accepts (Apow k ++ Bpow k) := by
    simp only [EndAnchor.BoolDFA.dfa_accepts, run_append, heq]
  exact AB_reject i k hik ((h _).mp (hsame.mpr hacc))

/-- **Théorème d'impossibilité** : aucun BoolDFA à espace d'états FINI ne reconnaît
    le langage d'auto-financement du huit comptable. La solvabilité en flux net
    n'est pas vérifiable à mémoire finie. -/
theorem no_finite_verifier (dfa : EndAnchor.BoolDFA (Fin 3 × Fin 3))
    [Fintype dfa.state]
    (h : ∀ w, dfa.dfa_accepts w ↔ isSelfFinancing huitTEG w) : False := by
  obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun n : Fin (Fintype.card dfa.state + 1) => dfa.run (Apow n.val))
    (by simp)
  rcases Nat.lt_trichotomy a.val b.val with hlt | heqv | hlt
  · exact collision_absurd dfa h a.val b.val hlt heq
  · exact absurd (Fin.ext heqv) hab
  · exact collision_absurd dfa h b.val a.val hlt heq.symm

/-! ### 6. Synthèse : la frontière de mémoire finie de la solvabilité.

  (A) assiette statique sorties-seules ⟹ vérificateur à états finis (théorème de la
      thèse, réutilisé) ; (B) assiette en flux net ⟹ aucun vérificateur fini.
  La frontière de vérifiabilité coïncide avec le critère d'assiette. -/

theorem frontiere_memoire_finie_de_la_solvabilite :
    (∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
       (Φ : ClearingOperator V) (w : List (V × V)),
       ClearingWFA.isValidClearingSequence Φ w ↔
       WeightedAutomaton.word_weight (ClearingWFA.clearingToWFA Φ) w = true)
    ∧ (∀ (dfa : EndAnchor.BoolDFA (Fin 3 × Fin 3)) (_ : Fintype dfa.state),
       ¬ (∀ w, dfa.dfa_accepts w ↔ isSelfFinancing huitTEG w)) :=
  ⟨fun _ _ _ Φ w => ClearingWFA.clearing_wfa_roundtrip Φ w,
   fun dfa inst h => @no_finite_verifier dfa inst h⟩

end SolvencyRegularity
