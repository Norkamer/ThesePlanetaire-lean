/-
  ThesePlanetaire/LocalTraceLang.lean
  Phase 6 (2026-10-02) : automates partiels, concurrence maximale et stabilité (Husson–Morin).

  Développé d'abord en `LocalTraceLang_scratch.lean` (workflow du dépôt). Plan :
  `~/.claude/plans/witty-dazzling-manatee.md` (Phase 6, 6a) ; analyse :
  `cache/analyse_stabilite_traces_locales_2026-10-02.md` (§1, §3, §9).

  Husson & Morin (FoSSaCS 2000) définissent les langages de traces locaux stables (Déf. 2.1 :
  S1 et S2) et les automates stablement concurrents (Déf. 2.4, axiome du cube) ; le Th. 4.4
  dit : stable ⟺ image d'un langage de Mazurkiewicz par projection. Ce module formalise le côté
  automate, en sémantique PARTIELLE (`none` = lettre non tirable), et donne deux critères
  suffisants qui évitent les preuves au cas par cas.
  1. `PAut σ α := σ → α → Option σ`, `run` (lecture d'un mot), `run_append` ;
  2. `maxPar δ q a b` : concurrence maximale (Déf. 2.3, prise maximale) — `a ≠ b`, les deux
     ordres définis et d'état d'arrivée égal ; `parAfter δ q x a b` : la même après `x`
     (`parAfter_iff` : « q·x existe et a ∥ b en q·x ») ; ★ `maxPar_symm`, ★ `maxPar_irrefl` ;
  3. `Cube` (Déf. 2.4), `StablyConcurrent`, `S2At`/`S2` (Déf. 2.1, S2 sur la
     paire-indépendance `I(u,{x,y}) := maxPar (q·u) x y`) ;
  4. critère « losange partiel » : une indépendance statique irréflexive `I` dont les échanges
     sont des égalités dans `Option` et qui majore `maxPar` donne ★ `stablyConcurrent_of_diamond`
     et ★ `S2_of_diamond` (le côté Mazurkiewicz : la concurrence EST `I` sur les lettres
     tirables) ; ★ `TraceQ.liftRun` : le langage est clos par traces de `I` ;
  5. critère commutatif : `IsCommutativePA δ` (`run q [a,b] = run q [b,a]`, égalité dans
     `Option`) ⟹ ★ `stablyConcurrent_of_commutative`, ★ `S2_of_commutative` — les deux membres
     de chaque équivalence se ramènent à « `run q [a,b,c]` est défini ». Suffisant, pas
     nécessaire (le producteur–consommateur de Husson–Morin est stable sans être commutatif) ;
  6. lien total / partiel : `ofGated P upd` (rejet = lettre non tirable) et `toTotal`
     (rejet = boucle) ; ★ `toTotal_ofGated` : `toTotal (ofGated P upd) = gatedStep P upd`.
  7. pas gardés partiels : `run_ofGated_pair`, ★ `isCommutativePA_ofGated` (mises à jour
     commutatives et tirabilité de `ab` ⟹ celle de `ba`), `maxPar_ofGated_iff` ;
  8. cohérence d'échange `SwapCoherent` (∥ ne lit plus que la définition des mots) et
     projections `ProjectsTo`, qui transportent le cube et S2 (★ `cube_iff_of_projectsTo`,
     ★ `S2At_iff_of_projectsTo`, `stablyConcurrent_iff_of_projectsTo`) ;
  9. états accessibles : `run_inv`, ★ `reachable_finite_of_inv` (invariant fini ⟹ système de
     transitions à pas fini, Déf. 1.7) ; `foldl_eq_run` (un pli `Option` à état mort est la
     lecture de l'automate partiel induit).
  Les sections 7 à 9 servent aux instances (`DepletionStable`, `LedgerNotStable`).

  Non formalisés (cités) : S1 et ∼ (Déf. 1.1, 2.1), complétude Cpl1-4 (Déf. 1.2), Déf. 2.5,
  Th. 4.4, 4.5, 5.4.

  Mathlib seul (plus `GatedStep`, module bas).
-/

import Mathlib.Tactic
import ThesePlanetaire.GatedStep

namespace LocalTraceLang

open GatedStep
open CommutativeClassification (IsCommutativeUpdate)

variable {σ α : Type*}

/-! ### 1. Automates partiels -/

/-- Automate partiel déterministe : `δ q a = none` si `a` n'est pas tirable en `q`. -/
abbrev PAut (σ α : Type*) := σ → α → Option σ

/-- Lecture d'un mot depuis `q` ; `none` dès qu'une lettre n'est pas tirable. -/
def run (δ : PAut σ α) : σ → List α → Option σ
  | q, [] => some q
  | q, a :: w => (δ q a).bind (fun q' => run δ q' w)

@[simp] theorem run_nil (δ : PAut σ α) (q : σ) : run δ q [] = some q := rfl

theorem run_cons (δ : PAut σ α) (q : σ) (a : α) (w : List α) :
    run δ q (a :: w) = (δ q a).bind (fun q' => run δ q' w) := rfl

@[simp] theorem run_singleton (δ : PAut σ α) (q : σ) (a : α) : run δ q [a] = δ q a := by
  rw [run_cons]
  cases δ q a <;> rfl

theorem run_append (δ : PAut σ α) :
    ∀ (q : σ) (u v : List α), run δ q (u ++ v) = (run δ q u).bind (fun q' => run δ q' v)
  | q, [], v => rfl
  | q, a :: u, v => by
    rw [List.cons_append, run_cons, run_cons]
    cases δ q a with
    | none => rfl
    | some q' => exact run_append δ q' u v

/-- Un mot lisible a ses préfixes lisibles. -/
theorem isSome_of_isSome_append {δ : PAut σ α} {q : σ} {u v : List α}
    (h : (run δ q (u ++ v)).isSome) : (run δ q u).isSome := by
  rw [run_append] at h
  cases hu : run δ q u with
  | none => rw [hu] at h; exact absurd h (by simp)
  | some _ => rfl

/-- Langage d'un automate partiel depuis `q₀` : les mots lisibles (clos par préfixe). -/
def lang (δ : PAut σ α) (q₀ : σ) : Set (List α) := {w | (run δ q₀ w).isSome}

/-! ### 2. Concurrence maximale (Déf. 2.3, prise maximale) -/

/-- `a ∥_q b` maximal : `a ≠ b`, `q·ab` défini et égal à `q·ba`. -/
def maxPar (δ : PAut σ α) (q : σ) (a b : α) : Prop :=
  a ≠ b ∧ (run δ q [a, b]).isSome ∧ run δ q [a, b] = run δ q [b, a]

/-- `a ∥_{q·x} b` : la concurrence maximale après `x` (faux si `x` n'est pas tirable). -/
def parAfter (δ : PAut σ α) (q : σ) (x a b : α) : Prop :=
  a ≠ b ∧ (run δ q [x, a, b]).isSome ∧ run δ q [x, a, b] = run δ q [x, b, a]

instance [DecidableEq σ] [DecidableEq α] (δ : PAut σ α) (q : σ) (a b : α) :
    Decidable (maxPar δ q a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance [DecidableEq σ] [DecidableEq α] (δ : PAut σ α) (q : σ) (x a b : α) :
    Decidable (parAfter δ q x a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- `parAfter` est bien « `q·x` existe et `a ∥ b` en `q·x` ». -/
theorem parAfter_iff (δ : PAut σ α) (q : σ) (x a b : α) :
    parAfter δ q x a b ↔ ∃ q', δ q x = some q' ∧ maxPar δ q' a b := by
  unfold parAfter maxPar
  rw [run_cons δ q x [a, b], run_cons δ q x [b, a]]
  cases δ q x with
  | none => simp
  | some q' => simp

/-- ★ La concurrence maximale est symétrique. -/
theorem maxPar_symm {δ : PAut σ α} {q : σ} {a b : α} (h : maxPar δ q a b) : maxPar δ q b a :=
  ⟨h.1.symm, h.2.2 ▸ h.2.1, h.2.2.symm⟩

/-- ★ La concurrence maximale est irréflexive. -/
theorem maxPar_irrefl (δ : PAut σ α) (q : σ) (a : α) : ¬ maxPar δ q a a := fun h => h.1 rfl

/-- Si `a ∥_q b`, les deux ordres sont définis. -/
theorem maxPar_isSome_swap {δ : PAut σ α} {q : σ} {a b : α} (h : maxPar δ q a b) :
    (run δ q [b, a]).isSome :=
  h.2.2 ▸ h.2.1

/-! ### 3. Axiome du cube (Déf. 2.4) et S2 (Déf. 2.1) -/

/-- Axiome du cube en `q` : `a∥_q c ∧ b∥_q c ∧ a∥_{q·c} b ⟺ a∥_q b ∧ b∥_{q·a} c ∧ a∥_{q·b} c`. -/
def Cube (δ : PAut σ α) (q : σ) (a b c : α) : Prop :=
  (maxPar δ q a c ∧ maxPar δ q b c ∧ parAfter δ q c a b) ↔
    (maxPar δ q a b ∧ parAfter δ q a b c ∧ parAfter δ q b a c)

/-- Automate stablement concurrent (Déf. 2.4), pour la concurrence maximale. -/
def StablyConcurrent (δ : PAut σ α) : Prop := ∀ q a b c, Cube δ q a b c

/-- S2 (Déf. 2.1) en l'état `q = q₀·u`, pour la paire-indépendance `I(u,{x,y}) := x ∥_{q₀·u} y` :
    pour `a, b, c` distincts, `(u,{a,c}) ∈ I ∧ (u.a,{b,c}) ∈ I ⇒
    ((u,{a,b}) ∈ I ⟺ (u.c,{a,b}) ∈ I)`. -/
def S2At (δ : PAut σ α) (q : σ) (a b c : α) : Prop :=
  a ≠ b → b ≠ c → a ≠ c → maxPar δ q a c → parAfter δ q a b c →
    (maxPar δ q a b ↔ parAfter δ q c a b)

/-- S2 en tout état. -/
def S2 (δ : PAut σ α) : Prop := ∀ q a b c, S2At δ q a b c

instance [DecidableEq σ] [DecidableEq α] (δ : PAut σ α) (q : σ) (a b c : α) :
    Decidable (Cube δ q a b c) :=
  inferInstanceAs (Decidable (_ ↔ _))

instance [DecidableEq σ] [DecidableEq α] (δ : PAut σ α) (q : σ) (a b c : α) :
    Decidable (S2At δ q a b c) :=
  inferInstanceAs (Decidable (_ → _ → _ → _ → _ → (_ ↔ _)))

/-! ### 4. Critère du losange partiel (côté Mazurkiewicz) -/

section Diamond

variable {δ : PAut σ α} {I : α → α → Prop}

/-- Échange `I`-indépendant en contexte : le mot lu ne change pas, dans `Option`. -/
theorem run_swap_of_diamond (hD : ∀ q a b, I a b → run δ q [a, b] = run δ q [b, a]) (q : σ)
    (u w : List α) {a b : α} (hab : I a b) :
    run δ q (u ++ a :: b :: w) = run δ q (u ++ b :: a :: w) := by
  rw [run_append, run_append]
  congr 1
  funext q'
  rw [show a :: b :: w = [a, b] ++ w from rfl, show b :: a :: w = [b, a] ++ w from rfl,
    run_append, run_append, hD q' a b hab]

/-- ★ Le langage lu depuis `q` descend sur le monoïde de traces M(α, I). -/
def TraceQ.liftRun (hD : ∀ q a b, I a b → run δ q [a, b] = run δ q [b, a]) (q : σ) :
    TraceQ I → Option σ :=
  Quot.lift (run δ q) (by
    intro _ _ h
    obtain ⟨u, w, a, b, hI⟩ := h
    exact run_swap_of_diamond hD q u w hI)

theorem TraceQ.liftRun_mk (hD : ∀ q a b, I a b → run δ q [a, b] = run δ q [b, a]) (q : σ)
    (l : List α) : TraceQ.liftRun hD q (TraceQ.mk I l) = run δ q l := rfl

/-- ★ Deux mots de même trace sont lus vers le même état (ou tous deux rejetés). -/
theorem run_trace_closed (hD : ∀ q a b, I a b → run δ q [a, b] = run δ q [b, a]) (q : σ)
    {w w' : List α} (h : TraceQ.mk I w = TraceQ.mk I w') : run δ q w = run δ q w' :=
  congrArg (TraceQ.liftRun hD q) h

variable (hirr : ∀ a, ¬ I a a) (hD : ∀ q a b, I a b → run δ q [a, b] = run δ q [b, a])
  (hI : ∀ q a b, maxPar δ q a b → I a b)
include hirr hD hI

/-- Sous le critère, `a ∥_q b ⟺ I a b ∧ q·ab défini`. -/
theorem maxPar_iff_of_diamond (q : σ) (a b : α) :
    maxPar δ q a b ↔ I a b ∧ (run δ q [a, b]).isSome :=
  ⟨fun h => ⟨hI q a b h, h.2.1⟩,
    fun h => ⟨fun hab => hirr a (hab ▸ h.1), h.2, hD q a b h.1⟩⟩

/-- Sous le critère, `a ∥_{q·x} b ⟺ I a b ∧ q·xab défini`. -/
theorem parAfter_iff_of_diamond (q : σ) (x a b : α) :
    parAfter δ q x a b ↔ I a b ∧ (run δ q [x, a, b]).isSome := by
  rw [parAfter_iff]
  constructor
  · rintro ⟨q', hq', hp⟩
    rw [maxPar_iff_of_diamond hirr hD hI] at hp
    refine ⟨hp.1, ?_⟩
    rw [run_cons, hq']
    exact hp.2
  · rintro ⟨hab, hs⟩
    rw [run_cons] at hs
    cases hq : δ q x with
    | none => rw [hq] at hs; exact absurd hs (by simp)
    | some q' =>
      rw [hq] at hs
      exact ⟨q', rfl, (maxPar_iff_of_diamond hirr hD hI q' a b).mpr ⟨hab, hs⟩⟩

omit hirr hI in
/-- Trois lettres deux à deux `I`-indépendantes : les six ordres sont lus vers le même état. -/
theorem run_perm3_of_diamond (q : σ) {a b c : α} (hab : I a b) (hbc : I b c) (hac : I a c) :
    run δ q [b, a, c] = run δ q [a, b, c] ∧ run δ q [a, c, b] = run δ q [a, b, c] ∧
      run δ q [c, a, b] = run δ q [a, b, c] ∧ run δ q [b, c, a] = run δ q [a, b, c] := by
  have s12 : ∀ {x y z : α}, I x y → run δ q [x, y, z] = run δ q [y, x, z] :=
    fun h => run_swap_of_diamond hD q [] _ h
  have s23 : ∀ {x y z : α}, I y z → run δ q [x, y, z] = run δ q [x, z, y] :=
    fun h => run_swap_of_diamond hD q [_] [] h
  exact ⟨(s12 hab).symm, (s23 hbc).symm, ((s23 hbc).trans (s12 hac)).symm,
    ((s12 hab).trans (s23 hac)).symm⟩

/-- ★ Critère du losange : la concurrence maximale vérifie l'axiome du cube. -/
theorem stablyConcurrent_of_diamond : StablyConcurrent δ := by
  intro q a b c
  unfold Cube
  simp only [maxPar_iff_of_diamond hirr hD hI, parAfter_iff_of_diamond hirr hD hI]
  constructor
  · rintro ⟨⟨hac, _⟩, ⟨hbc, _⟩, ⟨hab, hs⟩⟩
    obtain ⟨p1, -, p3, -⟩ := run_perm3_of_diamond hD q hab hbc hac
    rw [p3] at hs
    exact ⟨⟨hab, isSome_of_isSome_append (u := [a, b]) (v := [c]) hs⟩, ⟨hbc, hs⟩,
      ⟨hac, p1 ▸ hs⟩⟩
  · rintro ⟨⟨hab, _⟩, ⟨hbc, hs⟩, ⟨hac, _⟩⟩
    obtain ⟨-, p2, p3, p4⟩ := run_perm3_of_diamond hD q hab hbc hac
    exact ⟨⟨hac, isSome_of_isSome_append (u := [a, c]) (v := [b]) (p2 ▸ hs)⟩,
      ⟨hbc, isSome_of_isSome_append (u := [b, c]) (v := [a]) (p4 ▸ hs)⟩, ⟨hab, p3 ▸ hs⟩⟩

/-- ★ Critère du losange : la paire-indépendance maximale vérifie S2. -/
theorem S2_of_diamond : S2 δ := by
  intro q a b c _ _ _ h1 h2
  rw [maxPar_iff_of_diamond hirr hD hI] at h1 ⊢
  rw [parAfter_iff_of_diamond hirr hD hI] at h2 ⊢
  obtain ⟨hac, -⟩ := h1
  obtain ⟨hbc, hs⟩ := h2
  constructor
  · rintro ⟨hab, -⟩
    exact ⟨hab, (run_perm3_of_diamond hD q hab hbc hac).2.2.1 ▸ hs⟩
  · rintro ⟨hab, -⟩
    exact ⟨hab, isSome_of_isSome_append (u := [a, b]) (v := [c]) hs⟩

end Diamond

/-! ### 5. Critère commutatif -/

/-- Automate partiel commutatif : deux lettres se lisent dans les deux ordres vers le même
    résultat, rejet compris (égalité dans `Option`). -/
def IsCommutativePA (δ : PAut σ α) : Prop := ∀ q a b, run δ q [a, b] = run δ q [b, a]

section Commutative

variable {δ : PAut σ α} (h : IsCommutativePA δ)
include h

/-- Un automate commutatif vérifie le critère du losange pour `I := (· ≠ ·)`. -/
theorem diamond_of_commutative : ∀ q (a b : α), a ≠ b → run δ q [a, b] = run δ q [b, a] :=
  fun q a b _ => h q a b

/-- ★ Les six ordres de trois lettres sont lus vers le même état. -/
theorem run_perm3_of_commutative (q : σ) (a b c : α) :
    run δ q [b, a, c] = run δ q [a, b, c] ∧ run δ q [a, c, b] = run δ q [a, b, c] ∧
      run δ q [c, a, b] = run δ q [a, b, c] ∧ run δ q [b, c, a] = run δ q [a, b, c] ∧
      run δ q [c, b, a] = run δ q [a, b, c] := by
  have s12 : ∀ x y z : α, run δ q [x, y, z] = run δ q [y, x, z] :=
    fun x y z => run_swap_of_diamond (I := fun _ _ => True) (fun q a b _ => h q a b) q [] [z]
      trivial
  have s23 : ∀ x y z : α, run δ q [x, y, z] = run δ q [x, z, y] :=
    fun x y z => run_swap_of_diamond (I := fun _ _ => True) (fun q a b _ => h q a b) q [x] []
      trivial
  exact ⟨(s12 a b c).symm, (s23 a b c).symm, ((s23 a b c).trans (s12 a c b)).symm,
    ((s12 a b c).trans (s23 b a c)).symm,
    ((s23 a b c).trans ((s12 a c b).trans (s23 c a b))).symm⟩

/-- Sous commutativité, `a ∥_q b ⟺ a ≠ b ∧ q·ab défini`. -/
theorem maxPar_iff_of_commutative (q : σ) (a b : α) :
    maxPar δ q a b ↔ a ≠ b ∧ (run δ q [a, b]).isSome :=
  maxPar_iff_of_diamond (fun _ h => h rfl) (diamond_of_commutative h) (fun _ _ _ hp => hp.1) q a b

/-- Sous commutativité, `a ∥_{q·x} b ⟺ a ≠ b ∧ q·xab défini`. -/
theorem parAfter_iff_of_commutative (q : σ) (x a b : α) :
    parAfter δ q x a b ↔ a ≠ b ∧ (run δ q [x, a, b]).isSome :=
  parAfter_iff_of_diamond (fun _ h => h rfl) (diamond_of_commutative h) (fun _ _ _ hp => hp.1)
    q x a b

/-- ★ Un automate partiel commutatif est stablement concurrent (Déf. 2.4). -/
theorem stablyConcurrent_of_commutative : StablyConcurrent δ :=
  stablyConcurrent_of_diamond (fun _ h => h rfl) (diamond_of_commutative h)
    (fun _ _ _ hp => hp.1)

/-- ★ Un automate partiel commutatif vérifie S2 (Déf. 2.1). -/
theorem S2_of_commutative : S2 δ :=
  S2_of_diamond (fun _ h => h rfl) (diamond_of_commutative h) (fun _ _ _ hp => hp.1)

end Commutative

/-! ### 6. Sémantique totale (« tester puis garder ») contre sémantique partielle -/

/-- Automate partiel d'un pas gardé : le rejet rend la lettre non tirable. -/
def ofGated (P : σ → α → Prop) [∀ s a, Decidable (P s a)] (upd : σ → α → σ) : PAut σ α :=
  fun q a => if P q a then some (upd q a) else none

/-- Sémantique totale d'un automate partiel : une lettre non tirable laisse l'état inchangé. -/
def toTotal (δ : PAut σ α) (q : σ) (a : α) : σ := (δ q a).getD q

/-- ★ La sémantique totale du pas gardé partiel est `gatedStep` (« tester puis garder »). -/
theorem toTotal_ofGated (P : σ → α → Prop) [∀ s a, Decidable (P s a)] (upd : σ → α → σ) :
    toTotal (ofGated P upd) = gatedStep P upd := by
  funext q a
  unfold toTotal ofGated gatedStep
  split_ifs <;> rfl

/-! ### 7. Pas gardés partiels : lecture d'une paire, critère de commutativité -/

section Gated

variable {P : σ → α → Prop} [∀ s a, Decidable (P s a)] {upd : σ → α → σ}

/-- Lecture d'une paire par un pas gardé partiel. -/
theorem run_ofGated_pair (q : σ) (a b : α) :
    run (ofGated P upd) q [a, b] =
      if P q a ∧ P (upd q a) b then some (upd (upd q a) b) else none := by
  by_cases ha : P q a <;> by_cases hb : P (upd q a) b <;> simp [run_cons, ofGated, ha, hb]

theorem isSome_run_ofGated_pair (q : σ) (a b : α) :
    (run (ofGated P upd) q [a, b]).isSome ↔ P q a ∧ P (upd q a) b := by
  rw [run_ofGated_pair]
  split_ifs with h <;> simp [h]

/-- ★ Critère des pas gardés : si les mises à jour commutent et si la tirabilité de `ab`
    entraîne celle de `ba`, l'automate partiel est commutatif. -/
theorem isCommutativePA_ofGated (h_upd : ∀ q a b, upd (upd q a) b = upd (upd q b) a)
    (h_P : ∀ q a b, P q a ∧ P (upd q a) b → P q b ∧ P (upd q b) a) :
    IsCommutativePA (ofGated P upd) := fun q a b => by
  rw [run_ofGated_pair, run_ofGated_pair, h_upd]
  exact if_congr ⟨h_P q a b, h_P q b a⟩ rfl rfl

/-- Concurrence maximale d'un pas gardé partiel : les deux ordres passent leurs tests et mènent
    au même état. -/
theorem maxPar_ofGated_iff (q : σ) (a b : α) :
    maxPar (ofGated P upd) q a b ↔
      a ≠ b ∧ (P q a ∧ P (upd q a) b) ∧ (P q b ∧ P (upd q b) a) ∧
        upd (upd q a) b = upd (upd q b) a := by
  unfold maxPar
  rw [run_ofGated_pair, run_ofGated_pair]
  by_cases h1 : P q a ∧ P (upd q a) b <;> by_cases h2 : P q b ∧ P (upd q b) a
  · rw [if_pos h1, if_pos h2]
    simp [h1, h2]
  · rw [if_pos h1, if_neg h2]
    simp [h2]
  · rw [if_neg h1]
    simp [h1]
  · rw [if_neg h1]
    simp [h1]

/-- Mises à jour commutatives : la concurrence maximale ne lit que les tests. -/
theorem maxPar_ofGated_iff_of_comm (hc : IsCommutativeUpdate upd) (q : σ) (a b : α) :
    maxPar (ofGated P upd) q a b ↔
      a ≠ b ∧ (P q a ∧ P (upd q a) b) ∧ (P q b ∧ P (upd q b) a) := by
  rw [maxPar_ofGated_iff]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1⟩, fun h => ⟨h.1, h.2.1, h.2.2, hc q a b⟩⟩

end Gated

/-- Un automate partiel commutatif est stablement concurrent et vérifie S2. -/
theorem stable_of_commutative {σ α : Type*} {δ : PAut σ α} (h : IsCommutativePA δ) :
    StablyConcurrent δ ∧ S2 δ :=
  ⟨stablyConcurrent_of_commutative h, S2_of_commutative h⟩

/-! ### 8. Cohérence d'échange et projections -/

section Projections

variable {τ : Type*}

/-- Cohérence d'échange : quand les deux ordres de deux lettres sont définis, ils mènent au même
    état. -/
def SwapCoherent (δ : PAut σ α) : Prop :=
  ∀ q a b, (run δ q [a, b]).isSome → (run δ q [b, a]).isSome → run δ q [a, b] = run δ q [b, a]

/-- Un pas gardé à mises à jour commutatives est cohérent pour l'échange. -/
theorem swapCoherent_ofGated {P : σ → α → Prop} [∀ s a, Decidable (P s a)] {upd : σ → α → σ}
    (hc : IsCommutativeUpdate upd) : SwapCoherent (ofGated P upd) := by
  intro q a b h1 h2
  rw [run_ofGated_pair] at h1 h2 ⊢
  rw [run_ofGated_pair]
  by_cases g1 : P q a ∧ P (upd q a) b
  · by_cases g2 : P q b ∧ P (upd q b) a
    · rw [if_pos g1, if_pos g2, hc q a b]
    · rw [if_neg g2] at h2
      exact absurd h2 (by simp)
  · rw [if_neg g1] at h1
    exact absurd h1 (by simp)

section Coherent

variable {δ : PAut σ α} (hd : SwapCoherent δ)
include hd

/-- Sous cohérence d'échange, `a ∥_q b ⟺ a ≠ b ∧ q·ab et q·ba définis`. -/
theorem maxPar_iff_isSome (q : σ) (a b : α) :
    maxPar δ q a b ↔ a ≠ b ∧ (run δ q [a, b]).isSome ∧ (run δ q [b, a]).isSome :=
  ⟨fun h => ⟨h.1, h.2.1, maxPar_isSome_swap h⟩, fun h => ⟨h.1, h.2.1, hd q a b h.2.1 h.2.2⟩⟩

/-- Sous cohérence d'échange, `a ∥_{q·x} b ⟺ a ≠ b ∧ q·xab et q·xba définis`. -/
theorem parAfter_iff_isSome (q : σ) (x a b : α) :
    parAfter δ q x a b ↔ a ≠ b ∧ (run δ q [x, a, b]).isSome ∧ (run δ q [x, b, a]).isSome := by
  rw [parAfter_iff, run_cons δ q x [a, b], run_cons δ q x [b, a]]
  cases δ q x with
  | none => simp
  | some q' => simp [maxPar_iff_isSome hd]

end Coherent

/-- Projection : `π` envoie chaque transition de `δ` sur une transition de `δ'`, et chaque rejet
    sur un rejet. -/
def ProjectsTo (π : σ → τ) (δ : PAut σ α) (δ' : PAut τ α) : Prop :=
  ∀ q a, (δ q a).map π = δ' (π q) a

section Projection

variable {π : σ → τ} {δ : PAut σ α} {δ' : PAut τ α}

/-- Une projection commute avec la lecture des mots. -/
theorem run_map_of_projectsTo (h : ProjectsTo π δ δ') :
    ∀ (q : σ) (w : List α), (run δ q w).map π = run δ' (π q) w
  | _, [] => rfl
  | q, a :: w => by
    rw [run_cons, run_cons, ← h q a]
    cases δ q a with
    | none => rfl
    | some q' => exact run_map_of_projectsTo h q' w

/-- Une projection préserve le langage depuis chaque état. -/
theorem isSome_run_of_projectsTo (h : ProjectsTo π δ δ') (q : σ) (w : List α) :
    (run δ q w).isSome = (run δ' (π q) w).isSome := by
  rw [← run_map_of_projectsTo h, Option.isSome_map]

variable (hd : SwapCoherent δ) (hd' : SwapCoherent δ') (h : ProjectsTo π δ δ')
include hd hd' h

/-- ★ Le cube en `q` ne dépend que du langage depuis `q` : il passe à travers une projection. -/
theorem cube_iff_of_projectsTo (q : σ) (a b c : α) : Cube δ q a b c ↔ Cube δ' (π q) a b c := by
  simp only [Cube, maxPar_iff_isSome hd, maxPar_iff_isSome hd', parAfter_iff_isSome hd,
    parAfter_iff_isSome hd', isSome_run_of_projectsTo h q]

/-- ★ S2 en `q` passe à travers une projection. -/
theorem S2At_iff_of_projectsTo (q : σ) (a b c : α) : S2At δ q a b c ↔ S2At δ' (π q) a b c := by
  simp only [S2At, maxPar_iff_isSome hd, maxPar_iff_isSome hd', parAfter_iff_isSome hd,
    parAfter_iff_isSome hd', isSome_run_of_projectsTo h q]

variable (hs : Function.Surjective π)
include hs

/-- Projection surjective : stabilité de part et d'autre. -/
theorem stablyConcurrent_iff_of_projectsTo : StablyConcurrent δ ↔ StablyConcurrent δ' := by
  refine ⟨fun H q' a b c => ?_, fun H q a b c => ?_⟩
  · obtain ⟨q, rfl⟩ := hs q'
    exact (cube_iff_of_projectsTo hd hd' h q a b c).mp (H q a b c)
  · exact (cube_iff_of_projectsTo hd hd' h q a b c).mpr (H (π q) a b c)

theorem S2_iff_of_projectsTo : S2 δ ↔ S2 δ' := by
  refine ⟨fun H q' a b c => ?_, fun H q a b c => ?_⟩
  · obtain ⟨q, rfl⟩ := hs q'
    exact (S2At_iff_of_projectsTo hd hd' h q a b c).mp (H q a b c)
  · exact (S2At_iff_of_projectsTo hd hd' h q a b c).mpr (H (π q) a b c)

end Projection

end Projections

/-! ### 9. États accessibles -/

/-- Un invariant stable par les transitions vaut sur tous les états accessibles. -/
theorem run_inv {δ : PAut σ α} {Inv : σ → Prop}
    (hstep : ∀ q a q', Inv q → δ q a = some q' → Inv q') :
    ∀ (w : List α) (q q' : σ), Inv q → run δ q w = some q' → Inv q'
  | [], q, q', hq, h => by
    cases (Option.some.inj h)
    exact hq
  | a :: w, q, q', hq, h => by
    rw [run_cons] at h
    cases ha : δ q a with
    | none => rw [ha] at h; cases h
    | some q₁ => rw [ha] at h; exact run_inv hstep w q₁ q' (hstep q a q₁ hq ha) h

/-- Invariant fini et stable : l'ensemble des états accessibles est fini. -/
theorem reachable_finite_of_inv {δ : PAut σ α} {Inv : σ → Prop} {q₀ : σ}
    (hfin : {q | Inv q}.Finite) (h0 : Inv q₀)
    (hstep : ∀ q a q', Inv q → δ q a = some q' → Inv q') :
    {q | ∃ w, run δ q₀ w = some q}.Finite :=
  hfin.subset fun _ ⟨w, hw⟩ => run_inv hstep w q₀ _ h0 hw

/-- Pli d'un pas `Option` à état mort `none` : c'est la lecture de l'automate partiel induit. -/
theorem foldl_eq_run (f : Option σ → α → Option σ) (hf : ∀ a, f none a = none) :
    ∀ (w : List α) (q : σ), w.foldl f (some q) = run (fun q a => f (some q) a) q w
  | [], _ => rfl
  | a :: w, q => by
    have hnone : ∀ w : List α, w.foldl f none = none := by
      intro w
      induction w with
      | nil => rfl
      | cons b w ih => rw [List.foldl_cons, hf, ih]
    rw [List.foldl_cons, run_cons]
    cases f (some q) a with
    | none => exact hnone w
    | some q' => exact foldl_eq_run f hf w q'

end LocalTraceLang
