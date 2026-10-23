/-
  ThesePlanetaire/LedgerClock.lean
  Phase 8 (2026-10-02) : l'horloge du grand livre — top de période par mémoire, pont
  `canonStep ↔ planetStep`, classe de tout profil, stabilité (C5), cliquet (P2-12).

  Développé d'abord en `LedgerClock_scratch.lean` (workflow du dépôt). Plan :
  `~/.claude/plans/witty-dazzling-manatee.md` (Phase 8) ; analyse :
  `cache/analyse_phase8_horloge_grand_livre_2026-10-02.md`.

  Le grand livre planétaire (`PlanetaryLedger`) n'a pas d'horloge : tout y est « stock » (défaut
  D10). Ce module lui ajoute le top de période par `TokenizedCommons.withTick`, avec un effet
  par mémoire (`tickStock`, plafond = stock initial `S₀`). Sur la composante environnementale
  (montants nuls) d'une frontière isolée (`atBoundary`, qui est `BoundaryLedgerBridge.ledgerAt`
  sous la garde du profil gouverné) :
  1. ★ `clockStep_projects` : sous soldes ≥ 0 et `ClockInv`, la charge `S₀ − s` suit exactement
     `FeedbackClass.canonStep` ; en sémantique partielle, `clockP_projectsOn` ;
  2. ★ `clock_profileClass_sound`, `ledger_realizes_profile` : le grand livre horodaté réalise la
     classe de TOUT profil ; `physicsProfile_ledger_clock` est la contrepartie positive de
     `BoundaryLedgerBridge.physicsProfile_not_ledger` ;
  3. ★ `clock_T5_iff` : T5 ⟺ règlements commutatifs — libre, Parikh par période
     (`clock_period_perm_invariant`) ; gardé avec contention, pas de T5 ;
  4. ★ stabilité de Husson–Morin (C5) : stock stable en tout état, flow stable sur `ClockInv`
     (`clock_flow_stableOn`), regen non (`clock_regen_not_stable`) ; sur le modèle canonique,
     ★ `flow_regen_split` tranche D9 : même classe, stabilité différente ;
  5. ★ cliquet de seuil (P2-12), hors `Memory` : `ratchet_ne_tickOp`, `ratchet_not_stable`.

  Outil générique (§3) : transport du cube et de S2 par projection sur un invariant, fidèle sur
  les paires (`cube_iff_of_projectsOn`). `LocalTraceLang.cube_iff_of_projectsTo` exige la
  cohérence d'échange, qu'aucun automate à top non trivial ne vérifie.
-/

import ThesePlanetaire.BoundaryLedgerBridge
import ThesePlanetaire.TokenizedCommons
import ThesePlanetaire.DepletionStable

namespace LedgerClock

open LocalTraceLang
open FeedbackClass (FClass SemClass Memory Governance profileClass tickOp emitOp canonStep
  canonSupp DisjointFoot single_coord_not_D)
open CommutativeClassification (IsCommutativeUpdate commutative_implies_perm_invariant)
open GatedStep (Diamond)
open PlanetaryLedger (Footprint PState planetStep planetUpd planetAdmissible stockAdmissible
  gsupp deplete I_planet planetStep_comm planetStep_of_adm ledgerAdmissible_zero)
open TokenizedCommons (withTick liftOpt I_tick withTick_diamond diamond_withTick_iff)
open DepletionStable (stockP stock_commutative)
open FeedbackPlanetary (planet_feedback_class pay_zero)
open PlanetaryBoundaries (PlanetaryBoundary memoryOf isBudgeted ParikhProfile physicsProfile
  governedProfile ledgerProfile parikhClassIn)
open BoundaryLedgerBridge (ledgerAt ledgerAt_gated physicsProfile_not_ledger)

/-! ### 1. Top de période du grand livre -/

section Clock

variable {V B : Type*} [DecidableEq V] [DecidableEq B]

/-- Effet du top de période sur un stock, en forme « budget restant » de plafond `S₀` (le stock
    initial) : `stock` le conserve, `regen` lui rend `r` sans dépasser `S₀`, `flow` le remet à
    `S₀`. Miroir de `FeedbackClass.tickOp` sur la charge `S₀ - s` (`tickStock_load`). -/
def tickStock : Memory → ℕ → ℤ → ℤ → ℤ
  | .stock, _, _, s => s
  | .regen, r, S₀, s => min (s + r) S₀
  | .flow, _, S₀, _ => S₀

/-- Top de période sur toutes les frontières, chacune selon sa mémoire. -/
def tickStocks (mem : B → Memory) (r : B → ℕ) (S₀ : B → ℤ) (stock : B → ℤ) : B → ℤ :=
  fun c => tickStock (mem c) (r c) (S₀ c) (stock c)

/-- Top de période du grand livre : les stocks seuls bougent ; soldes et admis sont inchangés. -/
def tickLedger (mem : B → Memory) (r : B → ℕ) (S₀ : B → ℤ) (st : PState V B) : PState V B :=
  ⟨st.bal, tickStocks mem r S₀ st.stock, st.adm⟩

/-- ★ Grand livre planétaire horodaté (composante environnementale, montants nuls) : `some e`
    règle `e` (`planetStep 0`), `none` est le top de période, inerte sans horloge. -/
def clockStep (clock : Bool) (mem : B → Memory) (r : B → ℕ) (S₀ : B → ℤ) (fp : Footprint V B) :
    PState V B → Option (V × V) → PState V B :=
  withTick (planetStep 0 fp) (if clock then tickLedger mem r S₀ else id)

/-- Empreinte d'une seule frontière `b` : émissions de `b` seules, garde `{b}` si `b` est gardée. -/
def atBoundary (emit : V × V → B → ℤ) (b : B) (gov : Governance) : Footprint V B :=
  ⟨fun e c => if c = b then emit e c else 0, if gov = .gated then {b} else ∅⟩

end Clock

/-- ★ Le grand livre d'une frontière (`BoundaryLedgerBridge.ledgerAt`) est l'empreinte
    `atBoundary` sous la gouvernance du profil gouverné (les frontières budgétées sont gardées). -/
theorem ledgerAt_eq_atBoundary {V : Type*} (emit : V × V → PlanetaryBoundary → ℤ)
    (b : PlanetaryBoundary) : ledgerAt emit b = atBoundary emit b (governedProfile.gov b) := by
  have key : ∀ fp : Footprint V PlanetaryBoundary, fp = ⟨fp.emit, fp.gated⟩ := fun _ => rfl
  rw [key (ledgerAt emit b), ledgerAt_gated]
  cases hb : isBudgeted b <;> simp only [atBoundary, governedProfile, hb] <;> rfl

/-! ### 2. Modèles canoniques partiels -/

section Canon

variable {α : Type*}

/-- Une charge supplémentaire `k` passe la garde depuis `L`. -/
def fits (gov : Governance) (cap L k : ℕ) : Prop := gov = .gated → L + k ≤ cap

instance (gov : Governance) (cap L k : ℕ) : Decidable (fits gov cap L k) :=
  inferInstanceAs (Decidable (_ → _))

/-- Modèle canonique en sémantique partielle : le top (`none`) applique `tick` et est toujours
    tirable ; une émission gardée qui dépasserait `cap` n'est pas tirable. -/
def canonPA (tick : ℕ → ℕ) (gov : Governance) (e : α → ℕ) (cap : ℕ) : PAut ℕ (Option α)
  | L, none => some (tick L)
  | L, some a => if fits gov cap L (e a) then some (L + e a) else none

variable {tick : ℕ → ℕ} {gov : Governance} {e : α → ℕ} {cap : ℕ}

@[simp] lemma canonPA_none (L : ℕ) : canonPA tick gov e cap L none = some (tick L) := rfl

lemma canonPA_some (L : ℕ) (a : α) :
    canonPA tick gov e cap L (some a) = if fits gov cap L (e a) then some (L + e a) else none :=
  rfl

lemma fits_add (L k k' : ℕ) :
    fits gov cap L k ∧ fits gov cap (L + k) k' ↔ fits gov cap L (k + k') := by
  cases gov
  · simp [fits]
  · simp only [fits, forall_const]
    omega

/-- Deux émissions : la paire est lisible ssi la charge totale passe la garde. -/
lemma run_some_some (L : ℕ) (a b : α) :
    run (canonPA tick gov e cap) L [some a, some b] =
      if fits gov cap L (e a + e b) then some (L + e a + e b) else none := by
  have hf := fits_add (gov := gov) (cap := cap) L (e a) (e b)
  simp only [run_cons, canonPA_some, run_nil]
  by_cases h : fits gov cap L (e a + e b)
  · obtain ⟨h1, h2⟩ := hf.mpr h
    simp [h1, h2, h]
  · by_cases h1 : fits gov cap L (e a)
    · have h2 : ¬ fits gov cap (L + e a) (e b) := fun h2 => h (hf.mp ⟨h1, h2⟩)
      simp [h1, h2, h]
    · simp [h1, h]

lemma run_some_none (L : ℕ) (a : α) :
    run (canonPA tick gov e cap) L [some a, none] =
      if fits gov cap L (e a) then some (tick (L + e a)) else none := by
  simp only [run_cons, canonPA_some, canonPA_none, run_nil]
  by_cases h1 : fits gov cap L (e a) <;> simp [h1]

lemma run_none_some (L : ℕ) (a : α) :
    run (canonPA tick gov e cap) L [none, some a] =
      if fits gov cap (tick L) (e a) then some (tick L + e a) else none := by
  simp only [run_cons, canonPA_some, canonPA_none, run_nil]
  by_cases h1 : fits gov cap (tick L) (e a) <;> simp [h1]

/-- Deux émissions distinctes sont concurrentes ssi leur charge totale passe la garde. -/
lemma maxPar_some_some (L : ℕ) (a b : α) :
    maxPar (canonPA tick gov e cap) L (some a) (some b) ↔
      a ≠ b ∧ fits gov cap L (e a + e b) := by
  unfold maxPar
  rw [run_some_some, run_some_some, add_comm (e b) (e a), Nat.add_right_comm L (e b) (e a)]
  by_cases h : fits gov cap L (e a + e b) <;> simp [h]

lemma maxPar_none_none (L : ℕ) : ¬ maxPar (canonPA tick gov e cap) L none none :=
  maxPar_irrefl _ L none

lemma parAfter_none (L : ℕ) (a b : Option α) :
    parAfter (canonPA tick gov e cap) L none a b ↔ maxPar (canonPA tick gov e cap) (tick L) a b := by
  rw [parAfter_iff]
  simp

lemma parAfter_some (L : ℕ) (x : α) (a b : Option α) :
    parAfter (canonPA tick gov e cap) L (some x) a b ↔
      fits gov cap L (e x) ∧ maxPar (canonPA tick gov e cap) (L + e x) a b := by
  rw [parAfter_iff, canonPA_some]
  by_cases h : fits gov cap L (e x) <;> simp [h]

/-- Une émission et le top sont concurrents ssi les deux ordres sont tirables et mènent à la
    même charge. -/
lemma maxPar_some_none (L : ℕ) (a : α) :
    maxPar (canonPA tick gov e cap) L (some a) none ↔
      fits gov cap L (e a) ∧ fits gov cap (tick L) (e a) ∧ tick (L + e a) = tick L + e a := by
  unfold maxPar
  rw [run_some_none, run_none_some]
  by_cases h1 : fits gov cap L (e a) <;> by_cases h2 : fits gov cap (tick L) (e a) <;>
    simp [h1, h2]

lemma maxPar_none_some (L : ℕ) (a : α) :
    maxPar (canonPA tick gov e cap) L none (some a) ↔
      maxPar (canonPA tick gov e cap) L (some a) none :=
  ⟨maxPar_symm, maxPar_symm⟩

/-- La sémantique totale du modèle partiel est le pas canonique avec horloge. -/
theorem toTotal_canonPA (mem : Memory) (gov : Governance) (e : α → ℕ) (cap r : ℕ) :
    toTotal (canonPA (tickOp mem r) gov e cap) = canonStep true mem gov e cap r := by
  funext L x
  cases x with
  | none => rfl
  | some a =>
    simp only [toTotal, canonPA_some, canonStep, emitOp]
    cases gov <;> by_cases h : L + e a ≤ cap <;> simp [fits, h]

/-- Stock : le top est l'identité, le modèle partiel est commutatif. -/
theorem canon_stock_commutative (r : ℕ) : IsCommutativePA (canonPA (tickOp .stock r) gov e cap) := by
  intro L x y
  rcases x with _ | a <;> rcases y with _ | b
  · rfl
  · rw [run_none_some, run_some_none]; rfl
  · rw [run_none_some, run_some_none]; rfl
  · rw [run_some_some, run_some_some, add_comm (e b) (e a), Nat.add_right_comm L (e b) (e a)]

/-- Stock : stablement concurrent et S2, en tout état. -/
theorem canon_stock_stable (r : ℕ) :
    StablyConcurrent (canonPA (tickOp .stock r) gov e cap) ∧
      S2 (canonPA (tickOp .stock r) gov e cap) :=
  stable_of_commutative (canon_stock_commutative r)

/-- Flow : une émission est concurrente du top ssi elle est nulle et tirable. -/
lemma maxPar_flow_some_none (r L : ℕ) (a : α) :
    maxPar (canonPA (tickOp .flow r) gov e cap) L (some a) none ↔
      fits gov cap L 0 ∧ e a = 0 := by
  rw [maxPar_some_none]
  simp only [tickOp]
  cases gov
  · simp [fits, eq_comm]
  · simp only [fits, forall_const]
    omega

lemma maxPar_flow_none_some (r L : ℕ) (a : α) :
    maxPar (canonPA (tickOp .flow r) gov e cap) L none (some a) ↔
      fits gov cap L 0 ∧ e a = 0 :=
  ⟨fun h => (maxPar_flow_some_none r L a).mp (maxPar_symm h),
    fun h => maxPar_symm ((maxPar_flow_some_none r L a).mpr h)⟩

/-- Flow : le cube en tout état. Cas finis (trois lettres, au plus un top), clos par `grind`. -/
theorem canon_flow_cube (r : ℕ) (L : ℕ) (a b c : Option α) :
    Cube (canonPA (tickOp .flow r) gov e cap) L a b c := by
  unfold Cube
  rcases a with _ | a <;> rcases b with _ | b <;> rcases c with _ | c <;>
    simp only [parAfter_none, parAfter_some, maxPar_some_some, maxPar_flow_some_none,
      maxPar_flow_none_some, maxPar_none_none, false_and, and_false, tickOp] <;>
    cases gov <;> simp [fits] <;> grind

/-- Flow : S2 en tout état. -/
theorem canon_flow_S2At (r : ℕ) (L : ℕ) (a b c : Option α) :
    S2At (canonPA (tickOp .flow r) gov e cap) L a b c := by
  unfold S2At
  rcases a with _ | a <;> rcases b with _ | b <;> rcases c with _ | c <;>
    simp only [parAfter_none, parAfter_some, maxPar_some_some, maxPar_flow_some_none,
      maxPar_flow_none_some, maxPar_none_none, and_false, tickOp] <;>
    cases gov <;> simp [fits] <;> grind

/-- ★ Flow : le modèle canonique partiel est stablement concurrent et vérifie S2, en tout état,
    sans hypothèse sur les émissions ni le plafond. -/
theorem canon_flow_stable (r : ℕ) :
    StablyConcurrent (canonPA (tickOp .flow r) gov e cap) ∧
      S2 (canonPA (tickOp .flow r) gov e cap) :=
  ⟨canon_flow_cube r, canon_flow_S2At r⟩

/-- ★ Regen rompt le cube : deux émissions unitaires, plafond 2, régénération 1, depuis la
    charge 0, avec ou sans garde. `x ∥ y` et chacune commute avec le top après l'autre, mais
    aucune ne commute avec le top depuis 0 (la troncature `0 - 1 = 0` absorbe la
    régénération). -/
theorem canon_regen_not_cube {x y : α} (hxy : x ≠ y) (hx : e x = 1) (hy : e y = 1) :
    ¬ Cube (canonPA (tickOp .regen 1) gov e 2) 0 (some x) (some y) none := by
  unfold Cube
  simp only [parAfter_none, parAfter_some, maxPar_some_some, maxPar_some_none, tickOp, hx, hy]
  cases gov <;> simp [fits, hxy]

/-- ★ D9 tranché : flow et regen ont la même classe (`profileClass`), mais pas la même
    stabilité. Flow est stable pour toutes émissions, tout plafond et toute régénération ;
    regen ne l'est pas dès deux émissions unitaires distinctes (plafond 2, `r = 1`). -/
theorem flow_regen_split {x y : α} (hxy : x ≠ y) (hx : e x = 1) (hy : e y = 1) :
    profileClass true .flow gov = profileClass true .regen gov ∧
    (∀ (e' : α → ℕ) (cap' r : ℕ), StablyConcurrent (canonPA (tickOp .flow r) gov e' cap') ∧
      S2 (canonPA (tickOp .flow r) gov e' cap')) ∧
    ¬ StablyConcurrent (canonPA (tickOp .regen 1) gov e 2) :=
  ⟨by cases gov <;> rfl, fun _ _ r => canon_flow_stable r,
    fun h => canon_regen_not_cube hxy hx hy (h 0 _ _ _)⟩

end Canon

/-! ### 3. Projection du grand livre horodaté sur le modèle canonique -/

section Transport

variable {σ τ α : Type*}

/-- Projection sur un invariant : `Inv` est stable par les transitions, et sur `Inv` chaque
    transition (ou rejet) de `δ` s'envoie par `π` sur celle de `δ'`. -/
def ProjectsOn (Inv : σ → Prop) (π : σ → τ) (δ : PAut σ α) (δ' : PAut τ α) : Prop :=
  (∀ q a q', Inv q → δ q a = some q' → Inv q') ∧ ∀ q a, Inv q → (δ q a).map π = δ' (π q) a

/-- Fidélité sur les paires : depuis `Inv`, deux ordres définis d'une paire de même image par
    `π` mènent au même état. Remplace la cohérence d'échange (`SwapCoherent`), qu'aucun
    automate à top non trivial ne vérifie. -/
def PairFaithful (Inv : σ → Prop) (π : σ → τ) (δ : PAut σ α) : Prop :=
  ∀ q a b q₁ q₂, Inv q → run δ q [a, b] = some q₁ → run δ q [b, a] = some q₂ →
    π q₁ = π q₂ → q₁ = q₂

variable {Inv : σ → Prop} {π : σ → τ} {δ : PAut σ α} {δ' : PAut τ α}

lemma run_pair_eq_some {q q₂ : σ} {a b : α} (h : run δ q [a, b] = some q₂) :
    ∃ q₁, δ q a = some q₁ ∧ δ q₁ b = some q₂ := by
  rw [run_cons] at h
  cases ha : δ q a with
  | none => rw [ha] at h; cases h
  | some q₁ => rw [ha] at h; exact ⟨q₁, rfl, by simpa using h⟩

/-- Une projection sur invariant commute avec la lecture des mots depuis `Inv`. -/
theorem run_map_of_projectsOn (h : ProjectsOn Inv π δ δ') :
    ∀ (w : List α) (q : σ), Inv q → (run δ q w).map π = run δ' (π q) w
  | [], _, _ => rfl
  | a :: w, q, hq => by
    rw [run_cons, run_cons, ← h.2 q a hq]
    cases ha : δ q a with
    | none => rfl
    | some q' => exact run_map_of_projectsOn h w q' (h.1 q a q' hq ha)

variable (h : ProjectsOn Inv π δ δ') (hf : PairFaithful Inv π δ)
include h hf

theorem maxPar_iff_of_projectsOn {q : σ} (hq : Inv q) (a b : α) :
    maxPar δ q a b ↔ maxPar δ' (π q) a b := by
  unfold maxPar
  rw [← run_map_of_projectsOn h _ q hq, ← run_map_of_projectsOn h _ q hq]
  constructor
  · rintro ⟨hab, hs, he⟩
    exact ⟨hab, by simpa using hs, by rw [he]⟩
  · rintro ⟨hab, hs, he⟩
    refine ⟨hab, by simpa using hs, ?_⟩
    cases h1 : run δ q [a, b] with
    | none => rw [h1] at hs; simp at hs
    | some q₁ =>
      cases h2 : run δ q [b, a] with
      | none => rw [h1, h2] at he; simp at he
      | some q₂ =>
        rw [h1, h2, Option.map_some, Option.map_some, Option.some.injEq] at he
        rw [hf q a b q₁ q₂ hq h1 h2 he]

theorem parAfter_iff_of_projectsOn {q : σ} (hq : Inv q) (x a b : α) :
    parAfter δ q x a b ↔ parAfter δ' (π q) x a b := by
  rw [parAfter_iff, parAfter_iff, ← h.2 q x hq]
  cases hx : δ q x with
  | none => simp
  | some q' => simp [maxPar_iff_of_projectsOn h hf (h.1 q x q' hq hx) a b]

/-- ★ Le cube passe à travers une projection sur invariant fidèle sur les paires. -/
theorem cube_iff_of_projectsOn {q : σ} (hq : Inv q) (a b c : α) :
    Cube δ q a b c ↔ Cube δ' (π q) a b c := by
  simp only [Cube, maxPar_iff_of_projectsOn h hf hq, parAfter_iff_of_projectsOn h hf hq]

/-- ★ S2 passe à travers une projection sur invariant fidèle sur les paires. -/
theorem S2At_iff_of_projectsOn {q : σ} (hq : Inv q) (a b c : α) :
    S2At δ q a b c ↔ S2At δ' (π q) a b c := by
  simp only [S2At, maxPar_iff_of_projectsOn h hf hq, parAfter_iff_of_projectsOn h hf hq]

omit hf in
/-- Sémantique totale : la projection envoie le pas « tester puis garder » de `δ` sur celui
    de `δ'`. -/
theorem toTotal_of_projectsOn {q : σ} (hq : Inv q) (a : α) :
    π (toTotal δ q a) = toTotal δ' (π q) a := by
  unfold toTotal
  rw [← h.2 q a hq]
  cases δ q a <;> rfl

end Transport

section LedgerProjection

variable {V B : Type*} [DecidableEq B]

/-- Stocks planétaires seuls, avec top : `stockP` pour les paiements, `tickStocks` au top. -/
def clockP (mem : B → Memory) (r : B → ℕ) (S₀ : B → ℤ) (fp : Footprint V B) :
    PAut (B → ℤ) (Option (V × V))
  | s, none => some (tickStocks mem r S₀ s)
  | s, some e => stockP fp s e

/-- Charge de la frontière `b` : ce qui a été prélevé sur le stock initial. -/
def loadAt (S₀ : B → ℤ) (b : B) (s : B → ℤ) : ℕ := (S₀ b - s b).toNat

/-- Invariant de projection : le stock de `b` ne dépasse pas `S₀ b`, et reste ≥ 0 si `b` est
    gardée. Hors de lui, la projection échoue (émission libre au-dessus du plafond ; émission
    nulle gardée sous 0, admise par le grand livre mais non par le modèle canonique). -/
def ClockInv (S₀ : B → ℤ) (b : B) (gov : Governance) (s : B → ℤ) : Prop :=
  s b ≤ S₀ b ∧ (gov = .gated → 0 ≤ s b)

/-- Le top du stock est celui de la charge : `S₀ − min(s + r, S₀) = (S₀ − s) − r`, tronqué. -/
lemma tickStock_load (mem : Memory) (r : ℕ) {S₀ s : ℤ} (hs : s ≤ S₀) :
    (S₀ - tickStock mem r S₀ s).toNat = tickOp mem r (S₀ - s).toNat := by
  cases mem <;> simp only [tickStock, tickOp] <;> omega

lemma stockAdmissible_atBoundary (emit : V × V → B → ℤ) (b : B) (gov : Governance)
    (s : B → ℤ) (e : V × V) :
    stockAdmissible (atBoundary emit b gov) s e ↔
      (gov = .gated → emit e b ≠ 0 → emit e b ≤ s b) := by
  cases gov <;> simp [stockAdmissible, gsupp, atBoundary]

lemma deplete_atBoundary (emit : V × V → B → ℤ) (b : B) (gov : Governance) (s : B → ℤ)
    (e : V × V) (c : B) :
    deplete (atBoundary emit b gov) e s c = if c = b then s c - emit e c else s c := by
  by_cases hc : c = b <;> simp [deplete, atBoundary, hc]

variable {mem : B → Memory} {r : B → ℕ} {S₀ : B → ℤ} {emit : V × V → B → ℤ} {b : B}
  {gov : Governance}

/-- ★ Le grand livre horodaté (stocks seuls) se projette sur le modèle canonique de `b` :
    charge `loadAt`, émissions `emit · b`, plafond `S₀ b`, top `tickOp (mem b) (r b)`. -/
theorem clockP_projectsOn (hS : 0 ≤ S₀ b) (he : ∀ e, 0 ≤ emit e b) :
    ProjectsOn (ClockInv S₀ b gov) (loadAt S₀ b) (clockP mem r S₀ (atBoundary emit b gov))
      (canonPA (tickOp (mem b) (r b)) gov (fun e => (emit e b).toNat) (S₀ b).toNat) := by
  refine ⟨fun s x s' hs hx => ?_, fun s x hs => ?_⟩
  · obtain ⟨h1, h2⟩ := hs
    rcases x with _ | e
    · cases hx
      refine ⟨?_, fun hg => ?_⟩
      · simp only [tickStocks]
        cases mem b <;> simp only [tickStock] <;> omega
      · have := h2 hg
        simp only [tickStocks]
        cases mem b <;> simp only [tickStock] <;> omega
    · simp only [clockP, stockP, ofGated] at hx
      split_ifs at hx with hadm
      cases hx
      rw [stockAdmissible_atBoundary] at hadm
      have := he e
      refine ⟨?_, fun hg => ?_⟩ <;> rw [deplete_atBoundary, if_pos rfl]
      · omega
      · have := hadm hg; have := h2 hg; omega
  · obtain ⟨h1, h2⟩ := hs
    rcases x with _ | e
    · simp only [clockP, Option.map_some, canonPA_none, loadAt, tickStocks]
      rw [tickStock_load _ _ h1]
    · simp only [clockP, stockP, ofGated, canonPA_some, loadAt]
      have := he e
      have hval : loadAt S₀ b (deplete (atBoundary emit b gov) e s) =
          (S₀ b - s b).toNat + (emit e b).toNat := by
        unfold loadAt
        rw [deplete_atBoundary, if_pos rfl]
        omega
      by_cases hadm : stockAdmissible (atBoundary emit b gov) s e
      · rw [if_pos hadm, Option.map_some, hval, if_pos]
        rw [stockAdmissible_atBoundary] at hadm
        intro hg; have := hadm hg; have := h2 hg; omega
      · rw [if_neg hadm, if_neg]; · rfl
        rw [stockAdmissible_atBoundary] at hadm
        intro hf; apply hadm; intro hg _; have := hf hg; have := h2 hg; omega

/-- Le top et les paiements de `atBoundary` agissent hors de `b` par le seul top. -/
lemma clockP_off {s s' : B → ℤ} {x : Option (V × V)}
    (hx : clockP mem r S₀ (atBoundary emit b gov) s x = some s') {c : B} (hc : c ≠ b) :
    s' c = (if x.isSome then s c else tickStock (mem c) (r c) (S₀ c) (s c)) := by
  rcases x with _ | e
  · cases hx; rfl
  · simp only [clockP, stockP, ofGated] at hx
    split_ifs at hx
    cases hx
    simp [deplete_atBoundary, hc]

/-- Fidélité sur les paires : hors de `b`, les deux ordres appliquent les mêmes tops ; sur `b`,
    la charge détermine le stock sous l'invariant. -/
theorem clockP_pairFaithful (hS : 0 ≤ S₀ b) (he : ∀ e, 0 ≤ emit e b) :
    PairFaithful (ClockInv S₀ b gov) (loadAt S₀ b) (clockP mem r S₀ (atBoundary emit b gov)) := by
  intro q x y q₁ q₂ hq h1 h2 hπ
  have hP := clockP_projectsOn (mem := mem) (r := r) (gov := gov) hS he
  have i1 := run_inv hP.1 [x, y] q q₁ hq h1
  have i2 := run_inv hP.1 [y, x] q q₂ hq h2
  funext c
  by_cases hc : c = b
  · subst hc
    unfold loadAt at hπ
    have := i1.1; have := i2.1
    omega
  · obtain ⟨p₁, hx₁, hy₁⟩ := run_pair_eq_some h1
    obtain ⟨p₂, hy₂, hx₂⟩ := run_pair_eq_some h2
    rw [clockP_off hy₁ hc, clockP_off hx₁ hc, clockP_off hx₂ hc, clockP_off hy₂ hc]
    rcases x with _ | _ <;> rcases y with _ | _ <;> rfl

end LedgerProjection

/-! ### 3 bis. Sémantique totale : le grand livre horodaté complet -/

section LedgerTotal

variable {V B : Type*} [DecidableEq V] [DecidableEq B]
variable {mem : B → Memory} {r : B → ℕ} {S₀ : B → ℤ} {emit : V × V → B → ℤ} {b : B}
  {gov : Governance}

omit [DecidableEq B] in
/-- Soldes ≥ 0 et montants nuls : sur les stocks, le grand livre horodaté est la sémantique
    totale de `clockP`. -/
lemma clockStep_stock {st : PState V B} (hbal : ∀ v, 0 ≤ st.bal v) (fp : Footprint V B)
    (x : Option (V × V)) :
    (clockStep true mem r S₀ fp st x).stock = toTotal (clockP mem r S₀ fp) st.stock x := by
  rcases x with _ | e
  · rfl
  · simp only [clockStep, withTick, toTotal, clockP, stockP, ofGated, planetStep,
      GatedStep.gatedStep, planetAdmissible]
    by_cases h : stockAdmissible fp st.stock e
    · rw [if_pos ⟨(ledgerAdmissible_zero _ _).mpr (hbal _), h⟩, if_pos h]
      rfl
    · rw [if_neg (fun h' => h h'.2), if_neg h]
      rfl

/-- ★ `canonStep ↔ planetStep` : sous soldes ≥ 0 et `ClockInv`, la charge de `b` après un pas
    du grand livre horodaté est le pas canonique avec horloge appliqué à la charge. -/
theorem clockStep_projects (hS : 0 ≤ S₀ b) (he : ∀ e, 0 ≤ emit e b) {st : PState V B}
    (hbal : ∀ v, 0 ≤ st.bal v) (hinv : ClockInv S₀ b gov st.stock) (x : Option (V × V)) :
    loadAt S₀ b (clockStep true mem r S₀ (atBoundary emit b gov) st x).stock =
      canonStep true (mem b) gov (fun e => (emit e b).toNat) (S₀ b).toNat (r b)
        (loadAt S₀ b st.stock) x := by
  rw [clockStep_stock hbal, ← toTotal_canonPA,
    toTotal_of_projectsOn (clockP_projectsOn hS he) hinv]

end LedgerTotal

/-! ### 4. Classe du grand livre horodaté -/

section LedgerClass

variable {V B : Type*} [DecidableEq V] [DecidableEq B]

/-- Non-dégénérescence (miroir de `FeedbackClass.Nondeg`) : régénération effective, émissions
    ≥ 0 sur `b`, deux émetteurs distincts de `b`. -/
def LedgerNondeg (emit : V × V → B → ℤ) (r : B → ℕ) (b : B) : Prop :=
  0 < r b ∧ (∀ e, 0 ≤ emit e b) ∧ ∃ x y : V × V, x ≠ y ∧ emit x b ≠ 0 ∧ emit y b ≠ 0

omit [DecidableEq V] [DecidableEq B] in
/-- Un pli horodaté est commutatif si les règlements commutent et si le top commute avec
    chacun. -/
lemma withTick_commutative {σ α : Type*} {δ : σ → α → σ} {tick : σ → σ}
    (hδ : IsCommutativeUpdate δ) (ht : ∀ s a, tick (δ s a) = δ (tick s) a) :
    IsCommutativeUpdate (withTick δ tick) := by
  rintro s (_ | a) (_ | a')
  · rfl
  · exact (ht s a').symm
  · exact ht s a
  · exact hδ s a a'

omit [DecidableEq V] [DecidableEq B] in
lemma not_commutative_withTick {σ α : Type*} {δ : σ → α → σ} (tick : σ → σ)
    (h : ¬ IsCommutativeUpdate δ) : ¬ IsCommutativeUpdate (withTick δ tick) :=
  fun hc => h fun s a a' => hc s (some a) (some a')

omit [DecidableEq V] in
lemma atBoundary_emit_nonneg {emit : V × V → B → ℤ} {b : B} (hnn : ∀ e, 0 ≤ emit e b)
    (gov : Governance) :
    ∀ e, ∀ c ∈ (atBoundary emit b gov).gated, 0 ≤ (atBoundary emit b gov).emit e c := by
  intro e c _
  by_cases hcb : c = b
  · subst hcb; simp [atBoundary, hnn e]
  · simp [atBoundary, hcb]

/-- Frontière libre : les règlements (montants nuls) commutent. -/
lemma planetStep_free_commutative (emit : V × V → B → ℤ) (b : B) :
    IsCommutativeUpdate (planetStep 0 (atBoundary emit b .free)) := by
  have h0 : (atBoundary emit b .free).gated = ∅ := by simp [atBoundary]
  exact (planet_feedback_class (atBoundary emit b .free) (by simp [h0]) .stock).2.1 h0

/-- Frontière gardée à deux émetteurs distincts : les règlements ne commutent pas. -/
lemma planetStep_gated_noncomm {emit : V × V → B → ℤ} {b : B} (hnn : ∀ e, 0 ≤ emit e b)
    {x y : V × V} (hxy : x ≠ y) (hx : emit x b ≠ 0) (hy : emit y b ≠ 0) :
    ¬ IsCommutativeUpdate (planetStep 0 (atBoundary emit b .gated)) :=
  ((planet_feedback_class (atBoundary emit b .gated) (atBoundary_emit_nonneg hnn _) .stock).2.2
    b (by simp [atBoundary]) x y hxy (by simp [atBoundary, hx]) (by simp [atBoundary, hy])).2

variable {mem : B → Memory} {r : B → ℕ} {S₀ : B → ℤ} {emit : V × V → B → ℤ} {b : B}

/-- Mémoire `stock` en `b` : le top commute avec tout règlement de `atBoundary` (il ne touche
    pas `b`, et les règlements ne touchent que `b`). -/
lemma tickLedger_planetStep (hm : mem b = .stock) (gov : Governance) (st : PState V B)
    (e : V × V) :
    tickLedger mem r S₀ (planetStep 0 (atBoundary emit b gov) st e) =
      planetStep 0 (atBoundary emit b gov) (tickLedger mem r S₀ st) e := by
  have hadm : planetAdmissible 0 (atBoundary emit b gov) (tickLedger mem r S₀ st) e ↔
      planetAdmissible 0 (atBoundary emit b gov) st e := by
    unfold planetAdmissible
    rw [stockAdmissible_atBoundary, stockAdmissible_atBoundary]
    simp only [tickLedger, tickStocks, hm, tickStock]
  unfold planetStep GatedStep.gatedStep
  by_cases h : planetAdmissible 0 (atBoundary emit b gov) st e
  · rw [if_pos h, if_pos (hadm.mpr h)]
    simp only [tickLedger, planetUpd, PState.mk.injEq, true_and, and_true]
    funext c
    simp only [tickStocks, deplete_atBoundary]
    by_cases hc : c = b
    · subst hc; simp [hm, tickStock]
    · simp [hc]
  · rw [if_neg h, if_neg (fun h' => h (hadm.mp h'))]

/-- Mémoire non stock en `b`, frontière libre : le top ne commute pas avec une émission
    non nulle (témoin : stocks pleins `S₀`). -/
lemma clock_tick_noncomm (hm : mem b ≠ .stock) (hr : 0 < r b) {x : V × V}
    (hx : emit x b ≠ 0) :
    ¬ IsCommutativeUpdate (clockStep true mem r S₀ (atBoundary emit b .free)) := by
  intro hc
  have hadm : ∀ st : PState V B, st.bal = 0 → planetAdmissible 0 (atBoundary emit b .free) st x :=
    fun st h0 => ⟨(ledgerAdmissible_zero _ _).mpr (by simp [h0]),
      (stockAdmissible_atBoundary _ _ _ _ _).mpr (by simp)⟩
  have H := congrArg (fun st : PState V B => st.stock b) (hc ⟨0, S₀, 0⟩ (some x) none)
  simp only [clockStep, withTick, if_true] at H
  rw [planetStep_of_adm (hadm _ rfl), planetStep_of_adm (hadm _ rfl)] at H
  simp only [tickLedger, planetUpd, tickStocks, deplete_atBoundary, if_true] at H
  cases h : mem b
  · exact hm h
  · simp only [h, tickStock] at H; omega
  · simp only [h, tickStock] at H; omega

/-- ★ Classe du grand livre horodaté d'une frontière : c'est `profileClass clock (mem b) gov`,
    pour les 12 combinaisons (miroir de `FeedbackClass.profileClass_sound` sur le grand livre). -/
theorem clock_profileClass_sound (clock : Bool) (mem : B → Memory) (r : B → ℕ) (S₀ : B → ℤ)
    (gov : Governance) {emit : V × V → B → ℤ} {b : B} (hnd : LedgerNondeg emit r b) :
    SemClass (clockStep clock mem r S₀ (atBoundary emit b gov))
      (liftOpt (I_planet (atBoundary emit b gov))) (profileClass clock (mem b) gov) := by
  obtain ⟨hr, hnn, x, y, hxy, hx, hy⟩ := hnd
  have hD := withTick_diamond (planetStep_comm 0 (atBoundary emit b gov))
    (if clock then tickLedger mem r S₀ else id)
  cases gov
  · by_cases hc : clock = true ∧ mem b ≠ .stock
    · obtain ⟨rfl, hm⟩ := hc
      have hT : profileClass true (mem b) .free = .T := by
        cases h : mem b
        · exact absurd h hm
        · rfl
        · rfl
      rw [hT]
      exact ⟨hD, clock_tick_noncomm hm hr hx⟩
    · have hP : profileClass clock (mem b) .free = .P := by
        cases clock
        · cases mem b <;> rfl
        · have hm : mem b = .stock := by simpa using hc
          rw [hm]; rfl
      rw [hP]
      refine withTick_commutative (planetStep_free_commutative emit b) fun st e => ?_
      cases clock
      · rfl
      · exact tickLedger_planetStep (by simpa using hc) .free st e
  · have hT : profileClass clock (mem b) .gated = .T := by
      cases clock <;> cases mem b <;> rfl
    rw [hT]
    exact ⟨hD, not_commutative_withTick _ (planetStep_gated_noncomm hnn hxy hx hy)⟩

end LedgerClass

section Profiles

variable {V : Type*} [DecidableEq V]

/-- ★ Le grand livre horodaté réalise la classe de TOUT profil de modélisation, frontière par
    frontière : `parikhClassIn prof b` est la classe sémantique du grand livre de `b`, muni du
    top si `prof.clock`, gardé selon `prof.gov b`. -/
theorem ledger_realizes_profile (prof : ParikhProfile) (r : PlanetaryBoundary → ℕ)
    (S₀ : PlanetaryBoundary → ℤ) {emit : V × V → PlanetaryBoundary → ℤ} {b : PlanetaryBoundary}
    (hnd : LedgerNondeg emit r b) :
    SemClass (clockStep prof.clock memoryOf r S₀ (atBoundary emit b (prof.gov b)))
      (liftOpt (I_planet (atBoundary emit b (prof.gov b))))
      (profileClass prof.clock (memoryOf b) (prof.gov b)) ∧
    parikhClassIn prof b = (profileClass prof.clock (memoryOf b) (prof.gov b)).toNat :=
  ⟨clock_profileClass_sound prof.clock memoryOf r S₀ (prof.gov b) hnd, rfl⟩

/-- ★ Contrepartie positive de `BoundaryLedgerBridge.physicsProfile_not_ledger` : une frontière
    non budgétée à mémoire non stock (biosphère, aérosols) est P sur le grand livre sans
    horloge, T sur le grand livre horodaté — la classe de `physicsProfile`. -/
theorem physicsProfile_ledger_clock (r : PlanetaryBoundary → ℕ) (S₀ : PlanetaryBoundary → ℤ)
    {emit : V × V → PlanetaryBoundary → ℤ} {b : PlanetaryBoundary} (hb : isBudgeted b = false)
    (hm : memoryOf b ≠ .stock) (hnd : LedgerNondeg emit r b) :
    parikhClassIn physicsProfile b = 1 ∧
    SemClass (planetStep 0 (ledgerAt emit b)) (I_planet (ledgerAt emit b)) .P ∧
    SemClass (clockStep true memoryOf r S₀ (ledgerAt emit b))
      (liftOpt (I_planet (ledgerAt emit b))) .T := by
  obtain ⟨h1, hP, -⟩ := physicsProfile_not_ledger emit hb hm
  refine ⟨h1, hP, ?_⟩
  have hgov : governedProfile.gov b = .free := by simp [governedProfile, hb]
  have hT : profileClass true (memoryOf b) .free = .T := by
    cases h : memoryOf b
    · exact absurd h hm
    · rfl
    · rfl
  have h := clock_profileClass_sound true memoryOf r S₀ .free hnd
  rw [hT] at h
  rw [ledgerAt_eq_atBoundary, hgov]
  exact h

/-- ★ Le profil gouverné est la classe du grand livre horodaté de chaque frontière. -/
theorem governedProfile_ledger_clock (r : PlanetaryBoundary → ℕ) (S₀ : PlanetaryBoundary → ℤ)
    {emit : V × V → PlanetaryBoundary → ℤ} {b : PlanetaryBoundary} (hnd : LedgerNondeg emit r b) :
    SemClass (clockStep true memoryOf r S₀ (ledgerAt emit b))
      (liftOpt (I_planet (ledgerAt emit b)))
      (profileClass governedProfile.clock (memoryOf b) (governedProfile.gov b)) := by
  rw [ledgerAt_eq_atBoundary]
  exact clock_profileClass_sound true memoryOf r S₀ _ hnd

end Profiles

/-! ### 5. T5 et Parikh par période -/

section T5

variable {V B : Type*} [DecidableEq V] [DecidableEq B]

omit [DecidableEq B] in
/-- ★ T5 sur le grand livre horodaté : réordonnabilité intra-période ⟺ les règlements
    commutent, quel que soit le top. -/
theorem clock_T5_iff (clock : Bool) (mem : B → Memory) (r : B → ℕ) (S₀ : B → ℤ)
    (fp : Footprint V B) :
    Diamond (clockStep clock mem r S₀ fp) I_tick ↔ IsCommutativeUpdate (planetStep 0 fp) :=
  diamond_withTick_iff _ _

/-- Frontière libre : deux périodes de règlements permutés donnent le même état après le top
    (Parikh par période). -/
theorem clock_period_perm_invariant (clock : Bool) (mem : B → Memory) (r : B → ℕ)
    (S₀ : B → ℤ) (emit : V × V → B → ℤ) (b : B) {l₁ l₂ : List (V × V)} (h : l₁.Perm l₂)
    (st : PState V B) :
    (l₁.map some ++ [none]).foldl (clockStep clock mem r S₀ (atBoundary emit b .free)) st =
      (l₂.map some ++ [none]).foldl (clockStep clock mem r S₀ (atBoundary emit b .free)) st := by
  rw [List.foldl_append, List.foldl_append, List.foldl_map, List.foldl_map]
  congr 1
  exact commutative_implies_perm_invariant (planetStep_free_commutative emit b) h st

/-- Frontière gardée à deux émetteurs distincts : pas de T5 (cohérent avec
    `TokenizedCommons.fcfs_not_diamond_tick`). -/
theorem clock_gated_not_T5 (clock : Bool) (mem : B → Memory) (r : B → ℕ) (S₀ : B → ℤ)
    {emit : V × V → B → ℤ} {b : B} (hnn : ∀ e, 0 ≤ emit e b) {x y : V × V} (hxy : x ≠ y)
    (hx : emit x b ≠ 0) (hy : emit y b ≠ 0) :
    ¬ Diamond (clockStep clock mem r S₀ (atBoundary emit b .gated)) I_tick := by
  rw [clock_T5_iff]
  exact planetStep_gated_noncomm hnn hxy hx hy

end T5

/-! ### 6. Stabilité sur le grand livre (C5) -/

section LedgerStability

variable {V B : Type*} [DecidableEq B]
variable {mem : B → Memory} {r : B → ℕ} {S₀ : B → ℤ} {emit : V × V → B → ℤ} {b : B}
  {gov : Governance}

/-- Mémoire `stock` en `b` : les stocks horodatés forment un automate commutatif. -/
theorem clockP_stock_commutative (hm : mem b = .stock) (he : ∀ e, 0 ≤ emit e b) :
    IsCommutativePA (clockP mem r S₀ (atBoundary emit b gov)) := by
  have htick : ∀ s e, run (clockP mem r S₀ (atBoundary emit b gov)) s [none, some e] =
      run (clockP mem r S₀ (atBoundary emit b gov)) s [some e, none] := by
    intro s e
    have hadm : stockAdmissible (atBoundary emit b gov) (tickStocks mem r S₀ s) e ↔
        stockAdmissible (atBoundary emit b gov) s e := by
      rw [stockAdmissible_atBoundary, stockAdmissible_atBoundary]
      simp only [tickStocks, hm, tickStock]
    by_cases h : stockAdmissible (atBoundary emit b gov) s e
    · simp only [run_cons, run_nil, clockP, stockP, ofGated, Option.bind_some, if_pos h,
        if_pos (hadm.mpr h), Option.bind_some, Option.some.injEq]
      funext c
      simp only [tickStocks, deplete_atBoundary]
      by_cases hc : c = b
      · subst hc; simp [hm, tickStock]
      · simp [hc]
    · simp only [run_cons, run_nil, clockP, stockP, ofGated, Option.bind_some, if_neg h,
        if_neg (fun h' => h (hadm.mp h')), Option.bind_none]
  intro s x y
  rcases x with _ | a <;> rcases y with _ | a'
  · rfl
  · exact htick s a'
  · exact (htick s a).symm
  · exact stock_commutative (atBoundary_emit_nonneg he gov) s a a'

/-- Mémoire `stock` : stablement concurrent et S2, en tout état. -/
theorem clock_stock_stable (hm : mem b = .stock) (he : ∀ e, 0 ≤ emit e b) :
    StablyConcurrent (clockP mem r S₀ (atBoundary emit b gov)) ∧
      S2 (clockP mem r S₀ (atBoundary emit b gov)) :=
  stable_of_commutative (clockP_stock_commutative hm he)

/-- ★ Mémoire `flow` : cube et S2 en tout état de `ClockInv`, par transport du modèle
    canonique (`canon_flow_stable`). -/
theorem clock_flow_stableOn (hm : mem b = .flow) (hS : 0 ≤ S₀ b) (he : ∀ e, 0 ≤ emit e b)
    {s : B → ℤ} (hs : ClockInv S₀ b gov s) (x y z : Option (V × V)) :
    Cube (clockP mem r S₀ (atBoundary emit b gov)) s x y z ∧
      S2At (clockP mem r S₀ (atBoundary emit b gov)) s x y z := by
  rw [cube_iff_of_projectsOn (clockP_projectsOn hS he) (clockP_pairFaithful hS he) hs,
    S2At_iff_of_projectsOn (clockP_projectsOn hS he) (clockP_pairFaithful hS he) hs, hm]
  exact ⟨canon_flow_cube _ _ _ _ _, canon_flow_S2At _ _ _ _ _⟩

/-- ★ C5 en Lean : mémoire `regen` en `b` (plafond 2, régénération 1), deux émetteurs
    unitaires distincts : le cube échoue depuis les stocks pleins, avec ou sans garde. -/
theorem clock_regen_not_stable (hm : mem b = .regen) (hS : S₀ b = 2) (hr : r b = 1)
    (he : ∀ e, 0 ≤ emit e b) {x y : V × V} (hxy : x ≠ y) (hx : emit x b = 1)
    (hy : emit y b = 1) :
    ClockInv S₀ b gov S₀ ∧
      ¬ Cube (clockP mem r S₀ (atBoundary emit b gov)) S₀ (some x) (some y) none := by
  have hS' : 0 ≤ S₀ b := by rw [hS]; norm_num
  have hinv : ClockInv S₀ b gov S₀ := ⟨le_refl _, fun _ => hS'⟩
  refine ⟨hinv, ?_⟩
  rw [cube_iff_of_projectsOn (clockP_projectsOn hS' he) (clockP_pairFaithful hS' he) hinv, hm,
    hr]
  have h0 : loadAt S₀ b S₀ = 0 := by simp [loadAt]
  have hcap : (S₀ b).toNat = 2 := by rw [hS]; rfl
  rw [h0, hcap]
  exact canon_regen_not_cube hxy (by simp [hx]) (by simp [hy])

end LedgerStability

/-! ### 7. Cliquet (P2-12), hors `Memory` -/

section Ratchet

variable {α : Type*} {gov : Governance} {e : α → ℕ} {cap : ℕ}

/-- Cliquet de seuil `θ` : sous `θ`, le top régénère `r` ; dès `θ`, la frontière est basculée et
    le top ne régénère plus. Sur les états accessibles depuis 0, coïncide avec le modèle à
    drapeau `(L, basculé)` (la charge ne redescend jamais sous `θ` une fois atteint). -/
def ratchetTick (θ r L : ℕ) : ℕ := if θ ≤ L then L else L - r

/-- Modèle canonique partiel du cliquet. -/
def ratchetPA (θ r : ℕ) (gov : Governance) (e : α → ℕ) (cap : ℕ) : PAut ℕ (Option α) :=
  canonPA (ratchetTick θ r) gov e cap

/-- ★ P2-12 : le cliquet n'est aucune des mémoires de `Memory` (`θ ≥ 2`, `r > 0`) — sous `θ`
    il régénère (contre `stock`), au-delà il ne régénère plus (contre `regen` et `flow`). -/
theorem ratchet_ne_tickOp {θ r : ℕ} (hr : 0 < r) (hθ : 2 ≤ θ) (mem : Memory) (r' : ℕ) :
    tickOp mem r' ≠ ratchetTick θ r := by
  intro h
  have h1 := congrFun h 1
  have h2 := congrFun h θ
  cases mem <;> simp only [tickOp, ratchetTick] at h1 h2 <;> split_ifs at h1 h2 <;> omega

/-- Le cliquet est de classe T (jamais D, mono-coordonnée) dès qu'une émission tirable reste
    sous le seuil. -/
theorem ratchet_class_T {θ r : ℕ} (hr : 0 < r) {a : α} (ha : 0 < e a) (haθ : e a < θ)
    (hcap : e a ≤ cap) :
    SemClass (toTotal (ratchetPA θ r gov e cap)) (DisjointFoot canonSupp) .T := by
  refine ⟨(single_coord_not_D (fun _ h => absurd h Finset.univ_nonempty.ne_empty)).1,
    fun hc => ?_⟩
  have H := hc 0 (some a) none
  have hf : fits gov cap 0 (e a) := fun _ => by omega
  simp only [toTotal, ratchetPA, canonPA_some, canonPA_none, if_pos hf, Option.getD_some,
    ratchetTick] at H
  have hf' : fits gov cap (if θ ≤ 0 then 0 else 0 - r) (e a) := by
    intro _; split_ifs <;> omega
  rw [if_pos hf'] at H
  simp only [Option.getD_some] at H
  split_ifs at H <;> omega

/-- Basculée (`θ ≤ L`) et sans garde, la frontière se comporte en stock : toutes les lettres
    commutent depuis `L`. -/
theorem ratchet_tipped_commutes {θ r L : ℕ} (hL : θ ≤ L) (x y : Option α) :
    run (ratchetPA θ r .free e cap) L [x, y] = run (ratchetPA θ r .free e cap) L [y, x] := by
  unfold ratchetPA
  have hfree : ∀ L k, fits .free cap L k := fun _ _ h => absurd h (by decide)
  rcases x with _ | a <;> rcases y with _ | a'
  · rfl
  · rw [run_none_some, run_some_none, if_pos (hfree _ _), if_pos (hfree _ _)]
    simp only [ratchetTick, if_pos hL, if_pos (le_trans hL (Nat.le_add_right L (e a')))]
  · rw [run_none_some, run_some_none, if_pos (hfree _ _), if_pos (hfree _ _)]
    simp only [ratchetTick, if_pos hL, if_pos (le_trans hL (Nat.le_add_right L (e a)))]
  · rw [run_some_some, run_some_some, add_comm (e a') (e a), Nat.add_right_comm L (e a') (e a)]

/-- ★ Le cliquet peut rompre une stabilité que regen préserve : gardé, émissions 1 et 2,
    plafond 3, `r = 2`, `θ = 2`, depuis 0, lettres `(x, top, y)` — le cube du cliquet échoue,
    celui de regen tient au même point. -/
theorem ratchet_not_stable {x y : α} (hxy : x ≠ y) (hx : e x = 1) (hy : e y = 2) :
    ¬ Cube (ratchetPA 2 2 .gated e 3) 0 (some x) none (some y) ∧
      Cube (canonPA (tickOp .regen 2) .gated e 3) 0 (some x) none (some y) := by
  unfold ratchetPA Cube
  simp only [parAfter_none, parAfter_some, maxPar_some_some, maxPar_some_none, maxPar_none_some,
    tickOp, ratchetTick, hx, hy]
  simp [fits, hxy]

end Ratchet

end LedgerClock
