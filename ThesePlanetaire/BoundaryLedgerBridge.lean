/-
  ThesePlanetaire/BoundaryLedgerBridge.lean
  Phase 7 (2026-10-02) : pont entre la couche haute (`PlanetaryBoundaries`) et le grand livre
  planétaire (`PlanetaryLedger`, `FeedbackPlanetary`).

  Développé d'abord en `BoundaryLedgerBridge_scratch.lean` (workflow du dépôt). Plan :
  `~/.claude/plans/witty-dazzling-manatee.md` (Phase 7, étape 7b) ; analyse :
  `cache/analyse_refonte_couche_haute_2026-10-02.md`.

  `FeedbackPlanetary.planet_feedback_class` classe le grand livre planétaire GLOBALEMENT, pour
  une empreinte quelconque. Une classe PAR FRONTIÈRE demande deux choses que ce module fournit :
  - l'identification des frontières gardées aux frontières budgétées
    (`boundaryFootprint`, `mem_gated_iff`) ;
  - la restriction de l'empreinte à une frontière (`restrictTo`, `ledgerAt`).
  Résultats, sur la composante environnementale (montants nuls, `planetStep 0`) :
  1. ★ `ledgerProfile_certified` : le profil `PlanetaryBoundaries.ledgerProfile` (sans
     horloge) est un MAJORANT de la classe sémantique de chaque frontière, atteint — P pour une
     frontière non budgétée ; T pour une frontière budgétée dès que deux émetteurs distincts se
     la disputent (contention) ;
  2. ★ `physicsProfile_not_ledger` : le profil physique (avec horloge) n'est pas réalisé par le
     grand livre sans horloge — biosphère et aérosols y sont T, le grand livre restreint les
     donne P.
  Phase 8 : le grand livre muni d'un top de période par mémoire réalise la classe de tout
  profil, physique compris (`LedgerClock.ledger_realizes_profile`,
  `LedgerClock.physicsProfile_ledger_clock`).
-/

import ThesePlanetaire.FeedbackPlanetary

namespace BoundaryLedgerBridge

open PlanetaryBoundaries
open PlanetaryLedger (Footprint planetStep I_planet)
open FeedbackPlanetary (planet_feedback_class planet_not_D)
open FeedbackClass (FClass SemClass semClass_unique profileClass)

variable {V : Type*} [DecidableEq V]

/-! ### 1. Empreintes indexées par les frontières -/

/-- Empreinte planétaire indexée par les 9 frontières : les frontières budgétées
    (`isBudgeted`) sont gardées. -/
def boundaryFootprint (emit : V × V → PlanetaryBoundary → ℤ) : Footprint V PlanetaryBoundary :=
  ⟨emit, Finset.univ.filter (fun b => isBudgeted b = true)⟩

omit [DecidableEq V] in
theorem mem_gated_iff (emit : V × V → PlanetaryBoundary → ℤ) (b : PlanetaryBoundary) :
    b ∈ (boundaryFootprint emit).gated ↔ isBudgeted b = true := by
  simp [boundaryFootprint]

/-- Restriction d'une empreinte à la frontière `b` : les émissions sur les autres frontières
    sont annulées, la garde ne porte plus que sur `b`. -/
def restrictTo (fp : Footprint V PlanetaryBoundary) (b : PlanetaryBoundary) :
    Footprint V PlanetaryBoundary :=
  ⟨fun e c => if c = b then fp.emit e c else 0, fp.gated.filter (· = b)⟩

/-- Grand livre de la seule frontière `b`. -/
def ledgerAt (emit : V × V → PlanetaryBoundary → ℤ) (b : PlanetaryBoundary) :
    Footprint V PlanetaryBoundary :=
  restrictTo (boundaryFootprint emit) b

omit [DecidableEq V] in
theorem ledgerAt_gated (emit : V × V → PlanetaryBoundary → ℤ) (b : PlanetaryBoundary) :
    (ledgerAt emit b).gated = if isBudgeted b = true then {b} else ∅ := by
  ext c
  by_cases hb : isBudgeted b = true
  · simp only [ledgerAt, restrictTo, boundaryFootprint, hb, if_true, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨And.right, fun h => ⟨h ▸ hb, h⟩⟩
  · simp [ledgerAt, restrictTo, boundaryFootprint, hb]
    rintro hc rfl
    exact hb hc

omit [DecidableEq V] in
theorem ledgerAt_emit (emit : V × V → PlanetaryBoundary → ℤ) (b : PlanetaryBoundary)
    (e : V × V) : (ledgerAt emit b).emit e b = emit e b := by
  simp [ledgerAt, restrictTo, boundaryFootprint]

/-! ### 2. Certification du profil du grand livre -/

/-- Toute classe différente de D est ≤ T. -/
lemma le_T_of_ne_D {c : FClass} (h : c ≠ .D) : c ≤ .T := by
  cases c
  · decide
  · decide
  · exact absurd rfl h

/-- ★ Certification du profil du grand livre, frontière par frontière, sur la composante
    environnementale (montants nuls) du grand livre restreint à `b` :
    1. majorant : toute classe sémantique est ≤ celle du profil `ledgerProfile` ;
    2. `b` non budgétée : la classe est P, celle du profil (rang 0) ;
    3. `b` budgétée, émissions ≥ 0 et deux émetteurs distincts : la classe est T, celle du
       profil (rang 1).
    Le profil est un majorant atteint dès qu'il y a contention ; sans contention, une frontière
    budgétée reste P (`FeedbackPlanetary.planet_env_P`). -/
theorem ledgerProfile_certified (emit : V × V → PlanetaryBoundary → ℤ) (b : PlanetaryBoundary) :
    (∀ c, SemClass (planetStep 0 (ledgerAt emit b)) (I_planet (ledgerAt emit b)) c →
      c ≤ profileClass ledgerProfile.clock (memoryOf b) (ledgerProfile.gov b)) ∧
    (isBudgeted b = false →
      SemClass (planetStep 0 (ledgerAt emit b)) (I_planet (ledgerAt emit b))
        (profileClass ledgerProfile.clock (memoryOf b) (ledgerProfile.gov b)) ∧
      parikhClassIn ledgerProfile b = 0) ∧
    (isBudgeted b = true → (∀ e, 0 ≤ emit e b) →
      ∀ x y : V × V, x ≠ y → emit x b ≠ 0 → emit y b ≠ 0 →
        SemClass (planetStep 0 (ledgerAt emit b)) (I_planet (ledgerAt emit b))
          (profileClass ledgerProfile.clock (memoryOf b) (ledgerProfile.gov b)) ∧
        parikhClassIn ledgerProfile b = 1) := by
  have hval := parikhClass_ledger_values b
  -- Cas non budgété : aucune garde, l'environnement est P.
  have hfree : isBudgeted b = false →
      SemClass (planetStep 0 (ledgerAt emit b)) (I_planet (ledgerAt emit b))
        (profileClass ledgerProfile.clock (memoryOf b) (ledgerProfile.gov b)) := by
    intro hb
    have hg : (ledgerAt emit b).gated = ∅ := by rw [ledgerAt_gated, hb]; rfl
    have hgov : ledgerProfile.gov b = .free := by simp [ledgerProfile, hb]
    rw [hgov]
    exact (planet_feedback_class (ledgerAt emit b) (by simp [hg]) (memoryOf b)).2.1 hg
  refine ⟨fun c hc => ?_, fun hb => ⟨hfree hb, by rw [hval, hb]; rfl⟩,
    fun hb hnn x y hxy hx hy => ⟨?_, by rw [hval, hb]; rfl⟩⟩
  · -- Majorant.
    cases hb : isBudgeted b
    · rw [semClass_unique hc (hfree hb)]
    · have hgov : ledgerProfile.gov b = .gated := by simp [ledgerProfile, hb]
      have hT : profileClass ledgerProfile.clock (memoryOf b) .gated = .T := by
        cases memoryOf b <;> rfl
      rw [hgov, hT]
      exact le_T_of_ne_D fun h => planet_not_D 0 (ledgerAt emit b) (h ▸ hc)
  · -- Contention sur une frontière budgétée : T.
    have hg : (ledgerAt emit b).gated = {b} := by rw [ledgerAt_gated, if_pos hb]
    have hgov : ledgerProfile.gov b = .gated := by simp [ledgerProfile, hb]
    rw [hgov]
    have h_emit : ∀ e, ∀ c ∈ (ledgerAt emit b).gated, 0 ≤ (ledgerAt emit b).emit e c := by
      intro e c hc
      rw [hg, Finset.mem_singleton] at hc
      subst hc
      rw [ledgerAt_emit]
      exact hnn e
    refine (planet_feedback_class (ledgerAt emit b) h_emit (memoryOf b)).2.2 b
      (by rw [hg]; exact Finset.mem_singleton_self b) x y hxy ?_ ?_
    · rw [ledgerAt_emit]; exact hx
    · rw [ledgerAt_emit]; exact hy

/-! ### 3. Le profil physique n'est pas celui du grand livre -/

/-- ★ Une frontière non budgétée à mémoire non stock (biosphère, aérosols) est T sous le profil
    physique (`physicsProfile`, avec horloge) ; le grand livre sans horloge la donne P sur
    l'empreinte restreinte, donc pas T (`semClass_unique`). La classe par défaut `parikhClass`
    décrit un modèle à tops de période : le grand livre horodaté la réalise
    (`LedgerClock.physicsProfile_ledger_clock`). -/
theorem physicsProfile_not_ledger (emit : V × V → PlanetaryBoundary → ℤ) {b : PlanetaryBoundary}
    (hb : isBudgeted b = false) (hm : memoryOf b ≠ .stock) :
    parikhClassIn physicsProfile b = 1 ∧
    SemClass (planetStep 0 (ledgerAt emit b)) (I_planet (ledgerAt emit b)) .P ∧
    ¬ SemClass (planetStep 0 (ledgerAt emit b)) (I_planet (ledgerAt emit b)) .T := by
  have hP : SemClass (planetStep 0 (ledgerAt emit b)) (I_planet (ledgerAt emit b)) .P := by
    have h := ((ledgerProfile_certified emit b).2.1 hb).1
    have hgov : ledgerProfile.gov b = .free := by simp [ledgerProfile, hb]
    rw [hgov] at h
    have hc : profileClass ledgerProfile.clock (memoryOf b) .free = .P := by
      cases memoryOf b <;> rfl
    rwa [hc] at h
  refine ⟨?_, hP, fun hT => absurd (semClass_unique hP hT) (by decide)⟩
  cases b <;> first | exact absurd hb (by decide) | exact absurd rfl hm | decide

end BoundaryLedgerBridge
