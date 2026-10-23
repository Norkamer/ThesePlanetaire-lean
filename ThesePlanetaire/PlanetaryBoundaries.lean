/-
  ThesePlanetaire/PlanetaryBoundaries.lean
  Couche haute : les 9 frontières planétaires, leur classe de rétroaction, leur calibration, la
  double condition E-SFC et la mise à jour planétaire des scores.

  Phase 7 (2026-10-02) : refonte. Développé d'abord en `PlanetaryBoundariesP7_scratch.lean`
  (workflow du dépôt). Plan : `~/.claude/plans/witty-dazzling-manatee.md` (Phase 7) ; analyse :
  `cache/analyse_refonte_couche_haute_2026-10-02.md`.

  Contenu :
  1. les 9 frontières (`PlanetaryBoundary`) ; `numBoundaries` est dérivé du type ;
  2. la classe de Parikh DÉRIVÉE (Phase 4) : `parikhClassIn` sous un profil (`physicsProfile`,
     `governedProfile`, `ledgerProfile`), calculée par `FeedbackClass.profileClass` (horloge ×
     mémoire × gouvernance) et certifiée par `FeedbackClass.profileClass_sound` ; le profil
     `ledgerProfile` (sans horloge) est certifié sur le grand livre planétaire dans
     `BoundaryLedgerBridge` ; l'ancienne table stipulée est `parikhClass_macro` (vue macro
     héritée). Analyse : `cache/analyse_classes_parikh_2026-10-01.md` ;
  3. la calibration indexée par évaluation (Richardson et al. 2023, Planetary Health Check
     2025) : variables de contrôle typées, transgression DÉRIVÉE des données ;
  4. la double condition E-SFC (Dafermos, Nikolaidi & Galanis 2017, 2018) ;
  5. le domaine de validité D (non-vacuité d'un domaine de paramètres) ;
  6. la Taxonomie UE (règlement 2020/852) comme alphabet réglementaire ;
  7. la mise à jour planétaire des scores : contrôle individuel contre `C_plan` (conception de
     la thèse, conservée) et instrument par parts (correct et attribuable).

  Retirés à la Phase 7 de l'en-tête, faute de contenu formel : les ponts M1/M2/M3 (§V65), le
  seuil K_max (problème ouvert, non formalisé), Aprile et al.

  Chronologie des frontières : Rockström et al. 2009 (Nature 461 ; Ecology & Society 14(2)) ;
  Steffen et al. 2015 (Science 347) ; Richardson et al. 2023 (Science Advances 9) ; Findlay et
  al. 2025 (Global Change Biology 31(6), acidification) ; Planetary Health Check 2025 et 2026
  (PBScience, PIK).

  Références :
  - Dafermos, Nikolaidi & Galanis, Ecological Economics 131 (2017) et 152 (2018)
  - Godley & Lavoie, Monetary Economics (Palgrave Macmillan 2007)
  - Aubin, Viability Theory (Birkhäuser 1991)
  - Klessascheck, Fahrenkrog-Petersen, Mendling & Pufahl, EDOC 2024 (LNCS 15409)
  - Segerson, JEEM 15 (1988) 87-98 ; Ryberg et al. 2020 ; Hjalsted et al. 2021 ; McLaren et
    al., Frontiers in Climate 1 (2019)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import ThesePlanetaire.FeedbackClass

namespace PlanetaryBoundaries

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. Les 9 frontières planétaires

    Processus identifiés par Rockström et al. (2009) ; variables de contrôle révisées par
    Steffen et al. (2015), Richardson et al. (2023) et le Planetary Health Check 2025 (§3). -/

/-- Les 9 frontières planétaires (processus identifiés en 2009). -/
inductive PlanetaryBoundary
  | climateChange       -- Changement climatique (CO₂ atmosphérique, ppm ; forçage radiatif, W/m²)
  | biogeochemicalFlows -- Flux biogéochimiques (phosphore P, azote N : Tg/an)
  | freshwaterUse       -- Eau douce (eau bleue / verte : % des terres hors variabilité)
  | landSystemChange    -- Changement des terres (forêt restante, % de la couverture originelle)
  | ozoneDepletion      -- Appauvrissement de l'ozone stratosphérique (colonne, DU)
  | biosphereIntegrity  -- Intégrité de la biosphère (extinctions, E/MSY ; HANPP, %)
  | oceanAcidification  -- Acidification des océans (Ωarag de surface)
  | novelEntities       -- Entités nouvelles (substances rejetées sans évaluation suffisante)
  | atmosphericAerosols -- Aérosols atmosphériques (différence interhémisphérique d'AOD)
  deriving DecidableEq

/-- Instance Fintype pour PlanetaryBoundary (9 constructeurs). -/
instance : Fintype PlanetaryBoundary where
  elems := { .climateChange, .biogeochemicalFlows, .freshwaterUse, .landSystemChange,
             .ozoneDepletion, .biosphereIntegrity, .oceanAcidification, .novelEntities, .atmosphericAerosols }
  complete := by intro x; cases x <;> simp

/-- Nombre total de frontières planétaires, dérivé du type (Phase 7 ; stipulé `9` auparavant). -/
def numBoundaries : ℕ := Fintype.card PlanetaryBoundary

theorem numBoundaries_eq : numBoundaries = 9 := rfl

/-! ### 2. Classe de Parikh dérivée (Phase 4)

    La classe d'une frontière n'est pas une étiquette : c'est la classe de rétroaction
    (`FeedbackClass.FClass`) du modèle qui la régit sur l'historique des transactions, calculée
    par `FeedbackClass.profileClass` à partir de trois paramètres :
    - l'horloge (tops de période dans l'alphabet) et la gouvernance (garde « premier arrivé »),
      portées par un profil `ParikhProfile` ;
    - la mémoire de la variable de contrôle (`memoryOf`, calibration statut B).
    `profileClass_sound` certifie la classe calculée pour les 12 combinaisons ; aucune frontière
    isolée n'est D (`parikhClassIn_le_one`, via `single_coord_not_D`). Phase 7 : le grand livre
    planétaire n'a pas d'horloge ; son profil est `ledgerProfile`. Phase 8 : muni d'un top de
    période par mémoire, il réalise la classe de tout profil
    (`LedgerClock.ledger_realizes_profile`). -/

/-- Ancienne classification stipulée (vue macro héritée, Phase 5c) : 0 = Parikh-linéaire,
    1 = taux ou cascade, 2 = mémoire de la séquence. Conservée pour la vue macro
    (`TraceAdmissibility.*_macro`, `MonetaryPlanetaryBridge.*_macro`, `PhiFused`) ; elle
    confond non-additivité et dépendance à l'ordre (analyse Phase 4, §C). -/
def parikhClass_macro (b : PlanetaryBoundary) : ℕ :=
  match b with
  | .climateChange => 0
  | .biogeochemicalFlows => 0
  | .freshwaterUse => 0
  | .landSystemChange => 0
  | .ozoneDepletion => 0
  | .biosphereIntegrity => 1
  | .oceanAcidification => 1
  | .novelEntities => 2
  | .atmosphericAerosols => 2

/-- Mémoire de la variable de contrôle (calibration, statut B) :
    - `stock` : CO₂ (TCRE, longue vie), forêt restante, Ωarag ≈ fonction du CO₂ cumulé,
      polluants persistants ;
    - `flow` : flux N/P par an, prélèvements d'eau par an, aérosols (durée de vie courte) ;
    - `regen` : ODS à décroissance et récupération de la colonne d'ozone ; biosphère
      (recolonisation, dette d'extinction). -/
def memoryOf (b : PlanetaryBoundary) : FeedbackClass.Memory :=
  match b with
  | .climateChange => .stock
  | .biogeochemicalFlows => .flow
  | .freshwaterUse => .flow
  | .landSystemChange => .stock
  | .ozoneDepletion => .regen
  | .biosphereIntegrity => .regen
  | .oceanAcidification => .stock
  | .novelEntities => .stock
  | .atmosphericAerosols => .flow

/-- Profil de modélisation : horloge (tops de période dans l'historique) et gouvernance de
    chaque frontière. -/
structure ParikhProfile where
  clock : Bool
  gov : PlanetaryBoundary → FeedbackClass.Governance

/-- Frontières dotées d'un budget calibré (`planetary_boundary_weight` > 0,
    `isBudgeted_iff`). -/
def isBudgeted (b : PlanetaryBoundary) : Bool :=
  match b with
  | .climateChange | .biogeochemicalFlows | .freshwaterUse | .landSystemChange
  | .ozoneDepletion => true
  | _ => false

/-- Profil physique, défaut de `parikhClass` : avec horloge, sans garde. Statut B (Phase 7) :
    l'horloge relève des modèles canoniques `FeedbackClass.canonStep` (tops de période dans
    l'alphabet) ; le grand livre planétaire sans horloge ne la réalise pas (son profil est
    `ledgerProfile`, et `BoundaryLedgerBridge.physicsProfile_not_ledger` exhibe l'écart). Muni du
    top de période (Phase 8, `LedgerClock.clockStep`), il la réalise
    (`LedgerClock.physicsProfile_ledger_clock`). Sur un budget gardé, un top `regen` (charge
    tronquée `L - r`) rompt de plus la stabilité de Husson–Morin, même sans garde, contrairement
    à `stock` et `flow` (`LedgerClock.clock_regen_not_stable`, `LedgerClock.flow_regen_split` ;
    miroirs `python/tests/test_boundary_refonte.py`, `test_ledger_clock.py`). -/
def physicsProfile : ParikhProfile := ⟨true, fun _ => .free⟩

/-- Profil gouverné : avec horloge ; les frontières budgétées sont gardées (le grand livre
    planétaire, `PlanetaryLedger`). Réalisé par le grand livre horodaté, frontière par
    frontière (Phase 8, `LedgerClock.governedProfile_ledger_clock`). -/
def governedProfile : ParikhProfile :=
  ⟨true, fun b => if isBudgeted b then .gated else .free⟩

/-- Profil du grand livre planétaire (Phase 7) : SANS horloge — l'alphabet de `PlanetaryLedger`
    ne contient que des paiements, aucun top de période — ; les frontières budgétées sont
    gardées. Certifié sur le grand livre : `BoundaryLedgerBridge.ledgerProfile_certified`. -/
def ledgerProfile : ParikhProfile :=
  ⟨false, fun b => if isBudgeted b then .gated else .free⟩

/-- Classe de Parikh d'une frontière sous un profil (0 = P, 1 = T, 2 = D). -/
def parikhClassIn (prof : ParikhProfile) (b : PlanetaryBoundary) : ℕ :=
  (FeedbackClass.profileClass prof.clock (memoryOf b) (prof.gov b)).toNat

/-- Classe de Parikh par défaut : la physique dérivée (`physicsProfile`). Même nom que
    l'ancienne table, valeurs dérivées : voir `parikhClass_vs_macro`. -/
def parikhClass (b : PlanetaryBoundary) : ℕ := parikhClassIn physicsProfile b

/-- Aucune frontière isolée n'est D, sous aucun profil. -/
theorem parikhClassIn_le_one (prof : ParikhProfile) (b : PlanetaryBoundary) :
    parikhClassIn prof b ≤ 1 := by
  have h := FeedbackClass.profileClass_le_T prof.clock (memoryOf b) (prof.gov b)
  unfold parikhClassIn
  generalize FeedbackClass.profileClass prof.clock (memoryOf b) (prof.gov b) = c at h ⊢
  cases c
  · decide
  · decide
  · exact absurd h (by decide)

/-- Garder n'abaisse jamais la classe : la classe gouvernée majore la physique. -/
theorem parikhClass_le_governed (b : PlanetaryBoundary) :
    parikhClass b ≤ parikhClassIn governedProfile b := by
  cases b <;> decide

/-- Valeurs par défaut : P pour climat, terres, acidification, entités nouvelles ; T pour
    N/P, eau douce, ozone, biosphère, aérosols. -/
theorem parikhClass_values :
    parikhClass .climateChange = 0 ∧ parikhClass .biogeochemicalFlows = 1 ∧
    parikhClass .freshwaterUse = 1 ∧ parikhClass .landSystemChange = 0 ∧
    parikhClass .ozoneDepletion = 1 ∧ parikhClass .biosphereIntegrity = 1 ∧
    parikhClass .oceanAcidification = 0 ∧ parikhClass .novelEntities = 0 ∧
    parikhClass .atmosphericAerosols = 1 := by
  decide

/-- Profil gouverné : T partout sauf acidification et entités nouvelles (non budgétées, stock). -/
theorem parikhClass_governed_values (b : PlanetaryBoundary) :
    parikhClassIn governedProfile b =
      if b = .oceanAcidification ∨ b = .novelEntities then 0 else 1 := by
  cases b <;> decide

/-- Profil du grand livre : T exactement sur les 5 frontières budgétées, P ailleurs ; sans
    horloge, la mémoire n'intervient plus. -/
theorem parikhClass_ledger_values (b : PlanetaryBoundary) :
    parikhClassIn ledgerProfile b = if isBudgeted b then 1 else 0 := by
  cases b <;> decide

/-- Écarts entre la classe dérivée et l'ancienne table : six frontières changent (N/P, eau,
    ozone : 0 → 1 ; acidification : 1 → 0 ; entités nouvelles : 2 → 0 ; aérosols : 2 → 1) ;
    climat, terres et biosphère sont inchangées. -/
theorem parikhClass_vs_macro (b : PlanetaryBoundary) :
    parikhClass b = parikhClass_macro b ↔
      b = .climateChange ∨ b = .landSystemChange ∨ b = .biosphereIntegrity := by
  cases b <;> decide

/-- Poids des frontières budgétées : héritage HÉTÉROGÈNE, conservé pour `k0_five_budgets`
    (`TraceAdmissibility`) et la table du ch. 8bis. Ces nombres n'ont ni unité ni statut
    communs (la calibration typée est au §3) :
    - 420 (climat) ≈ la VALEUR COURANTE du CO₂ en ppm (417 en 2023, 423 en 2025), non la
      frontière (350) ;
    - 161 (flux N/P) : non sourcé ;
    - 4000 (eau douce) : km³/an, ancienne variable de consommation d'eau bleue, remplacée en
      2023 par des fractions de terres [attribution à Rockström et al. 2009 : À VÉRIFIER] ;
    - 75 (terres) : frontière globale de forêt restante, en % [attribution à Steffen et al.
      2015 : À VÉRIFIER] ;
    - 276 (ozone) : frontière, en DU.
    Un budget n'est pas une classe : les frontières budgétées (`isBudgeted`) ne sont pas les
    frontières de classe 0 (`parikhClass_vs_macro`) ; les autres ont un poids nul faute de
    calibration. -/
def planetary_boundary_weight (b : PlanetaryBoundary) : ℝ :=
  match b with
  | .climateChange => 420.0
  | .biogeochemicalFlows => 161.0
  | .freshwaterUse => 4000.0
  | .landSystemChange => 75.0
  | .ozoneDepletion => 276.0
  | .biosphereIntegrity => 0
  | .oceanAcidification => 0
  | .novelEntities => 0
  | .atmosphericAerosols => 0

theorem isBudgeted_iff (b : PlanetaryBoundary) :
    isBudgeted b = true ↔ 0 < planetary_boundary_weight b := by
  cases b <;> simp [isBudgeted, planetary_boundary_weight] <;> norm_num

/-! ### 3. Calibration indexée par évaluation (Phase 7)

    Chaque évaluation publiée (`Assessment`) fixe, pour chaque variable de contrôle d'une
    frontière, le seuil de l'espace sûr, le haut de la zone de risque croissant et une valeur
    courante. Règle d'agrégation des évaluations : une frontière est transgressée si L'UNE de
    ses variables l'est. La transgression est DÉRIVÉE des données saisies ; les cardinaux
    (`transgressed_r2023_card`, `transgressed_phc2025_card`) contrôlent la cohérence de la
    saisie avec les comptes publiés (6/9, 7/9) : ce ne sont pas des théorèmes empiriques.

    Sources, texte primaire lu le 2026-10-02 :
    - Richardson et al. 2023, Science Advances 9, eadh2458, table 1 [VÉRIFIÉ-EXT 02/10] ;
    - Planetary Health Check 2025 (PBScience, PIK), résumé exécutif, fiches par frontière
      [VÉRIFIÉ-EXT 02/10]. Deux changements de référence : acidification (préindustriel
      révisé ; frontière 80 % × 3,44 ≈ 2,75 → 2,86 : Findlay et al. 2025, GCB 31(6) e70238) et
      eau douce (conditions 2010-2019 ; frontières 10,2 / 11,1 % → 12,9 / 12,4 %). La variable
      P globale n'y figure plus.
    Le Planetary Health Check 2026 (21/09/2026) annonce 7/9, même ensemble (non saisi). -/

/-- Évaluation publiée de l'état des frontières. -/
inductive Assessment
  | richardson2023  -- Richardson et al. 2023, table 1
  | phc2025         -- Planetary Health Check 2025
  deriving DecidableEq, Fintype

/-- Sens de la frontière : `up`, transgressée au-dessus du seuil (CO₂, E/MSY, Tg/an…) ;
    `down`, transgressée au-dessous (forêt restante, ozone, Ωarag). -/
inductive Direction
  | up
  | down
  deriving DecidableEq

/-- Lecture de la valeur courante : exacte ; minorée (« > 100 E/MSY », « 100-1000 E/MSY ») ;
    qualitative seulement (entités nouvelles : « Transgressed », sans nombre). -/
inductive Reading
  | exact (q : ℚ)
  | atLeast (q : ℚ)
  | qualitative (transgressed : Bool)

/-- Unité d'une variable de contrôle. -/
inductive BoundaryUnit
  | ppm        -- concentration atmosphérique
  | wattPerM2  -- forçage radiatif
  | eMSY       -- extinctions par million d'espèces-années
  | percent    -- fraction (HANPP, forêt restante, terres hors variabilité, substances)
  | dobson     -- colonne d'ozone
  | omegaArag  -- état de saturation de l'aragonite (sans dimension)
  | tgPerYear  -- flux de P ou de N
  | deltaAOD   -- différence interhémisphérique d'épaisseur optique (sans dimension)
  deriving DecidableEq

/-- Variable de contrôle d'une frontière dans une évaluation. -/
structure ControlVariable where
  name : String
  unit : BoundaryUnit
  /-- seuil de l'espace sûr -/
  boundary : ℚ
  /-- haut de la zone de risque croissant (`none` : non défini) -/
  highRisk : Option ℚ
  reading : Reading
  dir : Direction

/-- Transgression ÉTABLIE d'une variable : la valeur courante est strictement au-delà du seuil.
    Une lecture minorée ne l'établit que dans le sens `up` ; une lecture qualitative est reprise
    telle quelle. -/
def ControlVariable.transgressed (x : ControlVariable) : Bool :=
  match x.reading, x.dir with
  | .exact q, .up => decide (x.boundary < q)
  | .exact q, .down => decide (q < x.boundary)
  | .atLeast q, .up => decide (x.boundary < q)
  | .atLeast _, .down => false
  | .qualitative t, _ => t

/-- Variables de contrôle de chaque frontière, par évaluation (valeurs des sources, §3). -/
def controls : Assessment → PlanetaryBoundary → List ControlVariable
  | .richardson2023, .climateChange =>
      [⟨"CO₂ atmosphérique", .ppm, 350, some 450, .exact 417, .up⟩,
       ⟨"forçage radiatif anthropique", .wattPerM2, 1, some (3 / 2), .exact (291 / 100), .up⟩]
  | .richardson2023, .biogeochemicalFlows =>
      [⟨"P global (eau douce vers océan)", .tgPerYear, 11, some 100, .exact (226 / 10), .up⟩,
       ⟨"P régional (engrais, sols érodables)", .tgPerYear, 62 / 10, some (112 / 10),
          .exact (175 / 10), .up⟩,
       ⟨"N (fixation industrielle et intentionnelle)", .tgPerYear, 62, some 82, .exact 190, .up⟩]
  | .richardson2023, .freshwaterUse =>
      [⟨"eau bleue", .percent, 102 / 10, some 50, .exact (182 / 10), .up⟩,
       ⟨"eau verte", .percent, 111 / 10, some 50, .exact (158 / 10), .up⟩]
  | .richardson2023, .landSystemChange =>
      [⟨"forêt restante (global)", .percent, 75, some 54, .exact 60, .down⟩]
  | .richardson2023, .ozoneDepletion =>
      [⟨"O₃ stratosphérique", .dobson, 276, some 261, .exact (2846 / 10), .down⟩]
  | .richardson2023, .biosphereIntegrity =>
      [⟨"diversité génétique", .eMSY, 10, some 100, .atLeast 100, .up⟩,
       ⟨"intégrité fonctionnelle (HANPP)", .percent, 10, some 20, .exact 30, .up⟩]
  | .richardson2023, .oceanAcidification =>
      [⟨"Ωarag de surface (80 % du préindustriel 3,44)", .omegaArag, 4 / 5 * (344 / 100),
          some (275 / 100), .exact (28 / 10), .down⟩]
  | .richardson2023, .novelEntities =>
      [⟨"substances sans évaluation suffisante", .percent, 0, none, .qualitative true, .up⟩]
  | .richardson2023, .atmosphericAerosols =>
      [⟨"différence interhémisphérique d'AOD", .deltaAOD, 1 / 10, some (1 / 4),
          .exact (76 / 1000), .up⟩]
  | .phc2025, .climateChange =>
      [⟨"CO₂ atmosphérique", .ppm, 350, some 450, .exact 423, .up⟩,
       ⟨"forçage radiatif anthropique", .wattPerM2, 1, some (3 / 2), .exact (297 / 100), .up⟩]
  | .phc2025, .biogeochemicalFlows =>
      [⟨"P minéral appliqué aux cultures", .tgPerYear, 62 / 10, some (112 / 10),
          .exact (182 / 10), .up⟩,
       ⟨"N (fixation intentionnelle)", .tgPerYear, 62, some 82, .exact 165, .up⟩]
  | .phc2025, .freshwaterUse =>
      [⟨"eau bleue", .percent, 129 / 10, some 50, .exact (226 / 10), .up⟩,
       ⟨"eau verte", .percent, 124 / 10, some 50, .exact 22, .up⟩]
  | .phc2025, .landSystemChange =>
      [⟨"forêt restante (global)", .percent, 75, some 54, .exact 59, .down⟩]
  | .phc2025, .ozoneDepletion =>
      [⟨"O₃ stratosphérique", .dobson, 277, some 263, .exact (2857 / 10), .down⟩]
  | .phc2025, .biosphereIntegrity =>
      [⟨"diversité génétique", .eMSY, 10, some 100, .atLeast 100, .up⟩,
       ⟨"intégrité fonctionnelle (HANPP)", .percent, 10, some 20, .exact 30, .up⟩]
  | .phc2025, .oceanAcidification =>
      [⟨"Ωarag de surface (80 % du préindustriel révisé)", .omegaArag, 286 / 100,
          some (275 / 100), .exact (284 / 100), .down⟩]
  | .phc2025, .novelEntities =>
      [⟨"substances sans évaluation suffisante", .percent, 0, none, .qualitative true, .up⟩]
  | .phc2025, .atmosphericAerosols =>
      [⟨"différence interhémisphérique d'AOD", .deltaAOD, 1 / 10, some (1 / 4),
          .exact (63 / 1000), .up⟩]

/-- Frontière transgressée selon une évaluation : l'une de ses variables l'est. -/
def transgressed (a : Assessment) (b : PlanetaryBoundary) : Bool :=
  (controls a b).any ControlVariable.transgressed

/-- Nombre de frontières transgressées selon une évaluation. -/
def transgressedCount (a : Assessment) : ℕ :=
  (Finset.univ.filter (fun b => transgressed a b = true)).card

/-- Contrôle de saisie : Richardson et al. 2023 compte 6 frontières transgressées sur 9. -/
theorem transgressed_r2023_card : transgressedCount .richardson2023 = 6 := by
  decide +kernel

/-- Contrôle de saisie : le Planetary Health Check 2025 compte 7 frontières transgressées. -/
theorem transgressed_phc2025_card : transgressedCount .phc2025 = 7 := by
  decide +kernel

/-- De 2023 à 2025, la seule frontière qui bascule est l'acidification (changement de
    référence du préindustriel, non simple aggravation). -/
theorem transgressed_phc2025_eq (b : PlanetaryBoundary) :
    transgressed .phc2025 b = (transgressed .richardson2023 b || decide (b = .oceanAcidification)) := by
  cases b <;> decide +kernel

/-- Le compte des transgressions ne dépasse jamais le nombre de frontières. -/
theorem transgressedCount_le (a : Assessment) : transgressedCount a ≤ numBoundaries :=
  Finset.card_filter_le _ _

/-! ### 4. Double condition E-SFC (Ecological Stock-Flow Consistent)

    Dafermos, Nikolaidi & Galanis (2017, 2018) : les stocks de ressources naturelles
    entrent dans les bilans comme actifs, les flux d'émissions comme passifs différés.
    La stationnarité requiert simultanément :
    Σ_j B_j^fin = 0  ET  Σ_j F_j^phys ≤ C_plan. -/

/-- État d'une institution j : un solde financier et un flux physique par période. Pas de
    stock : écart avec Dafermos, Nikolaidi & Galanis, où matière, énergie, CO₂ atmosphérique et
    capital sont des stocks dynamiques ; le stock planétaire est porté par le grand livre
    (`PlanetaryLedger.PState.stock`). -/
structure InstitutionState where
  financial_balance : ℝ  -- B_j^fin
  physical_flow : ℝ      -- F_j^phys

/-- Condition de stationnarité financière : Σ B_j^fin = 0. C'est l'identité de fermeture
    comptable d'un système fermé (les soldes financiers sectoriels se compensent : Godley &
    Lavoie 2007), non une condition dynamique. -/
def financial_stationarity (states : Finset InstitutionState) : Prop :=
  ∑ s ∈ states, s.financial_balance = 0

/-- Condition de stationnarité physique : Σ F_j^phys ≤ C_plan. Contrainte d'AGRÉGAT : `C_plan`
    est ici un total (capacité planétaire) ; la mise à jour du §7 le réemploie comme seuil
    individuel. -/
def physical_stationarity (states : Finset InstitutionState) (C_plan : ℝ) : Prop :=
  ∑ s ∈ states, s.physical_flow ≤ C_plan

/-- Théorème : la double condition E-SFC est satisfiable.
    Preuve par construction : l'état (0,0) satisfait les deux conditions. Non-vacuité d'un
    domaine de paramètres : aucune dynamique, donc pas un cône ni un noyau de viabilité au sens
    d'Aubin (1991).
    **Mort gardé — principe économique** (cône de viabilité E-SFC,
    Dafermos-Nikolaidi-Galanis 2018, cité chapitre1). -/
theorem esfc_viability_cone :
    ∃ (states : Finset InstitutionState) (C_plan : ℝ),
      C_plan > 0 ∧ financial_stationarity states ∧ physical_stationarity states C_plan := by
  refine ⟨{⟨0, 0⟩}, 1, by norm_num, ?_, ?_⟩
  · simp [financial_stationarity]
  · simp [physical_stationarity]

/-! ### 5. Domaine de validité D

    Un domaine de PARAMÈTRES ; ses « viabilités » sont des non-vacuités (témoins explicites),
    non des noyaux de viabilité (Aubin 1991). -/

/-- Domaine de validité D. `k_env` est dérivable de la calibration (`currentDomain`) ; `k_fin`,
    `T` et `n` prennent des valeurs illustratives. -/
structure ValidityDomain where
  k_env : ℕ  -- nombre de frontières transgressées
  k_fin : ℕ  -- nombre d'institutions hors conformité
  T : ℝ      -- volume transactionnel annuel
  n : ℕ      -- nombre d'institutions
  h_k_env : k_env ≤ numBoundaries
  h_T : T > 0
  h_n : n ≥ 2

/-- Théorème : le domaine de validité D est non vide.
    Preuve par construction explicite (non-vacuité, non noyau de viabilité).
    **Mort gardé — théorème d'existence** (noyau de viabilité, Aubin 1991 ;
    cité annexe_assertions). -/
theorem viability_kernel_non_empty :
    ∃ (d : ValidityDomain), d.k_env = 0 ∧ d.k_fin = 0 ∧ d.T = 1 ∧ d.n = 2 := by
  let d : ValidityDomain := {
    k_env := 0,
    k_fin := 0,
    T := 1,
    n := 2,
    h_k_env := by decide,
    h_T := by norm_num,
    h_n := by decide
  }
  use d

/-- Théorème : la situation actuelle x_curr = (6, 2, 10^10, 200) appartient à D.
    `k_env = 6` coïncide avec le compte de Richardson et al. 2023 (`current_state_r2023`) ; le
    Planetary Health Check 2025 en compte 7. `k_fin`, `T`, `n` sont illustratifs.
    **Mort gardé — théorème d'existence** (état courant dans le domaine D). -/
theorem current_state_in_domain :
    ∃ (d : ValidityDomain), d.k_env = 6 ∧ d.k_fin = 2 ∧ d.T = 10 ^ 10 ∧ d.n = 200 := by
  let d : ValidityDomain := {
    k_env := 6,
    k_fin := 2,
    T := 10 ^ 10,
    n := 200,
    h_k_env := by decide,
    h_T := by norm_num,
    h_n := by decide
  }
  use d

/-- État courant selon une évaluation : `k_env` DÉRIVÉ de la calibration (§3) ; `k_fin`, `T`,
    `n` reprennent les valeurs illustratives de `current_state_in_domain`. -/
def currentDomain (a : Assessment) : ValidityDomain where
  k_env := transgressedCount a
  k_fin := 2
  T := 10 ^ 10
  n := 200
  h_k_env := transgressedCount_le a
  h_T := by norm_num
  h_n := by decide

theorem currentDomain_k_env (a : Assessment) :
    (currentDomain a).k_env = transgressedCount a := rfl

/-- L'état de `current_state_in_domain` est `currentDomain .richardson2023`. -/
theorem current_state_r2023 :
    (currentDomain .richardson2023).k_env = 6 ∧ (currentDomain .richardson2023).k_fin = 2 ∧
      (currentDomain .richardson2023).T = 10 ^ 10 ∧ (currentDomain .richardson2023).n = 200 :=
  ⟨transgressed_r2023_card, rfl, rfl, rfl⟩

theorem currentDomain_phc2025_k_env : (currentDomain .phc2025).k_env = 7 :=
  transgressed_phc2025_card

/-! ### 6. Taxonomie UE comme alphabet réglementaire

    Règlement (UE) 2020/852. Art. 9 : six objectifs environnementaux. Art. 3 : une activité est
    durable si elle remplit QUATRE conditions — (a) contribution substantielle à au moins un
    objectif (art. 10-16) ; (b) absence de préjudice important aux autres (art. 17) ;
    (c) garanties minimales (art. 18) ; (d) conformité aux critères d'examen technique (TSC).
    Les art. 5-8 sont des obligations de PUBLICATION (produits financiers ; art. 8 : entreprises
    soumises à la publication d'informations non financières, périmètre restreint par
    l'Omnibus I, directive (UE) 2026/470, aux entités de plus de 1000 salariés et 450 M€ de
    chiffre d'affaires [source secondaire]). Le considérant 15 vise la publication VOLONTAIRE
    d'opérateurs hors champ. Aucun de ces textes n'interdit une transaction : traiter `binding`
    et `opt_in` comme des gardes du WFA de clearing est un choix de modélisation. -/

/-- 6 objectifs environnementaux de l'EU Taxonomy (Art. 9). -/
inductive EUTaxonomyObjective
  | climateMitigation
  | climateAdaptation
  | waterUse
  | circularEconomy
  | pollutionPrevention
  | biodiversityProtection
  deriving DecidableEq

/-- Une transition relève soit d'une publication obligatoire (`binding`), soit d'une
    publication volontaire (`opt_in`). -/
inductive TaxonomyTransitionType
  | binding    -- Art. 5-8 : publication obligatoire (art. 8 : périmètre Omnibus I)
  | opt_in     -- Considérant 15 : publication volontaire
  deriving DecidableEq

/-- Instance Fintype pour EUTaxonomyObjective (6 constructeurs). -/
instance : Fintype EUTaxonomyObjective where
  elems := { .climateMitigation, .climateAdaptation, .waterUse,
             .circularEconomy, .pollutionPrevention, .biodiversityProtection }
  complete := by intro x; cases x <;> simp

/-- Garde réglementaire sur une transition du WFA de clearing.
    Chaque transition peut être contrainte par un objectif de la Taxonomie EU
    et par un type (`binding` : publication obligatoire, `opt_in` : volontaire).
    Source : Klessascheck, Fahrenkrog-Petersen, Mendling & Pufahl (2024),
    "Unlocking Sustainability Compliance: Characterizing the EU Taxonomy for
    Business Process Management", EDOC 2024 / BIWeek 2024, Vienna.
    arXiv:2408.11386v2, DOI: 10.1007/978-3-031-78338-8_18.
    Les auteurs extraient 1 636 contraintes des critères de la Taxonomie (classification
    assistée par Llama-3-8B). Environ 80 % (1 313) sont exploitables en conformance checking,
    toutes dimensions confondues (control-flow, temps, ressources, données) ; la dimension
    control-flow n'en compte que 632 (≈ 39 % : 624 d'existence d'activité, 8 entre activités). -/
structure RegulatoryGuard where
  edge : V × V
  taxonomy_obj : EUTaxonomyObjective
  transition_type : TaxonomyTransitionType

/-- Théorème : la Taxonomie EU a 6 objectifs.
    Preuve : par construction du type `EUTaxonomyObjective`.
    **Mort gardé — fait économique** (6 objectifs EU Taxonomy 2020/852,
    cité chapitre8bis via \leanref). -/
theorem eu_taxonomy_six_objectives :
    Fintype.card EUTaxonomyObjective = 6 := by
  rw [Fintype.card]
  simp
  rfl

/-! ### 7. Fonction de mise à jour planétaire

    Conception de la thèse (ch. 8bis : « toutes les institutions partagent la même contrainte
    C_plan ») : chaque institution est contrôlée INDIVIDUELLEMENT contre `C_plan` ; un flux
    au-delà annule son score (rejet par hard feasibility), sinon le score croît, borné.
    `C_plan` y change de rôle : total au §4 (`physical_stationarity`), seuil individuel ici. Le
    code reproduit fidèlement ce choix (`planetary_update_function`, inchangé).

    Phase 7 — contrôler une contrainte d'AGRÉGAT institution par institution est un trilemme :
    - contre le total (`planetary_update_function`) : incorrect dès deux institutions
      (`uniform_share_unsound`) : chacune passe, la somme atteint |V| · C_plan ;
    - ambiant, sur la somme (Segerson 1988) : correct, mais la sanction est collective et non
      attribuable ; sur des flux signés, les absorptions compensent les émissions (McLaren et
      al. 2019) ;
    - par parts (`planetary_update_shares`, Σ parts ≤ C_plan ; partage de l'espace sûr :
      Ryberg et al. 2020, Hjalsted et al. 2021) : correct (`shares_sound`) et attribuable.
    L'ancienne fonction est le cas de la part uniforme `C_plan` (`update_eq_uniform_share`). -/

/-- Fonction de mise à jour des scores avec contrainte planétaire C_plan.
    Modèle E-SFC simplifié : l'institution est récompensée (score + 1 borné)
    tant que son flux physique reste sous le seuil C_plan.
    Si le flux dépasse C_plan, le score est nul (rejet).
    Seuil INDIVIDUEL (conception de la thèse) : voir l'en-tête du §7.

    Noncomputable car `≤` sur `ℝ` n'est pas décidable computablement. -/
noncomputable def planetary_update_function
    (institutions : V → InstitutionState)
    (C_plan : ℝ)
    (max_score : ℕ)
    (scores : V → ℕ) : V → ℕ :=
  λ v =>
    if (institutions v).physical_flow ≤ C_plan then
      min (scores v + 1) max_score
    else
      0

-- Instances de section conservées : signature citée (`StabilityWFA.planetary_stability`).
set_option linter.unusedSectionVars false in
/-- Lemme : la mise à jour planétaire est monotone.
    Si les scores initiaux sont ordonnés, les scores mis à jour le restent. -/
lemma planetary_update_monotone
    (institutions : V → InstitutionState) (C_plan : ℝ) (max_score : ℕ)
    (s₁ s₂ : V → ℕ) (h_mono : ∀ v, s₁ v ≤ s₂ v) (v : V) :
    planetary_update_function institutions C_plan max_score s₁ v ≤
    planetary_update_function institutions C_plan max_score s₂ v := by
  have h1 : planetary_update_function institutions C_plan max_score s₁ v =
      if (institutions v).physical_flow ≤ C_plan then min (s₁ v + 1) max_score else 0 := rfl
  have h2 : planetary_update_function institutions C_plan max_score s₂ v =
      if (institutions v).physical_flow ≤ C_plan then min (s₂ v + 1) max_score else 0 := rfl
  rw [h1, h2]
  split_ifs with h_cond
  · -- Cas conforme : min (s₁ v + 1) max_score ≤ min (s₂ v + 1) max_score
    apply min_le_min
    · exact Nat.add_le_add_right (h_mono v) 1
    · rfl
  · -- Cas non conforme : 0 ≤ 0
    rfl

-- Instances de section conservées : signature citée (`StabilityWFA.planetary_stability`).
set_option linter.unusedSectionVars false in
/-- Lemme : la mise à jour planétaire est bornée par max_score.
    Par construction (min avec max_score ou 0). -/
lemma planetary_update_bounded
    (institutions : V → InstitutionState) (C_plan : ℝ) (max_score : ℕ)
    (s : V → ℕ) (v : V) :
    planetary_update_function institutions C_plan max_score s v ≤ max_score := by
  have h1 : planetary_update_function institutions C_plan max_score s v =
      if (institutions v).physical_flow ≤ C_plan then min (s v + 1) max_score else 0 := rfl
  rw [h1]
  split_ifs with h_cond
  · -- Cas conforme : min (s v + 1) max_score ≤ max_score
    apply Nat.min_le_right
  · -- Cas non conforme : 0 ≤ max_score
    exact Nat.zero_le max_score

/-- Mise à jour par parts (Phase 7) : chaque institution est contrôlée contre SA part
    `share v` de la capacité ; même forme de score que `planetary_update_function`. -/
noncomputable def planetary_update_shares
    (institutions : V → InstitutionState)
    (share : V → ℝ)
    (max_score : ℕ)
    (scores : V → ℕ) : V → ℕ :=
  fun v =>
    if (institutions v).physical_flow ≤ share v then
      min (scores v + 1) max_score
    else
      0

omit [Fintype V] [DecidableEq V] in
/-- L'ancienne mise à jour est l'instrument par parts à part UNIFORME `C_plan`. -/
theorem update_eq_uniform_share (institutions : V → InstitutionState) (C_plan : ℝ)
    (max_score : ℕ) (scores : V → ℕ) :
    planetary_update_function institutions C_plan max_score scores =
      planetary_update_shares institutions (fun _ => C_plan) max_score scores :=
  rfl

omit [DecidableEq V] in
/-- ★ Correction des parts : si les parts tiennent dans la capacité (Σ parts ≤ C_plan) et
    qu'aucune institution n'est exclue (score non nul), la contrainte d'agrégat
    `Σ flux ≤ C_plan` est satisfaite. Contraposée : un dépassement exclut au moins une
    institution, celle qui excède sa part (attribution). -/
theorem shares_sound (institutions : V → InstitutionState) (share : V → ℝ) {C_plan : ℝ}
    (h_share : ∑ v, share v ≤ C_plan) (max_score : ℕ) (scores : V → ℕ)
    (h_pass : ∀ v, planetary_update_shares institutions share max_score scores v ≠ 0) :
    ∑ v, (institutions v).physical_flow ≤ C_plan := by
  refine le_trans (Finset.sum_le_sum fun v _ => ?_) h_share
  by_contra h
  exact h_pass v (if_neg h)

omit [DecidableEq V] in
/-- ★ Incorrection de la part uniforme : dès deux institutions et `C_plan > 0`, il existe des
    flux tels que CHAQUE institution passe le contrôle de `planetary_update_function` alors que
    leur somme vaut |V| · C_plan > C_plan. La borne |V| · C_plan est atteinte : c'est celle
    que `shares_sound` donne pour la part uniforme. -/
theorem uniform_share_unsound (hV : 2 ≤ Fintype.card V) {C_plan : ℝ} (hC : 0 < C_plan)
    (max_score : ℕ) (scores : V → ℕ) :
    ∃ institutions : V → InstitutionState,
      (∀ v, planetary_update_function institutions C_plan max_score scores v =
        min (scores v + 1) max_score) ∧
      ∑ v, (institutions v).physical_flow = Fintype.card V * C_plan ∧
      C_plan < ∑ v, (institutions v).physical_flow := by
  refine ⟨fun _ => ⟨0, C_plan⟩, fun v => if_pos le_rfl, ?_, ?_⟩
  · simp [Finset.sum_const, nsmul_eq_mul]
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h2 : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hV
    nlinarith

end PlanetaryBoundaries
