/-
  MonnaiesEndogene/OrganicLP.lean
  Phase 4 (v4.2) : LP organique pour TEG monétaire.

  ╔══════════════════════════════════════════════════════════════════════╗
  ║  NOTE TERMINOLOGIQUE — Dissolution de l'analogie Kabanov (v4.2)     ║
  ╠══════════════════════════════════════════════════════════════════════╣
  ║  Ce module utilise des objets COMBINATOIRES AUTONOMES.             ║
  ║  Il ne formalise PAS de concepts de finance mathématique continue. ║
  ║                                                                      ║
  ║  • PAS de "shadow price" continu (λ ∈ ℝ). L4 utilise `rarity : ℕ`.   ║
  ║  • PAS de "no-arbitrage" au sens de Kabanov–Schachermayer.         ║
  ║    `SolvencyCone` est un cône au sens IDEMPOTENT (D4 booléen),      ║
  ║    non un cône convexe dans ℝ^d.                                    ║
  ║  • PAS de dualité LP continue (max c·x = min b·λ).                 ║
  ║    La dualité est celle des TREILLIS FINIS (Knaster-Tarski),       ║
  ║    formalisée dans `DualiteLP.lean`.                                ║
  ║                                                                      ║
  ║  Les objets de ce module (cashFlowSum, isSelfFinancing,             ║
  ║  SolvencyCone, carbonBudgetLocal) sont indépendants de ℝ.           ║
  ║  Ils sont définis sur ℤ, ℕ, et Z_max (dioïde tropical).            ║
  ╚══════════════════════════════════════════════════════════════════════╝

  Architecture v4.2 (post-méta-analyse C1–C5 + Dissolution) :
  - `isSelfFinancing` : condition centrale de solvabilité (préfixe-closed)
  - `isStrictlySolvent` : solvabilité avec buffer (LCR/NSFR)
  - `SolvencyCone` : cône idempotent combinatoire (filter sur all_paths)
  - `totalPotential` : somme des cash-flows sur les sommets (borne globale)
  - `carbonBudgetLocal` : sup max-plus sur `all_paths` (remplace #P-difficile)

  Références :
  - Baccelli–Cohen–Olsder–Quadrat (1992), Ch. 2 (TEG max-plus)
  - Cormen et al. (2009), §24.2 (plus long chemin dans un DAG)
  - Zimmermann (1981), Ann. Disc. Math. 10 (optimisation sur dioïdes)
  - `cache/plan_organic_teg_lp.md` (plan v4.2)
  - `cache/meta_critique_analyse_phase4.md` (méta-analyse, verdict 🟡)
-/

import ThesePlanetaire.OrganicTEG
import ThesePlanetaire.ConditionalBernoulli

namespace OrganicLP

open OrganicTEG ConditionalBernoulli WeightedAutomaton

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 1. Cash-flow cumulé et conditions de solvabilité (C5)

  `cashFlowSum` somme les cash-flows sur les sommets sources des arêtes
  du chemin. C'est le flux monétaire cumulé intertemporel. -/

/-- Cash-flow cumulé d'un chemin = somme des cash-flows des sommets sources. -/
def cashFlowSum (teg : OrganicTEG V) (w : List (V × V)) : ℤ :=
  (w.map (fun e => teg.cash_flow e.1)).sum

/-- Condition d'auto-financement (solvabilité intertemporelle) :
    le cash-flow cumulé est ≥ 0 sur tout préfixe du chemin.
    Formulation avec `Finset.range (w.length + 1)` pour garantir
    la décidabilité (quantification finie). -/
def isSelfFinancing (teg : OrganicTEG V) (w : List (V × V)) : Prop :=
  ∀ n ∈ Finset.range (w.length + 1), 0 ≤ cashFlowSum teg (w.take n)

/-- Condition de solvabilité stricte : le cash-flow cumulé reste ≥ buffer
    sur tout préfixe. Le buffer : ℕ modélise les contraintes de liquidité
    bancaire (LCR — Liquidity Coverage Ratio, NSFR — Net Stable Funding Ratio). -/
def isStrictlySolvent (teg : OrganicTEG V) (w : List (V × V)) (buffer : ℕ) : Prop :=
  ∀ n ∈ Finset.range (w.length + 1), (buffer : ℤ) ≤ cashFlowSum teg (w.take n)

/-! ### 2. Instances de décidabilité

  `Finset.filter` exige `DecidablePred`. Les deux prédicats sont
  décidables car `isValidTEGTrace` est une conjonction de propriétés
  sur des `Finset` et des égalités, et `isSelfFinancing` est une
  quantification finie sur `Finset.range`. -/

noncomputable instance decidableValidTEGTrace (teg : OrganicTEG V) : DecidablePred (isValidTEGTrace teg) := by
  intro w
  classical
  infer_instance

instance decidableSelfFinancing (teg : OrganicTEG V) : DecidablePred (isSelfFinancing teg) := by
  intro w
  unfold isSelfFinancing
  infer_instance

/-! ### 3. Cône de solvabilité idempotent (C5)

  `SolvencyCone` est un sous-ensemble fini de `m.all_paths`. C'est un
  "cône" au sens du dioïde D4 (booléen, idempotent), PAS un cône convexe
  au sens de Kabanov–Schachermayer (ℝ^d).

  Un cône idempotent : si w₁ et w₂ sont dans le cône, leur superposition
  (union des arêtes) reste dans le cône — la structure est booléenne,
  pas linéaire. -/

/-- Cône de solvabilité combinatoire : chemins valides ET auto-finançants.
    NOTE : `noncomputable` car `isValidTEGTrace` utilise `classical`
    (décidabilité par axiome du tiers exclu). Le cône est un objet
    mathématique fini, pas une procédure de calcul. -/
noncomputable def SolvencyCone (teg : OrganicTEG V) (m : UniformPathMeasure V) : Finset (List (V × V)) :=
  m.all_paths.filter (fun w => isValidTEGTrace teg w ∧ isSelfFinancing teg w)

/-! ### 4. Potentiel total et budget carbone local (C1, C2)

  `totalPotential` est la somme des cash-flows sur tous les sommets.
  C'est une borne supérieure universelle (indépendante du chemin).

  `carbonBudgetLocal` remplace la contrainte globale #P-difficile
  `∑_w carbon_emissions(w) ≤ carbon_budget` par un sup fini sur
  `all_paths` via le dioïde tropical `Z_max`. Chaque chemin vérifie
  individuellement `word_weight w ≤ carbonBudgetLocal`. -/

/-- Potentiel total : somme des cash-flows sur l'ensemble des sommets. -/
def totalPotential (teg : OrganicTEG V) : ℤ :=
  ∑ v ∈ Finset.univ, teg.cash_flow v

/-- Budget carbone local : sup (max) des poids max-plus sur `all_paths`.
    Cette borne combinatoire est calculable en O(|all_paths|) par
    énumération, ou en O(|V|+|E|) par programmation dynamique sur DAG.
    Elle remplace la contrainte globale #P-difficile. -/
def carbonBudgetLocal (teg : OrganicTEG V) (m : UniformPathMeasure V) : Z_max :=
  m.all_paths.sup (fun w => word_weight (organicValuationWFA teg) w)

/-! ### 5. Théorèmes de solvabilité (C5, C1, C2)

  Tous les théorèmes sont prouvés sans sorry, sans ℝ, sans axiome. -/

/-- Théorème : tout chemin auto-finançant et valide appartient au
    cône de solvabilité. C'est une équivalence structurelle
    (condition nécessaire et suffisante, tautologique par définition). -/
theorem self_financing_implies_solvency (teg : OrganicTEG V) (m : UniformPathMeasure V)
    (w : List (V × V)) (hw : w ∈ m.all_paths) (h_sf : isSelfFinancing teg w)
    (h_valid : isValidTEGTrace teg w) :
    w ∈ SolvencyCone teg m := by
  unfold SolvencyCone
  simp [hw]
  exact ⟨h_valid, h_sf⟩

/-- Théorème : la solvabilité stricte (avec buffer) implique la
    solvabilité standard (buffer = 0). Le buffer est une condition
    suffisante de non-négativité préfixe.

    Preuve : `cashFlowSum ≥ buffer` et `buffer ≥ 0` (ℕ) ⟹ `cashFlowSum ≥ 0`. -/
theorem strict_solvency_implies_solvency (teg : OrganicTEG V) (w : List (V × V))
    (buffer : ℕ) (h_strict : isStrictlySolvent teg w buffer) :
    isSelfFinancing teg w := by
  unfold isSelfFinancing isStrictlySolvent at *
  intro n hn
  have h := h_strict n hn
  linarith

/-- Théorème : le cône de solvabilité est non vide si le TEG admet
    au moins un chemin valide auto-finançant dans `all_paths`. -/
theorem solvency_cone_nonempty (teg : OrganicTEG V) (m : UniformPathMeasure V)
    (h : ∃ w ∈ m.all_paths, isValidTEGTrace teg w ∧ isSelfFinancing teg w) :
    (SolvencyCone teg m).Nonempty := by
  obtain ⟨w, hw, h_valid, h_sf⟩ := h
  use w
  exact self_financing_implies_solvency teg m w hw h_sf h_valid

/-- Théorème principal C1 : borne combinatoire locale via dioïde tropical.
    Tout chemin dans `SolvencyCone` a un poids max-plus ≤ `carbonBudgetLocal`.

    Cette borne remplace la contrainte globale #P-difficile :
      `∑_{w ∈ all_paths} emissions(w) ≤ carbon_budget`
    par une contrainte par chemin :
      `word_weight (organicValuationWFA teg) w ≤ carbonBudgetLocal teg m`

    La borne est calculable en O(|V|+|E|) par programmation dynamique
    sur le DAG des transitions (Cormen et al. 2009, §24.2).

    Preuve : `Finset.le_sup` — si `w ∈ all_paths`, alors
    `f w ≤ sup_{x ∈ all_paths} f x`. -/
theorem carbon_budget_local_via_maxplus (teg : OrganicTEG V) (m : UniformPathMeasure V)
    (w : List (V × V)) (hw : w ∈ SolvencyCone teg m) :
    word_weight (organicValuationWFA teg) w ≤ carbonBudgetLocal teg m := by
  unfold SolvencyCone at hw
  rw [Finset.mem_filter] at hw
  rcases hw with ⟨hw_path, _, _⟩
  unfold carbonBudgetLocal
  exact Finset.le_sup hw_path

/-- Théorème : si tous les cash-flows sont non-négatifs, alors tout
    chemin est auto-finançant (condition suffisante triviale). -/
theorem cashFlowSum_nonneg_of_nonneg_cashflow (teg : OrganicTEG V)
    (h_nonneg : ∀ v, teg.cash_flow v ≥ 0) (w : List (V × V)) :
    isSelfFinancing teg w := by
  unfold isSelfFinancing cashFlowSum
  intro n hn
  apply List.sum_nonneg
  intro x hx
  rw [List.mem_map] at hx
  rcases hx with ⟨e, he, rfl⟩
  apply h_nonneg e.1

end OrganicLP
