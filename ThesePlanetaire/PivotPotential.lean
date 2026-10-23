/-
  ThesePlanetaire/PivotPotential.lean
  Pivot d'admission, phase 1 (lecture crédit/reconstitution) : potentiel amont max-plus.

  Provenance : scratch PivotPotential_scratch, porté verbatim (2026-10-01). Plan :
  `~/.claude/plans/witty-dazzling-manatee.md` (« NOUVEAU PLAN », amendements A/B) ;
  analyse : `cache/analyse_tension_A7_G3a_observation_vs_admission_2026-10-01.md` §8-§9.

  `DualDAG.vertex_load` ne somme que les arêtes SORTANTES du sommet testé contre
  `pool.holdings`, un champ STATIQUE jamais reconstitué par une arête entrante. Ce module
  ajoute au test d'admission un crédit `π_S(e.1)` lu sur les arêtes AMONT déjà admises :
  le poids max-plus (somme des demandes) d'une marche de longueur ≤ |V| se terminant en
  `e.1` dans l'état admis `S`, calculé par `KarpAlgorithm.karp_d` (aucune machinerie
  max-plus nouvelle). Le test reste côté SOURCE (`e.1`), comme `isAdmissible`.

  ★ Lecture crédit = NON conservative (décision B, phase 1) : le crédit d'une chaîne
  `y → z → m` vaut la somme des deux demandes en `m`, pas ce que `m` reçoit
  directement. Sur un état admis CYCLIQUE à poids positifs, la borne de longueur
  `|V|` est un artefact (le crédit dépend du nombre de sommets, pas seulement du
  graphe admis). Phase 2 (vrai coût réduit, π aux deux extrémités, ancrée sur
  `NumeraireExistence.potentiel_iff_max_cycle_mean_nonpos`) : non construite ici.

  Résultats :
  - `upstreamPotential_insert_eq` : ajouter une arête `a` ne change pas le crédit en `r`
    si `a.2` n'atteint pas `r` (pièce porteuse de `PivotCommutation`).
  - `pivotAdmissible_empty_iff` / `isAdmissible_imp_pivotAdmissible` : conservativité
    (relaxation de `isAdmissible` à CHAQUE état — pas d'inclusion des folds pour autant :
    admettre plus tôt peut bloquer plus tard).
  - `pivot_order_dependent_despite_edge_indep` : `edge_indep` (aucun sommet partagé) ne
    suffit pas à la commutation sous ce modèle.
-/

import Mathlib.Tactic
import ThesePlanetaire.Basic
import ThesePlanetaire.DualDAG
import ThesePlanetaire.EdgeIndependence
import ThesePlanetaire.KarpAlgorithm

namespace PivotPotential

open DualDAG (FuturePool vertex_load admissionFoldP isAdmissible isAdmissible_iff_load)
open KarpAlgorithm (EdgeSet karp_d)

/-! ### 1. Reachability — réutilise `Basic.Reachable` (Basic.lean non modifié)

  `Reachable` (Basic.lean:122) n'a ni `trans` ni monotonie dans le dépôt ; on les
  ajoute ici comme code neuf, sous des noms préfixés pour ne pas polluer l'espace
  racine. -/

section Reach

variable {V : Type*}

/-- Atteignabilité dans le graphe porté par un ensemble d'arêtes. -/
abbrev reachesIn (S : Finset (V × V)) (u v : V) : Prop :=
  Reachable (⟨S⟩ : DirectedGraph V) u v

theorem reachable_trans {g : DirectedGraph V} {u v w : V}
    (h1 : Reachable g u v) (h2 : Reachable g v w) : Reachable g u w := by
  revert h2
  induction h1 with
  | refl _ => exact id
  | step x y _ hxy _ ih => exact fun h2 => Reachable.step x y w hxy (ih h2)

/-- Prolonger un chemin par une arête finale. -/
theorem reachable_snoc {g : DirectedGraph V} {u v w : V}
    (h : Reachable g u v) (hvw : (v, w) ∈ g.edges) : Reachable g u w :=
  reachable_trans h (Reachable.step v w w hvw (Reachable.refl w))

/-- Monotonie de l'atteignabilité en l'ensemble d'arêtes. -/
theorem reachable_mono {g g' : DirectedGraph V} (h_sub : g.edges ⊆ g'.edges) {u v : V}
    (h : Reachable g u v) : Reachable g' u v := by
  induction h with
  | refl x => exact Reachable.refl x
  | step x y z hxy _ ih => exact Reachable.step x y z (h_sub hxy) ih

end Reach

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### 2. Pont vers `KarpAlgorithm` et potentiel amont -/

/-- Graphe pondéré de l'état admis : poids `demands e` sur les arêtes admises, `⊥` ailleurs
    (même idiome que `matrixToEdgeSet`/`tegToZmaxMatrix`). `karp_d` ne lit que `weight`. -/
def admissionEdgeSet (demands : V × V → ℤ) (S : ActivationState V) : EdgeSet V where
  edges := S
  weight := fun e => if e ∈ S then Z_max.ofInt (demands e) else Z_max.negInf

/-- Crédit amont en `r` : sup max-plus des poids des marches de longueur ≤ |V| se
    terminant en `r` dans l'état admis `S`, depuis n'importe quel sommet. La marche vide
    (`k = 0`, départ `r`) donne le plancher `1 = ofInt 0`. `maxCycleMeanKarp` n'est
    délibérément pas utilisé. -/
def upstreamPotential (demands : V × V → ℤ) (S : ActivationState V) (r : V) : Z_max :=
  (Finset.univ : Finset V).sup (fun u => (Finset.range (Fintype.card V + 1)).sup
    (fun k => karp_d (admissionEdgeSet demands S) u k r))

/-- Admission avec crédit amont : généralise `isAdmissible_iff_load` (DualDAG.lean:1247).
    Comparaison dans `ℤ` via `Z_max.toInt` (l'ordre de `Z_max` n'est décidable que
    classiquement, Z_max.lean:183). -/
def pivotAdmissible (pool : FuturePool V) (demands : V × V → ℤ) (S : ActivationState V)
    (e : V × V) : Prop :=
  vertex_load demands (S ∪ {e}) e.1 ≤
    pool.holdings e.1 + Z_max.toInt (upstreamPotential demands S e.1)

instance pivotAdmissible.decidable (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V) (e : V × V) : Decidable (pivotAdmissible pool demands S e) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Fold test-and-keep sous `pivotAdmissible` : instance de `admissionFoldP`
    (DualDAG.lean:852) — jamais branché sur `coupled_operator` (non monotone,
    `coupled_operator_not_monotone`). -/
def pivotAdmissionFold (pool : FuturePool V) (demands : V × V → ℤ)
    (edges : List (V × V)) : ActivationState V :=
  admissionFoldP (pivotAdmissible pool demands) edges

/-! ### 3. Dépliage de `karp_d` et lemmes de poids -/

lemma karp_d_zero (E : EdgeSet V) (s v : V) :
    karp_d E s 0 v = if v = s then (1 : Z_max) else Z_max.negInf := by
  rw [karp_d, if_pos rfl]

lemma karp_d_succ (E : EdgeSet V) (s : V) (k : ℕ) (v : V) :
    karp_d E s (k + 1) v = (Finset.univ : Finset V).sup (fun u => karp_d E s k u * E.weight (u, v)) := by
  rw [karp_d, if_neg (Nat.succ_ne_zero k), show (k + 1) - 1 = k from by omega]

omit [Fintype V] in
lemma weight_of_mem (demands : V × V → ℤ) (S : ActivationState V) {e : V × V} (h : e ∈ S) :
    (admissionEdgeSet demands S).weight e = Z_max.ofInt (demands e) := by
  simp only [admissionEdgeSet, if_pos h]

omit [Fintype V] in
lemma weight_of_not_mem (demands : V × V → ℤ) (S : ActivationState V) {e : V × V} (h : e ∉ S) :
    (admissionEdgeSet demands S).weight e = 0 := by
  simp only [admissionEdgeSet, if_neg h, Z_max.zero_eq]

/-! ### 4. Ponts `Z_max` ↔ `ℤ` (via `toWithBot_le_iff`, Z_max.lean:298) -/

lemma ofInt_le_ofInt {m n : ℤ} : Z_max.ofInt m ≤ Z_max.ofInt n ↔ m ≤ n := by
  rw [← Z_max.toWithBot_le_iff]
  simp [Z_max.Z_max_toWithBot]

lemma le_toInt_of_ofInt_le {n : ℤ} {z : Z_max} (h : Z_max.ofInt n ≤ z) : n ≤ z.toInt := by
  cases z with
  | negInf =>
    rw [← Z_max.toWithBot_le_iff] at h
    exact absurd h (WithBot.not_coe_le_bot n)
  | ofInt m => exact ofInt_le_ofInt.mp h

lemma toInt_le_of_le_ofInt {n : ℤ} {z : Z_max} (h : z ≤ Z_max.ofInt n) (h0 : 0 ≤ n) :
    z.toInt ≤ n := by
  cases z with
  | negInf => exact h0
  | ofInt m => exact ofInt_le_ofInt.mp h

/-! ### 5. Localité du crédit : ajouter `a` ne touche que l'aval de `a.2`

  Pièce porteuse de `PivotCommutation`. Induction sur la longueur de marche, cas par
  prédécesseur : une marche de poids non `⊥` vers `v` qui emprunte `a` place `v` en aval
  de `a.2` ; si `a.2` n'atteint pas `v`, aucune marche vers `v` ne voit `a`. -/

/-- Pour tout `v` hors de l'aval de `a.2` (dans `S ∪ {a}`), `karp_d` est inchangé par
    l'insertion de `a`. -/
lemma karp_d_insert_eq (demands : V × V → ℤ) (S : ActivationState V) (a : V × V) (s : V) :
    ∀ (k : ℕ) (v : V), ¬ reachesIn (S ∪ {a}) a.2 v →
      karp_d (admissionEdgeSet demands (S ∪ {a})) s k v =
        karp_d (admissionEdgeSet demands S) s k v := by
  intro k
  induction k with
  | zero => intro v _; rw [karp_d_zero, karp_d_zero]
  | succ k ih =>
    intro v hv
    rw [karp_d_succ, karp_d_succ]
    refine Finset.sup_congr rfl (fun u _ => ?_)
    have hne : (u, v) ≠ a := by
      rintro rfl
      exact hv (Reachable.refl v)
    have hw : (admissionEdgeSet demands (S ∪ {a})).weight (u, v) =
        (admissionEdgeSet demands S).weight (u, v) := by
      simp only [admissionEdgeSet, Finset.mem_union, Finset.mem_singleton, hne, or_false]
    rw [hw]
    by_cases huv : (u, v) ∈ S
    · have hu : ¬ reachesIn (S ∪ {a}) a.2 u := fun hu =>
        hv (reachable_snoc hu (Finset.mem_union_left _ huv))
      rw [ih u hu]
    · rw [weight_of_not_mem demands S huv, Z_max.mul_zero, Z_max.mul_zero]

/-- ★ Localité du crédit amont : si `a.2` n'atteint pas `r` dans `S ∪ {a}`, admettre `a`
    ne change pas `π(r)`. -/
theorem upstreamPotential_insert_eq (demands : V × V → ℤ) (S : ActivationState V)
    (a : V × V) (r : V) (h : ¬ reachesIn (S ∪ {a}) a.2 r) :
    upstreamPotential demands (S ∪ {a}) r = upstreamPotential demands S r := by
  unfold upstreamPotential
  refine Finset.sup_congr rfl (fun u _ => Finset.sup_congr rfl (fun k _ => ?_))
  exact karp_d_insert_eq demands S a u k r h

/-! ### 6. Plancher, état vide, conservativité -/

/-- Plancher : la marche vide en `r` donne `π(r) ≥ 1 = ofInt 0`. -/
lemma one_le_upstreamPotential (demands : V × V → ℤ) (S : ActivationState V) (r : V) :
    (1 : Z_max) ≤ upstreamPotential demands S r := by
  unfold upstreamPotential
  have h0 : karp_d (admissionEdgeSet demands S) r 0 r = 1 := by rw [karp_d_zero, if_pos rfl]
  calc (1 : Z_max) = karp_d (admissionEdgeSet demands S) r 0 r := h0.symm
    _ ≤ (Finset.range (Fintype.card V + 1)).sup
          (fun k => karp_d (admissionEdgeSet demands S) r k r) :=
        Finset.le_sup (f := fun k => karp_d (admissionEdgeSet demands S) r k r)
          (Finset.mem_range.mpr (Nat.succ_pos _))
    _ ≤ _ := Finset.le_sup (f := fun u => (Finset.range (Fintype.card V + 1)).sup
          (fun k => karp_d (admissionEdgeSet demands S) u k r)) (Finset.mem_univ r)

lemma toInt_upstreamPotential_nonneg (demands : V × V → ℤ) (S : ActivationState V) (r : V) :
    0 ≤ (upstreamPotential demands S r).toInt :=
  le_toInt_of_ofInt_le (one_le_upstreamPotential demands S r)

/-- Sur l'état vide, toute marche non vide a un poids `⊥`. -/
lemma karp_d_empty_succ (demands : V × V → ℤ) (s : V) (k : ℕ) (v : V) :
    karp_d (admissionEdgeSet demands ∅) s (k + 1) v = 0 := by
  rw [karp_d_succ]
  refine le_antisymm (Finset.sup_le fun u _ => ?_) bot_le
  rw [weight_of_not_mem demands ∅ (Finset.notMem_empty _), Z_max.mul_zero]

/-- Sur l'état vide, le crédit est nul : `π_∅(r) = 1 = ofInt 0`. -/
theorem upstreamPotential_empty (demands : V × V → ℤ) (r : V) :
    upstreamPotential demands ∅ r = 1 := by
  refine le_antisymm ?_ (one_le_upstreamPotential demands ∅ r)
  unfold upstreamPotential
  refine Finset.sup_le fun u _ => Finset.sup_le fun k _ => ?_
  cases k with
  | zero =>
    rw [karp_d_zero]
    split_ifs
    · exact le_refl _
    · exact bot_le
  | succ k => rw [karp_d_empty_succ]; exact bot_le

/-- Conservativité depuis ∅ : sans arête amont admise, le pivot coïncide avec `isAdmissible`. -/
theorem pivotAdmissible_empty_iff (pool : FuturePool V) (demands : V × V → ℤ) (e : V × V) :
    pivotAdmissible pool demands ∅ e ↔ isAdmissible pool demands ∅ e := by
  rw [isAdmissible_iff_load]
  unfold pivotAdmissible
  rw [upstreamPotential_empty]
  have h1 : Z_max.toInt (1 : Z_max) = 0 := rfl
  rw [h1, add_zero]

/-- Conservativité à CHAQUE état : `pivotAdmissible` relâche `isAdmissible` pas à pas.
    (N'entraîne PAS `admissionFold ⊆ pivotAdmissionFold` : admettre plus tôt peut
    bloquer plus tard — cf. `pivot_order_dependent_despite_edge_indep`.) -/
theorem isAdmissible_imp_pivotAdmissible (pool : FuturePool V) (demands : V × V → ℤ)
    (S : ActivationState V) (e : V × V) (h : isAdmissible pool demands S e) :
    pivotAdmissible pool demands S e := by
  rw [isAdmissible_iff_load] at h
  unfold pivotAdmissible
  have := toInt_upstreamPotential_nonneg demands S e.1
  omega

/-! ### 7. Valeurs concrètes : marches de longueur 1 et 2

  `karp_d` est défini par récursion bien fondée (`k - 1`) : pas de `decide`, tout passe
  par `karp_d_zero`/`karp_d_succ` (idiome `rw`, KarpAlgorithm.lean:160-188). -/

lemma karp_d_one (E : EdgeSet V) (s v : V) : karp_d E s 1 v = E.weight (s, v) := by
  show karp_d E s (0 + 1) v = _
  rw [karp_d_succ]
  refine le_antisymm (Finset.sup_le fun u _ => ?_) ?_
  · rw [karp_d_zero]
    split_ifs with h
    · rw [h, Z_max.one_mul]
    · rw [← Z_max.zero_eq, Z_max.zero_mul]; exact bot_le
  · calc E.weight (s, v) = karp_d E s 0 s * E.weight (s, v) := by
          rw [karp_d_zero, if_pos rfl, Z_max.one_mul]
      _ ≤ _ := Finset.le_sup (f := fun u => karp_d E s 0 u * E.weight (u, v)) (Finset.mem_univ s)

/-- Une marche de longueur 2 dans l'état admis minore `karp_d … 2`. -/
lemma ofInt_add_le_karp_d_two (demands : V × V → ℤ) (S : ActivationState V) (s w v : V)
    (h1 : (s, w) ∈ S) (h2 : (w, v) ∈ S) :
    Z_max.ofInt (demands (s, w) + demands (w, v)) ≤ karp_d (admissionEdgeSet demands S) s 2 v := by
  show _ ≤ karp_d _ s (1 + 1) v
  rw [karp_d_succ]
  calc Z_max.ofInt (demands (s, w) + demands (w, v))
      = karp_d (admissionEdgeSet demands S) s 1 w * (admissionEdgeSet demands S).weight (w, v) := by
        rw [karp_d_one, weight_of_mem demands S h1, weight_of_mem demands S h2]; rfl
    _ ≤ _ := Finset.le_sup (f := fun u => karp_d (admissionEdgeSet demands S) s 1 u *
          (admissionEdgeSet demands S).weight (u, v)) (Finset.mem_univ w)

lemma karp_d_le_upstreamPotential (demands : V × V → ℤ) (S : ActivationState V) (s : V)
    {k : ℕ} (hk : k ≤ Fintype.card V) (r : V) :
    karp_d (admissionEdgeSet demands S) s k r ≤ upstreamPotential demands S r :=
  (Finset.le_sup (f := fun k => karp_d (admissionEdgeSet demands S) s k r)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))).trans
    (Finset.le_sup (f := fun u => (Finset.range (Fintype.card V + 1)).sup
      (fun k => karp_d (admissionEdgeSet demands S) u k r)) (Finset.mem_univ s))

/-- État « sans chaînage » (aucune arête admise ne part de la cible d'une autre) : toute
    marche de longueur ≥ 2 a un poids `⊥`. -/
lemma karp_d_ge_two_of_no_chain (demands : V × V → ℤ) (S : ActivationState V)
    (h_nc : ∀ e ∈ S, ∀ f ∈ S, e.2 ≠ f.1) (s : V) :
    ∀ k, 2 ≤ k → ∀ v, karp_d (admissionEdgeSet demands S) s k v = 0 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro v
    show karp_d _ s (1 + 1) v = 0
    rw [karp_d_succ]
    refine le_antisymm (Finset.sup_le fun u _ => ?_) bot_le
    rw [karp_d_one]
    by_cases h1 : (s, u) ∈ S
    · by_cases h2 : (u, v) ∈ S
      · exact (h_nc _ h1 _ h2 rfl).elim
      · rw [weight_of_not_mem demands S h2, Z_max.mul_zero]
    · rw [weight_of_not_mem demands S h1, Z_max.zero_mul]
  | succ k _ ih =>
    intro v
    rw [karp_d_succ]
    refine le_antisymm (Finset.sup_le fun u _ => ?_) bot_le
    rw [ih u, Z_max.zero_mul]

/-- Sans chaînage, le crédit en `r` est majoré par le plus lourd arc entrant (et 0). -/
lemma upstreamPotential_le_of_no_chain (demands : V × V → ℤ) (S : ActivationState V)
    (h_nc : ∀ e ∈ S, ∀ f ∈ S, e.2 ≠ f.1) (r : V) (n : ℤ) (hn : 0 ≤ n)
    (hw : ∀ u, (admissionEdgeSet demands S).weight (u, r) ≤ Z_max.ofInt n) :
    upstreamPotential demands S r ≤ Z_max.ofInt n := by
  unfold upstreamPotential
  refine Finset.sup_le fun u _ => Finset.sup_le fun k _ => ?_
  rcases k with _ | _ | k
  · rw [karp_d_zero]
    split_ifs
    · exact ofInt_le_ofInt.mpr hn
    · exact bot_le
  · rw [karp_d_one]; exact hw u
  · rw [karp_d_ge_two_of_no_chain demands S h_nc u (k + 2) (by omega)]; exact bot_le

/-! ### 8. Témoin : `edge_indep` ne suffit pas sous le pivot

  `V = Fin 4`, sommets `m = 0, x = 1, y = 2, z = 3` ; arêtes `c = (z,m)`, `b = (y,z)`,
  `a = (m,x)` ; holdings `y, z ↦ 1`, `m, x ↦ 0` ; demandes 1 sauf `a ↦ 2`.
  - `[c, a, b]` : `a` testée sous `{c}`, `π(m) = 1` (arc `z → m`) : `2 > 0 + 1`, rejetée.
  - `[c, b, a]` : `a` testée sous `{c, b}`, `π(m) ≥ 2` (chemin `y → z → m`) : admise.
  `a` et `b` ne partagent aucun sommet, mais `b.2 = z` est en amont de `a.1 = m` via `c`
  — exactement ce qu'exclut `I_LP` (PivotCommutation). -/

namespace Witness

def pool : FuturePool (Fin 4) := ⟨fun v => if v = 2 ∨ v = 3 then 1 else 0, by decide⟩
def demands : Fin 4 × Fin 4 → ℤ := fun e => if e = (0, 1) then 2 else 1
def c : Fin 4 × Fin 4 := (3, 0)
def b : Fin 4 × Fin 4 := (2, 3)
def a : Fin 4 × Fin 4 := (0, 1)

end Witness

open Witness in
theorem pivot_order_dependent_despite_edge_indep :
    ∃ (pool : FuturePool (Fin 4)) (demands : Fin 4 × Fin 4 → ℤ) (c a b : Fin 4 × Fin 4),
      EdgeIndependence.edge_indep a b ∧
      pivotAdmissionFold pool demands [c, a, b] ≠ pivotAdmissionFold pool demands [c, b, a] := by
  refine ⟨pool, demands, c, a, b, by decide, ?_⟩
  have hc : pivotAdmissible pool demands ∅ c :=
    (pivotAdmissible_empty_iff pool demands c).mpr ((isAdmissible_iff_load _ _ _ _).mpr (by decide))
  have hb : pivotAdmissible pool demands (∅ ∪ {c}) b :=
    isAdmissible_imp_pivotAdmissible _ _ _ _ ((isAdmissible_iff_load _ _ _ _).mpr (by decide))
  -- `a` rejetée sous `{c}` : π(m) ≤ 1
  have ha_rej : ¬ pivotAdmissible pool demands (∅ ∪ {c}) a := by
    have hd : ∀ u : Fin 4, demands (u, a.1) ≤ 1 := by decide
    have hπ : upstreamPotential demands (∅ ∪ {c}) a.1 ≤ Z_max.ofInt 1 :=
      upstreamPotential_le_of_no_chain demands _ (by decide) a.1 1 (by norm_num) (fun u => by
        by_cases h : (u, a.1) ∈ (∅ ∪ {c} : Finset (Fin 4 × Fin 4))
        · rw [weight_of_mem _ _ h]; exact ofInt_le_ofInt.mpr (hd u)
        · rw [weight_of_not_mem _ _ h]; exact bot_le)
    have hint := toInt_le_of_le_ofInt hπ (by norm_num)
    have hload : vertex_load demands ((∅ ∪ {c}) ∪ {a}) a.1 = 2 := by decide
    have hh : pool.holdings a.1 = 0 := by decide
    unfold pivotAdmissible
    omega
  -- `a` admise sous `{c, b}` : π(m) ≥ 2
  have ha_adm : pivotAdmissible pool demands ((∅ ∪ {c}) ∪ {b}) a := by
    have h2 := le_toInt_of_ofInt_le
      ((ofInt_add_le_karp_d_two demands ((∅ ∪ {c}) ∪ {b}) 2 3 a.1 (by decide) (by decide)).trans
        (karp_d_le_upstreamPotential demands _ 2 (by simp) a.1))
    have hd : demands (2, 3) + demands (3, a.1) = 2 := by decide
    have hload : vertex_load demands (((∅ ∪ {c}) ∪ {b}) ∪ {a}) a.1 = 2 := by decide
    have hh : pool.holdings a.1 = 0 := by decide
    unfold pivotAdmissible
    omega
  unfold pivotAdmissionFold admissionFoldP
  simp only [List.foldl_cons, List.foldl_nil]
  rw [if_pos hc, if_neg ha_rej, if_pos hb, if_pos ha_adm]
  decide

end PivotPotential
