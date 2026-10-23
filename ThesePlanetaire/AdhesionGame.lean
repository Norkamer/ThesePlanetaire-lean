/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/AdhesionGame.lean
  Phase 11 (2026-10-02), étape 11b : l'adhésion des émetteurs comme jeu de coordination —
  équilibres extrêmes (Tarski), orbites de la dynamique myope, champ d'amorçage, hystérésis,
  statique comparative des voies.

  Développé d'abord en `AdhesionGame_scratch.lean` (workflow du dépôt). Plan :
  `cache/phase11_2026-10-02/plan_phase11.md` ; analyse :
  `cache/analyse_phase11_adhesion_emetteurs_2026-10-02.md` §1-2 ; sonde G1-G3
  (`cache/phase11_2026-10-02/outils/sonde_adhesion.py`) ; amont :
  `cache/adhesion_emetteurs_et_alpha_c_2026-10-02.md` Partie I.
-/

import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# Le jeu d'adhésion

Joueurs `V` (les émetteurs). `g i S` est le gain net d'adhérer pour `i` quand les **autres**
adhérents forment `S` ; il est évalué en `X \ {i}`. La meilleure réponse à `X` est
`brSet g X = {i | 0 ≤ g i (X \ {i})}` (l'égalité va à l'adhésion) ; un équilibre de Nash est un
point fixe. Sous `Supermodular g` (complémentarités stratégiques : `g i` croissant), `br g` est
monotone sur le treillis `Set V` et Tarski s'applique. Le modèle de Renn (arXiv 2608.12143 v3,
§10-12) instancie le cas symétrique, gain fonction du seul nombre d'adhérents.

1. ★ `isNash_iff_fixed`, `lfp_least_nash`, `gfp_greatest_nash`, `nash_unique_iff` : les
   équilibres forment un ensemble de borne inférieure `lfp` et supérieure `gfp` ; l'équilibre est
   unique ssi `lfp = gfp` (bistabilité ⟺ `lfp ≠ gfp`).
2. ★ `iterate_post`, `iterate_pre` (opérateur monotone quelconque sur `Set V`, `V` fini) : depuis
   `N ⊆ F N`, la dynamique myope simultanée croît et atteint en au plus `card V − ncard N` pas le
   plus petit point fixe contenant `N` ; depuis `F L ⊆ L`, elle décroît et atteint en au plus
   `ncard L` pas le plus grand point fixe contenu dans `L`.
3. ★ `lfp_eq_empty_iff` : le plus petit équilibre est vide ssi chaque gain isolé `g i ∅` est
   négatif — le noyau ne se forme pas par la seule incitation à l'entrée. `shift g H` ajoute un
   champ d'amorçage uniforme : ★ `lfp_shift_mono`, `ignition_none`, `ignition_all`.
4. ★ Hystérésis : `afterSeed g hg H` (plus grand équilibre de `g` contenu dans `lfp` du jeu
   amorcé) est la limite de la dynamique après retrait de l'amorçage (`seed_then_withdraw`) ;
   ★ `afterSeed_full` : si l'amorçage allume tout, le retrait laisse le plus grand équilibre.
   ★ `bistable_witness` : coordination à deux joueurs, `lfp = ∅`, `gfp = univ`.
5. ★ Statique comparative : `lfp_mono_gain`, `gfp_mono_gain` ; drain (`addGain`) et obligation
   (`mandate`) élargissent les équilibres extrêmes.
-/

namespace AdhesionGame

variable {V : Type*}
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ### §1. Jeu et équilibres -/

/-- Meilleure réponse à l'ensemble adhérent `X` : `i` adhère si son gain face aux autres
adhérents est positif ou nul. -/
def brSet (g : V → Set V → 𝕜) (X : Set V) : Set V := {i | 0 ≤ g i (X \ {i})}

/-- Complémentarités stratégiques : le gain d'adhérer croît avec les autres adhérents. -/
def Supermodular (g : V → Set V → 𝕜) : Prop := ∀ i, Monotone (g i)

/-- La meilleure réponse, monotone sous `Supermodular`. -/
def br (g : V → Set V → 𝕜) (hg : Supermodular g) : Set V →o Set V where
  toFun := brSet g
  monotone' _ _ h _ hi := le_trans hi (hg _ (Set.diff_subset_diff_left h))

/-- Équilibre de Nash en stratégies pures : aucun adhérent ne veut sortir, aucun non-adhérent ne
veut entrer. -/
def IsNash (g : V → Set V → 𝕜) (X : Set V) : Prop :=
  (∀ i ∈ X, 0 ≤ g i (X \ {i})) ∧ ∀ i ∉ X, g i (X \ {i}) < 0

variable {g : V → Set V → 𝕜}

omit [IsStrictOrderedRing 𝕜] in
/-- ★ Les équilibres sont les points fixes de la meilleure réponse. -/
theorem isNash_iff_fixed {X : Set V} : IsNash g X ↔ brSet g X = X := by
  constructor
  · rintro ⟨h1, h2⟩
    ext i
    by_cases hi : i ∈ X
    · exact iff_of_true (h1 i hi) hi
    · exact iff_of_false (not_le.mpr (h2 i hi)) hi
  · intro h
    exact ⟨fun i hi => (Set.ext_iff.mp h i).mpr hi,
      fun i hi => not_le.mp fun h' => hi ((Set.ext_iff.mp h i).mp h')⟩

omit [IsStrictOrderedRing 𝕜] in
theorem nash_eq_fixedPoints (hg : Supermodular g) :
    {X | IsNash g X} = Function.fixedPoints (br g hg) :=
  Set.ext fun _ => isNash_iff_fixed

omit [IsStrictOrderedRing 𝕜] in
/-- ★ Le plus petit équilibre est `lfp (br g)`. -/
theorem lfp_least_nash (hg : Supermodular g) : IsLeast {X | IsNash g X} (br g hg).lfp := by
  rw [nash_eq_fixedPoints hg]
  exact (br g hg).isLeast_lfp

omit [IsStrictOrderedRing 𝕜] in
/-- ★ Le plus grand équilibre est `gfp (br g)`. -/
theorem gfp_greatest_nash (hg : Supermodular g) : IsGreatest {X | IsNash g X} (br g hg).gfp := by
  rw [nash_eq_fixedPoints hg]
  exact (br g hg).isGreatest_gfp

omit [IsStrictOrderedRing 𝕜] in
/-- ★ **Unicité ⟺ `lfp = gfp`** ; la bistabilité est `lfp ≠ gfp`. -/
theorem nash_unique_iff (hg : Supermodular g) :
    (∃! X, IsNash g X) ↔ (br g hg).lfp = (br g hg).gfp := by
  constructor
  · rintro ⟨X, -, hX⟩
    rw [hX _ (lfp_least_nash hg).1, hX _ (gfp_greatest_nash hg).1]
  · intro h
    refine ⟨_, (lfp_least_nash hg).1, fun Y hY => le_antisymm ?_ ((lfp_least_nash hg).2 hY)⟩
    rw [h]
    exact (gfp_greatest_nash hg).2 hY

/-! ### §2. Orbites de la dynamique myope simultanée

Lemmes génériques pour un opérateur monotone `F` sur `Set V`, `V` fini. `lfpAbove F N` est le
plus petit point fixe de `X ↦ N ∪ F X`, `gfpBelow F L` le plus grand de `X ↦ L ∩ F X`. -/

section Orbits

variable (F : Set V →o Set V)

/-- `X ↦ N ∪ F X`. -/
def upOp (N : Set V) : Set V →o Set V where
  toFun X := N ∪ F X
  monotone' _ _ h := Set.union_subset_union_right _ (F.monotone h)

/-- `X ↦ L ∩ F X`. -/
def downOp (L : Set V) : Set V →o Set V where
  toFun X := L ∩ F X
  monotone' _ _ h := Set.inter_subset_inter_right _ (F.monotone h)

/-- Le plus petit point fixe de `F` au-dessus de `N` (quand `N ⊆ F N`). -/
def lfpAbove (N : Set V) : Set V := (upOp F N).lfp

/-- Le plus grand point fixe de `F` au-dessous de `L` (quand `F L ⊆ L`). -/
def gfpBelow (L : Set V) : Set V := (downOp F L).gfp

variable {N L X : Set V}

theorem lfpAbove_eq : N ∪ F (lfpAbove F N) = lfpAbove F N := (upOp F N).map_lfp

theorem gfpBelow_eq : L ∩ F (gfpBelow F L) = gfpBelow F L := (downOp F L).map_gfp

theorem subset_lfpAbove : N ⊆ lfpAbove F N := fun _ hx => (lfpAbove_eq F).le (Or.inl hx)

theorem gfpBelow_subset : gfpBelow F L ⊆ L := fun _ hx => ((gfpBelow_eq F).ge hx).1

theorem lfpAbove_least (hN : N ⊆ X) (hX : F X ⊆ X) : lfpAbove F N ⊆ X :=
  OrderHom.lfp_le _ (Set.union_subset hN hX)

theorem gfpBelow_greatest (hL : X ⊆ L) (hX : X ⊆ F X) : X ⊆ gfpBelow F L :=
  OrderHom.le_gfp _ (Set.subset_inter hL hX)

theorem lfpAbove_fixed (hN : N ⊆ F N) : F (lfpAbove F N) = lfpAbove F N := by
  refine le_antisymm (fun _ hx => (lfpAbove_eq F).le (Or.inr hx)) fun x hx => ?_
  rcases (lfpAbove_eq F).ge hx with hx | hx
  · exact F.monotone (subset_lfpAbove F) (hN hx)
  · exact hx

theorem gfpBelow_fixed (hL : F L ⊆ L) : F (gfpBelow F L) = gfpBelow F L := by
  refine le_antisymm (fun x hx => (gfpBelow_eq F).le ⟨?_, hx⟩)
    fun _ hx => ((gfpBelow_eq F).ge hx).2
  exact hL (F.monotone (gfpBelow_subset F) hx)

theorem iterate_succ_subset (hN : N ⊆ F N) : ∀ k, (⇑F)^[k] N ⊆ F ((⇑F)^[k] N)
  | 0 => hN
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    exact F.monotone (iterate_succ_subset hN k)

theorem iterate_succ_supset (hL : F L ⊆ L) : ∀ k, F ((⇑F)^[k] L) ⊆ (⇑F)^[k] L
  | 0 => hL
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    exact F.monotone (iterate_succ_supset hL k)

theorem subset_iterate (hN : N ⊆ F N) : ∀ k, N ⊆ (⇑F)^[k] N
  | 0 => le_rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    exact (subset_iterate hN k).trans (iterate_succ_subset F hN k)

theorem iterate_subset_of (hNX : N ⊆ X) (hX : F X ⊆ X) : ∀ k, (⇑F)^[k] N ⊆ X
  | 0 => hNX
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    exact (F.monotone (iterate_subset_of hNX hX k)).trans hX

theorem subset_iterate_of (hXL : X ⊆ L) (hX : X ⊆ F X) : ∀ k, X ⊆ (⇑F)^[k] L
  | 0 => hXL
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    exact hX.trans (F.monotone (subset_iterate_of hXL hX k))

theorem iterate_fixed_of_le {x : Set V} {m k : ℕ} (hm : F ((⇑F)^[m] x) = (⇑F)^[m] x)
    (hk : m ≤ k) : (⇑F)^[k] x = (⇑F)^[m] x := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [add_comm, Function.iterate_add_apply, Function.iterate_fixed hm]

theorem lfpAbove_empty : lfpAbove F ∅ = F.lfp :=
  le_antisymm (lfpAbove_least F (Set.empty_subset _) F.map_lfp.le)
    (F.lfp_le (lfpAbove_fixed F (Set.empty_subset _)).le)

theorem gfpBelow_univ : gfpBelow F Set.univ = F.gfp :=
  le_antisymm (F.le_gfp (gfpBelow_fixed F (Set.subset_univ _)).ge)
    (gfpBelow_greatest F (Set.subset_univ _) F.map_gfp.ge)

variable [Finite V]

/-- Croissance : tant que la suite n'est pas fixe, elle gagne un élément par pas. -/
theorem iterate_post_card (hN : N ⊆ F N) :
    ∀ m, F ((⇑F)^[m] N) = (⇑F)^[m] N ∨ N.ncard + m ≤ ((⇑F)^[m] N).ncard
  | 0 => Or.inr (by simp)
  | m + 1 => by
    rw [Function.iterate_succ_apply']
    by_cases he : F ((⇑F)^[m] N) = (⇑F)^[m] N
    · exact Or.inl (by rw [he, he])
    · right
      rcases iterate_post_card hN m with h | h
      · exact absurd h he
      · have hs : (⇑F)^[m] N ⊂ F ((⇑F)^[m] N) :=
          Set.ssubset_iff_subset_ne.mpr ⟨iterate_succ_subset F hN m, Ne.symm he⟩
        have := Set.ncard_lt_ncard hs (Set.toFinite _)
        omega

/-- Décroissance : tant que la suite n'est pas fixe, elle perd un élément par pas. -/
theorem iterate_pre_card (hL : F L ⊆ L) :
    ∀ m, F ((⇑F)^[m] L) = (⇑F)^[m] L ∨ ((⇑F)^[m] L).ncard + m ≤ L.ncard
  | 0 => Or.inr (by simp)
  | m + 1 => by
    rw [Function.iterate_succ_apply']
    by_cases he : F ((⇑F)^[m] L) = (⇑F)^[m] L
    · exact Or.inl (by rw [he, he])
    · right
      rcases iterate_pre_card hL m with h | h
      · exact absurd h he
      · have hs : F ((⇑F)^[m] L) ⊂ (⇑F)^[m] L :=
          Set.ssubset_iff_subset_ne.mpr ⟨iterate_succ_supset F hL m, he⟩
        have := Set.ncard_lt_ncard hs (Set.toFinite _)
        omega

/-- ★ **Orbite croissante** : depuis `N ⊆ F N`, après `card V − ncard N` pas (et au-delà), la
dynamique est au plus petit point fixe contenant `N`. -/
theorem iterate_post (hN : N ⊆ F N) {k : ℕ} (hk : Nat.card V - N.ncard ≤ k) :
    (⇑F)^[k] N = lfpAbove F N := by
  set m := Nat.card V - N.ncard
  have hfix : F ((⇑F)^[m] N) = (⇑F)^[m] N := by
    rcases iterate_post_card F hN m with h | h
    · exact h
    · have h1 := Set.ncard_le_card N
      have h2 := Set.ncard_le_card (F ((⇑F)^[m] N))
      exact (Set.eq_of_subset_of_ncard_le (iterate_succ_subset F hN m) (by omega)
        (Set.toFinite _)).symm
  rw [iterate_fixed_of_le F hfix hk]
  exact le_antisymm (iterate_subset_of F (subset_lfpAbove F) (lfpAbove_fixed F hN).le m)
    (lfpAbove_least F (subset_iterate F hN m) hfix.le)

/-- ★ **Orbite décroissante** : depuis `F L ⊆ L`, après `ncard L` pas (et au-delà), la
dynamique est au plus grand point fixe contenu dans `L`. -/
theorem iterate_pre (hL : F L ⊆ L) {k : ℕ} (hk : L.ncard ≤ k) :
    (⇑F)^[k] L = gfpBelow F L := by
  set m := L.ncard
  have hfix : F ((⇑F)^[m] L) = (⇑F)^[m] L := by
    rcases iterate_pre_card F hL m with h | h
    · exact h
    · exact Set.eq_of_subset_of_ncard_le (iterate_succ_supset F hL m) (by omega)
        (Set.toFinite _)
  rw [iterate_fixed_of_le F hfix hk]
  exact le_antisymm (gfpBelow_greatest F (iterate_subset_of F le_rfl hL m) hfix.ge)
    (subset_iterate_of F (gfpBelow_subset F) (gfpBelow_fixed F hL).ge m)

/-- ★ Depuis `∅`, `card V` pas atteignent `lfp`. -/
theorem iterate_lfp : (⇑F)^[Nat.card V] ∅ = F.lfp := by
  rw [iterate_post F (Set.empty_subset _) (Nat.sub_le _ _), lfpAbove_empty]

/-- ★ Depuis `univ`, `card V` pas atteignent `gfp`. -/
theorem iterate_gfp : (⇑F)^[Nat.card V] Set.univ = F.gfp := by
  rw [iterate_pre F (Set.subset_univ _) (Set.ncard_univ V).le, gfpBelow_univ]

end Orbits

/-! ### §3. Statique comparative et champ d'amorçage -/

theorem lfp_mono_of_le {F G : Set V →o Set V} (h : ∀ X, F X ⊆ G X) : F.lfp ⊆ G.lfp :=
  F.lfp_le ((h _).trans G.map_lfp.le)

theorem gfp_mono_of_le {F G : Set V →o Set V} (h : ∀ X, F X ⊆ G X) : F.gfp ⊆ G.gfp :=
  G.le_gfp (F.map_gfp.ge.trans (h _))

omit [IsStrictOrderedRing 𝕜] in
/-- ★ Un gain plus élevé élargit la meilleure réponse. -/
theorem br_le_of_gain_le {g' : V → Set V → 𝕜} (h : ∀ i S, g i S ≤ g' i S) (X : Set V) :
    brSet g X ⊆ brSet g' X :=
  fun i hi => le_trans hi (h i _)

omit [IsStrictOrderedRing 𝕜] in
/-- ★ … donc le plus petit équilibre. -/
theorem lfp_mono_gain {g' : V → Set V → 𝕜} (hg : Supermodular g) (hg' : Supermodular g')
    (h : ∀ i S, g i S ≤ g' i S) : (br g hg).lfp ⊆ (br g' hg').lfp :=
  lfp_mono_of_le (br_le_of_gain_le h)

omit [IsStrictOrderedRing 𝕜] in
/-- ★ … et le plus grand. -/
theorem gfp_mono_gain {g' : V → Set V → 𝕜} (hg : Supermodular g) (hg' : Supermodular g')
    (h : ∀ i S, g i S ≤ g' i S) : (br g hg).gfp ⊆ (br g' hg').gfp :=
  gfp_mono_of_le (br_le_of_gain_le h)

/-- Champ d'amorçage uniforme `H` (subvention, ou obligation transitoire). -/
def shift (g : V → Set V → 𝕜) (H : 𝕜) : V → Set V → 𝕜 := fun i S => g i S + H

theorem Supermodular.shift (hg : Supermodular g) (H : 𝕜) : Supermodular (shift g H) :=
  fun i _ _ h => by
    have := hg i h
    simp only [AdhesionGame.shift]
    linarith

/-- ★ L'ensemble des champs qui allument (un noyau `N` donné, ou tout) est un ensemble
supérieur. -/
theorem lfp_shift_mono (hg : Supermodular g) {H H' : 𝕜} (hH : H ≤ H') :
    (br (shift g H) (hg.shift H)).lfp ⊆ (br (shift g H') (hg.shift H')).lfp :=
  lfp_mono_gain _ _ fun _ _ => by simp only [shift]; linarith

omit [IsStrictOrderedRing 𝕜] in
/-- ★ (E3) **Le noyau ne se forme pas par la seule incitation à l'entrée** : le plus petit
équilibre est vide ssi tout gain isolé est négatif. -/
theorem lfp_eq_empty_iff (hg : Supermodular g) : (br g hg).lfp = ∅ ↔ ∀ i, g i ∅ < 0 := by
  constructor
  · intro h i
    have h0 := (br g hg).map_lfp
    rw [h] at h0
    refine not_le.mp fun hi => ?_
    have : i ∈ br g hg ∅ := by
      show 0 ≤ g i (∅ \ {i})
      rwa [Set.empty_diff]
    rw [h0] at this
    exact this
  · intro h
    refine Set.subset_empty_iff.mp ((br g hg).lfp_le fun i hi => ?_)
    have : 0 ≤ g i (∅ \ {i}) := hi
    rw [Set.empty_diff] at this
    exact absurd this (not_le.mpr (h i))

omit [IsStrictOrderedRing 𝕜] in
theorem lfp_eq_univ_of (hg : Supermodular g) (h : ∀ i, 0 ≤ g i ∅) : (br g hg).lfp = Set.univ := by
  refine Set.eq_univ_of_forall fun i => ?_
  rw [← (br g hg).map_lfp]
  refine (br g hg).monotone (Set.empty_subset _) ?_
  show 0 ≤ g i (∅ \ {i})
  rw [Set.empty_diff]
  exact h i

/-- ★ Encadrement, bas : un champ inférieur à tous les coûts d'entrée `c_i = −g i ∅` n'allume
rien. -/
theorem ignition_none (hg : Supermodular g) {H : 𝕜} (h : ∀ i, g i ∅ + H < 0) :
    (br (shift g H) (hg.shift H)).lfp = ∅ :=
  (lfp_eq_empty_iff _).mpr h

/-- ★ Encadrement, haut : un champ supérieur à tous les coûts d'entrée allume tout. -/
theorem ignition_all (hg : Supermodular g) {H : 𝕜} (h : ∀ i, 0 ≤ g i ∅ + H) :
    (br (shift g H) (hg.shift H)).lfp = Set.univ :=
  lfp_eq_univ_of _ h

/-! ### §4. Hystérésis : amorcer, puis retirer -/

/-- Après amorçage `H` (la dynamique amorcée monte jusqu'à `lfp` du jeu amorcé), puis retrait :
le plus grand équilibre de `g` contenu dans l'état atteint. -/
def afterSeed (g : V → Set V → 𝕜) (hg : Supermodular g) (H : 𝕜) : Set V :=
  gfpBelow (br g hg) (br (shift g H) (hg.shift H)).lfp

/-- Lemme clé : un amorçage positif laisse un état dont la meilleure réponse sans amorçage est
plus petite. -/
theorem br_lfp_shift_subset (hg : Supermodular g) {H : 𝕜} (hH : 0 ≤ H) :
    br g hg (br (shift g H) (hg.shift H)).lfp ⊆ (br (shift g H) (hg.shift H)).lfp := by
  intro i hi
  rw [← (br (shift g H) (hg.shift H)).map_lfp]
  have hi' : 0 ≤ g i ((br (shift g H) (hg.shift H)).lfp \ {i}) := hi
  show 0 ≤ g i ((br (shift g H) (hg.shift H)).lfp \ {i}) + H
  linarith

/-- ★ L'état après retrait est un équilibre du jeu sans amorçage. -/
theorem afterSeed_nash (hg : Supermodular g) {H : 𝕜} (hH : 0 ≤ H) :
    IsNash g (afterSeed g hg H) :=
  isNash_iff_fixed.mpr (gfpBelow_fixed _ (br_lfp_shift_subset hg hH))

theorem afterSeed_subset (hg : Supermodular g) (H : 𝕜) :
    afterSeed g hg H ⊆ (br (shift g H) (hg.shift H)).lfp :=
  gfpBelow_subset _

/-- ★ C'est le plus grand équilibre contenu dans l'état amorcé. -/
theorem afterSeed_greatest (hg : Supermodular g) {H : 𝕜} {X : Set V} (hX : IsNash g X)
    (hXL : X ⊆ (br (shift g H) (hg.shift H)).lfp) : X ⊆ afterSeed g hg H :=
  gfpBelow_greatest _ hXL (isNash_iff_fixed.mp hX).ge

theorem afterSeed_subset_gfp (hg : Supermodular g) {H : 𝕜} (hH : 0 ≤ H) :
    afterSeed g hg H ⊆ (br g hg).gfp :=
  (gfp_greatest_nash hg).2 (afterSeed_nash hg hH)

/-- L'amorçage ne nuit jamais : le plus petit équilibre reste en dessous. -/
theorem lfp_subset_afterSeed (hg : Supermodular g) {H : 𝕜} (hH : 0 ≤ H) :
    (br g hg).lfp ⊆ afterSeed g hg H :=
  afterSeed_greatest hg (lfp_least_nash hg).1
    (lfp_mono_gain _ _ fun _ _ => le_add_of_nonneg_right hH)

/-- ★ **La dynamique après retrait** : depuis l'état amorcé, `card V` pas de la dynamique sans
amorçage atteignent `afterSeed`. -/
theorem afterSeed_iterate [Finite V] (hg : Supermodular g) {H : 𝕜} (hH : 0 ≤ H) :
    (⇑(br g hg))^[Nat.card V] (br (shift g H) (hg.shift H)).lfp = afterSeed g hg H :=
  iterate_pre _ (br_lfp_shift_subset hg hH) (Set.ncard_le_card _)

/-- ★ **Amorcer puis retirer**, de bout en bout : `card V` pas amorcés depuis `∅`, puis `card V`
pas sans amorçage. -/
theorem seed_then_withdraw [Finite V] (hg : Supermodular g) {H : 𝕜} (hH : 0 ≤ H) :
    (⇑(br g hg))^[Nat.card V] ((⇑(br (shift g H) (hg.shift H)))^[Nat.card V] ∅) =
      afterSeed g hg H := by
  rw [iterate_lfp, afterSeed_iterate hg hH]

/-- ★ **Hystérésis comme ressource** : si l'amorçage allume tout, le retrait laisse le plus grand
équilibre. -/
theorem afterSeed_full (hg : Supermodular g) {H : 𝕜}
    (h : (br (shift g H) (hg.shift H)).lfp = Set.univ) : afterSeed g hg H = (br g hg).gfp := by
  unfold afterSeed
  rw [h, gfpBelow_univ]

/-! ### Le témoin bistable : coordination à deux joueurs -/

open Classical in
/-- Chacun gagne à adhérer ssi l'autre adhère. -/
noncomputable def coordGain : Fin 2 → Set (Fin 2) → ℚ := fun _ S => if S.Nonempty then 1 else -1

theorem coordGain_super : Supermodular coordGain := by
  intro _ S T h
  simp only [coordGain]
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h1.mono h) h2
  · norm_num
  · exact le_rfl

/-- ★ **Bistabilité** : `lfp = ∅`, `gfp = univ`, deux équilibres. -/
theorem bistable_witness :
    (br coordGain coordGain_super).lfp = ∅ ∧ (br coordGain coordGain_super).gfp = Set.univ ∧
      ¬ ∃! X, IsNash coordGain X := by
  have h1 : (br coordGain coordGain_super).lfp = ∅ :=
    (lfp_eq_empty_iff _).mpr fun _ => by simp [coordGain]
  have h2 : (br coordGain coordGain_super).gfp = Set.univ := by
    refine Set.eq_univ_of_univ_subset ((br coordGain coordGain_super).le_gfp fun i _ => ?_)
    have hne : (Set.univ \ {i} : Set (Fin 2)).Nonempty := by
      fin_cases i
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
    show 0 ≤ coordGain i (Set.univ \ {i})
    simp [coordGain, hne]
  refine ⟨h1, h2, fun h => ?_⟩
  have := (nash_unique_iff coordGain_super).mp h
  rw [h1, h2] at this
  exact Set.empty_ne_univ this

/-! ### §5. Les voies comme modifications de gain -/

/-- Ajout d'un terme de gain `D` (voie 2 : drain frontalier évité en adhérant). -/
def addGain (g D : V → Set V → 𝕜) : V → Set V → 𝕜 := fun i S => g i S + D i S

theorem Supermodular.add {D : V → Set V → 𝕜} (hg : Supermodular g) (hD : Supermodular D) :
    Supermodular (addGain g D) :=
  fun i _ _ h => add_le_add (hg i h) (hD i h)

/-- ★ **Voie 2** : un drain positif et monotone élargit les deux équilibres extrêmes. -/
theorem drain_enlarges {D : V → Set V → 𝕜} (hg : Supermodular g) (hD : Supermodular D)
    (h0 : ∀ i S, 0 ≤ D i S) :
    (br g hg).lfp ⊆ (br (addGain g D) (hg.add hD)).lfp ∧
      (br g hg).gfp ⊆ (br (addGain g D) (hg.add hD)).gfp :=
  have h : ∀ i S, g i S ≤ addGain g D i S := fun i S => le_add_of_nonneg_right (h0 i S)
  ⟨lfp_mono_gain _ _ h, gfp_mono_gain _ _ h⟩

open Classical in
/-- Voie 1 : obligation d'adhérer pour les joueurs de `J` (gain tronqué à `0`). -/
noncomputable def mandate (g : V → Set V → 𝕜) (J : Set V) : V → Set V → 𝕜 :=
  fun i S => if i ∈ J then max (g i S) 0 else g i S

omit [IsStrictOrderedRing 𝕜] in
theorem Supermodular.mandate (hg : Supermodular g) (J : Set V) :
    Supermodular (AdhesionGame.mandate g J) := by
  intro i _ _ h
  simp only [AdhesionGame.mandate]
  split_ifs
  · exact max_le_max (hg i h) le_rfl
  · exact hg i h

omit [IsStrictOrderedRing 𝕜] in
/-- ★ **Voie 1** : l'obligation élargit les deux équilibres extrêmes, et les obligés sont dans
le plus petit. -/
theorem mandate_enlarges (hg : Supermodular g) (J : Set V) :
    (br g hg).lfp ⊆ (br (mandate g J) (hg.mandate J)).lfp ∧
      (br g hg).gfp ⊆ (br (mandate g J) (hg.mandate J)).gfp ∧
        J ⊆ (br (mandate g J) (hg.mandate J)).lfp := by
  have h : ∀ i S, g i S ≤ mandate g J i S := fun i S => by
    simp only [mandate]
    split_ifs
    · exact le_max_left _ _
    · exact le_rfl
  refine ⟨lfp_mono_gain _ _ h, gfp_mono_gain _ _ h, fun i hi => ?_⟩
  rw [← OrderHom.map_lfp]
  show 0 ≤ mandate g J i (_ \ {i})
  simp only [mandate, if_pos hi]
  exact le_max_right _ _

end AdhesionGame

/-!
## Domaine (généralisation D-13, 2026-10-03)

Toutes les déclarations sont énoncées sur un corps ordonné quelconque `𝕜`, sauf le témoin bistable
(`coordGain`, `coordGain_super`, `bistable_witness`), qui reste dans `ℚ`.

- Classes : `[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`, comme `MeasureFibration` ; les
  énoncés précédés de `omit … in` en demandent moins. `ℚ` et `ℝ` en sont des instances ; les
  énoncés valent donc dans `ℝ` sans autre argument.
- Un témoin dans `ℚ` est un exemple à valeurs rationnelles, pas une restriction d'un résultat.
- Historique : la sonde ℚ→ℝ du 2026-10-03 (`cache/verification.md` §V179), consignée ici par
  D-12, avait montré que les preuves passaient dans `ℝ`. La généralisation la remplace
  (`cache/verification.md` §V181 ; décision D-13 de `ThèseNov26/00_cadre/decisions.md`).
-/
