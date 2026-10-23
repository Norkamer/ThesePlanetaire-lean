/-
Copyright (c) 2026 Lionel GRENET (Norkamer).
Released under the MIT license as described in the file LICENSE at the repository root.
SPDX-License-Identifier: MIT

  ThesePlanetaire/JointReserve.lean
  Réserve conjointe (2026-10-11, D-40) — papier 11 : les réserves du théorème 2 à plusieurs
  plafonds. Développé d'abord en `JointReserve_scratch.lean` (workflow du dépôt). Sonde qui le
  précède (calcul exhaustif dans ℕ, 0 écart) et trace : `cache/reserve_conjointe_2026-10-11/`.

  Module neuf (D-30) : aucun module existant n'est modifié. Il importe `GuardField` (papier 11).

  Portée. Un vecteur de charges `L : B → M`, un plafond `cap c` sur chaque coordonnée `c` d'un
  ensemble fini `G` ; des sources incontrôlables `u`, chacune au plus une fois par période, qui
  ajoutent `eu u c` à chaque coordonnée ; un top **coordonnée par coordonnée**,
  `L ↦ (tick c (L c))_c`. Un top qui couple les coordonnées (une régénération partagée) n'entre
  pas dans ce cadre : la sonde montre que la décomposition casse alors.
  - §1, générique (`+` et `≤` seulement, donc ℕ et tout corps ordonné) : la projection d'un
    ensemble tenable est tenable (`tenableJ_proj`), l'intersection des relevés aussi
    (`tenableJ_lift`) ; le plus grand ensemble tenable est l'intersection des plus grands
    ensembles tenables de chaque coordonnée (`regionJ_iff`) ; viabilité ssi viabilité sur
    chaque coordonnée (`viableJ_iff_forall`, `M` non vide).
  - §2, générique (préordre, addition croissante) : une source à plusieurs plans possibles
    (`TenableC`) équivaut au substitut `w` qui prend, sur chaque coordonnée, le pire plan
    (`regionC_iff`, `viableC_iff`), si le top est croissant sur chaque coordonnée plafonnée.
  - §3, corps ordonné : réserve vectorielle (`reserveJ_maximal`, sans signe ;
    `reserveJ_tenable_iff`, émissions ≥ 0) ; viabilité ssi `Σ_u eu u c ≤ ρ_c` sur chaque
    coordonnée plafonnée (`viableJ_iff`, corps archimédien, émissions ≥ 0).
  - §4, corps archimédien : émetteurs non couverts. Avec la nature et le substitut « maximum des
    deux plans sur chaque coordonnée » (`coverageJ_max_iff`), ou avec des émetteurs qui
    choisissent un profil mixte à chaque période (`coverageJ_iff`), un ensemble tenable non vide
    existe ssi `E_nat,c + M_{A,c} ≤ ρ_c` sur chaque coordonnée plafonnée ; couvrir plus ne nuit
    pas (`coverageJ_mono`).
  - §5 : le pire cas vectoriel n'est atteint par aucun profil (`jointWorst_not_attained`) :
    l'analogue vectoriel de « some mixed profile attains `M_A(μ)` » (théorème 2(c)(i)) est faux ;
    pont ℕ vers la viabilité de `ReserveCoverage` (`viableJ_nat_iff`).
  Nature : §1 et §3 sont les preuves du théorème 2 relues coordonnée par coordonnée, avec un
  `J` commun ; §2 est l'argument « fermé vers le bas » (top croissant, émissions comparées
  coordonnée par coordonnée). Rien ici sur la partie (a) (une source `m` fois), la proposition
  sur les fibres, le non-blocage ni les échéances.
  Les `example` de la fin sont des témoins de non-vacuité, dans ℚ.
-/
import ThesePlanetaire.GuardField

namespace JointReserve

open FeedbackClass (Memory)
open GuardField (ControlledInvariantSetF XresSetF TopOKF ViableF tickOpF rhoF
  reserveSetF_maximal reserveSetF_ci_iff topOKF_iff viableF_iff)

/-! ## §1. Décomposition plafond par plafond (générique : `+` et `≤`) -/

section Decomposition

variable {B U M : Type*} [DecidableEq U]

/-- Ensemble tenable à une coordonnée (la définition de `ControlledInvariantSetF` et de
`ReserveCoverage.ControlledInvariantSet`, pour un type `M` quelconque). -/
def TenableS [Add M] [LE M] (tick : M → M) (eu : U → M) (cap : M) (X : M × Finset U → Prop) :
    Prop :=
  (∀ L J, X (L, J) → L ≤ cap) ∧
    (∀ L J u, X (L, J) → u ∉ J → X (L + eu u, insert u J)) ∧
    ∀ L J, X (L, J) → X (tick L, ∅)

/-- Ensemble tenable vectoriel : chaque coordonnée plafonnée reste sous son plafond ; une source
`u ∉ J` ajoute `eu u c` à chaque coordonnée `c` ; le top agit coordonnée par coordonnée. -/
def TenableJ [Add M] [LE M] (G : Finset B) (tick : B → M → M) (eu : U → B → M) (cap : B → M)
    (X : (B → M) × Finset U → Prop) : Prop :=
  (∀ L J, X (L, J) → ∀ c ∈ G, L c ≤ cap c) ∧
    (∀ L J u, X (L, J) → u ∉ J → X (fun c => L c + eu u c, insert u J)) ∧
    ∀ L J, X (L, J) → X (fun c => tick c (L c), ∅)

/-- Le plus grand ensemble tenable, à une coordonnée : les états contenus dans un ensemble
tenable. -/
def RegionS [Add M] [LE M] (tick : M → M) (eu : U → M) (cap : M) (q : M × Finset U) : Prop :=
  ∃ X, TenableS tick eu cap X ∧ X q

/-- Le plus grand ensemble tenable vectoriel. -/
def RegionJ [Add M] [LE M] (G : Finset B) (tick : B → M → M) (eu : U → B → M) (cap : B → M)
    (q : (B → M) × Finset U) : Prop :=
  ∃ X, TenableJ G tick eu cap X ∧ X q

/-- Viabilité à une coordonnée : un ensemble tenable non vide existe. -/
def ViableS [Add M] [LE M] (tick : M → M) (eu : U → M) (cap : M) : Prop :=
  ∃ X, TenableS tick eu cap X ∧ ∃ q, X q

/-- Viabilité vectorielle. -/
def ViableJ [Add M] [LE M] (G : Finset B) (tick : B → M → M) (eu : U → B → M) (cap : B → M) :
    Prop :=
  ∃ X, TenableJ G tick eu cap X ∧ ∃ q, X q

variable [Add M] [LE M] {G : Finset B} {tick : B → M → M} {eu : U → B → M} {cap : B → M}

/-- ★ **Projection.** La projection d'un ensemble tenable vectoriel sur une coordonnée plafonnée
est tenable pour cette coordonnée seule. -/
theorem tenableJ_proj {X : (B → M) × Finset U → Prop} (hX : TenableJ G tick eu cap X) {c : B}
    (hc : c ∈ G) :
    TenableS (tick c) (fun u => eu u c) (cap c) (fun q => ∃ L, X (L, q.2) ∧ L c = q.1) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ J ⟨L, hL, rfl⟩
    exact hX.1 L J hL c hc
  · rintro _ J u ⟨L, hL, rfl⟩ hu
    exact ⟨_, hX.2.1 L J u hL hu, rfl⟩
  · rintro _ J ⟨L, hL, rfl⟩
    exact ⟨_, hX.2.2 L J hL, rfl⟩

/-- ★ **Relèvement.** L'intersection des relevés d'ensembles tenables, un par coordonnée
plafonnée, est tenable (l'ensemble `J` des sources tirées est commun). -/
theorem tenableJ_lift {Xc : B → M × Finset U → Prop}
    (hXc : ∀ c ∈ G, TenableS (tick c) (fun u => eu u c) (cap c) (Xc c)) :
    TenableJ G tick eu cap (fun q => ∀ c ∈ G, Xc c (q.1 c, q.2)) :=
  ⟨fun _ _ h c hc => (hXc c hc).1 _ _ (h c hc),
    fun _ _ u h hu c hc => (hXc c hc).2.1 _ _ u (h c hc) hu,
    fun _ _ h c hc => (hXc c hc).2.2 _ _ (h c hc)⟩

/-- Le plus grand ensemble tenable est tenable. -/
theorem regionS_tenable {t : M → M} {f : U → M} {k : M} : TenableS t f k (RegionS t f k) :=
  ⟨fun L J ⟨_, hX, h⟩ => hX.1 L J h,
    fun L J u ⟨X, hX, h⟩ hu => ⟨X, hX, hX.2.1 L J u h hu⟩,
    fun L J ⟨X, hX, h⟩ => ⟨X, hX, hX.2.2 L J h⟩⟩

/-- ★ **Décomposition.** Un état vectoriel est dans le plus grand ensemble tenable ssi, sur
chaque coordonnée plafonnée, sa projection est dans le plus grand ensemble tenable de cette
coordonnée. -/
theorem regionJ_iff {q : (B → M) × Finset U} :
    RegionJ G tick eu cap q ↔ ∀ c ∈ G, RegionS (tick c) (fun u => eu u c) (cap c) (q.1 c, q.2) := by
  constructor
  · rintro ⟨X, hX, hq⟩ c hc
    exact ⟨_, tenableJ_proj hX hc, q.1, hq, rfl⟩
  · intro h
    exact ⟨_, tenableJ_lift fun c _ => regionS_tenable, h⟩

/-- ★ **Viabilité plafond par plafond.** Un ensemble tenable vectoriel non vide existe ssi, sur
chaque coordonnée plafonnée, un ensemble tenable non vide existe. -/
theorem viableJ_iff_forall [Nonempty M] :
    ViableJ G tick eu cap ↔ ∀ c ∈ G, ViableS (tick c) (fun u => eu u c) (cap c) := by
  constructor
  · rintro ⟨X, hX, ⟨L, J⟩, hq⟩ c hc
    exact ⟨_, tenableJ_proj hX hc, (L c, J), L, hq, rfl⟩
  · intro h
    have h0 : ∀ c ∈ G, ∃ ℓ, RegionS (tick c) (fun u => eu u c) (cap c) (ℓ, ∅) := by
      intro c hc
      obtain ⟨X, hX, ⟨ℓ, J⟩, hq⟩ := h c hc
      exact ⟨tick c ℓ, X, hX, hX.2.2 ℓ J hq⟩
    classical
    let L : B → M := fun c =>
      if hc : c ∈ G then Classical.choose (h0 c hc) else Classical.arbitrary M
    refine ⟨_, tenableJ_lift fun c _ => regionS_tenable, (L, ∅), fun c hc => ?_⟩
    show RegionS _ _ _ (L c, ∅)
    simp only [L, dif_pos hc]
    exact Classical.choose_spec (h0 c hc)

end Decomposition

/-! ## §2. Sources à plusieurs plans : le pire cas se prend coordonnée par coordonnée -/

section Choice

variable {B U M : Type*} [DecidableEq U]

/-- Ensemble tenable quand une source `u ∉ J` peut émettre tout vecteur `v` tel que `P u v` (par
exemple l'un des plans d'un émetteur, ou un profil mixte). -/
def TenableC [Add M] [LE M] (G : Finset B) (tick : B → M → M) (P : U → (B → M) → Prop)
    (cap : B → M) (X : (B → M) × Finset U → Prop) : Prop :=
  (∀ L J, X (L, J) → ∀ c ∈ G, L c ≤ cap c) ∧
    (∀ L J u v, X (L, J) → u ∉ J → P u v → X (fun c => L c + v c, insert u J)) ∧
    ∀ L J, X (L, J) → X (fun c => tick c (L c), ∅)

def RegionC [Add M] [LE M] (G : Finset B) (tick : B → M → M) (P : U → (B → M) → Prop)
    (cap : B → M) (q : (B → M) × Finset U) : Prop :=
  ∃ X, TenableC G tick P cap X ∧ X q

def ViableC [Add M] [LE M] (G : Finset B) (tick : B → M → M) (P : U → (B → M) → Prop)
    (cap : B → M) : Prop :=
  ∃ X, TenableC G tick P cap X ∧ ∃ q, X q

variable [Add M] [Preorder M] [AddLeftMono M] [AddRightMono M] {G : Finset B} {tick : B → M → M}
  {P : U → (B → M) → Prop} {w : U → B → M} {cap : B → M}

/-- Fermeture vers le bas, coordonnée par coordonnée, avec un témoin par coordonnée. -/
def downJ (G : Finset B) (X : (B → M) × Finset U → Prop) : (B → M) × Finset U → Prop :=
  fun q => ∀ c ∈ G, ∃ L', X (L', q.2) ∧ q.1 c ≤ L' c

omit [DecidableEq U] [Add M] [AddLeftMono M] [AddRightMono M] in
theorem downJ_self {X : (B → M) × Finset U → Prop} {q : (B → M) × Finset U} (h : X q) :
    downJ G X q :=
  fun _ _ => ⟨q.1, h, le_rfl⟩

/-- Plusieurs plans → substitut : `downJ` d'un ensemble tenable à plans est tenable pour le
substitut `w`, si chaque coordonnée de `w` est atteinte ou dépassée par un plan. -/
theorem tenableJ_downJ_of_C (hmono : ∀ c ∈ G, Monotone (tick c))
    (hw : ∀ u, ∀ c ∈ G, ∃ v, P u v ∧ w u c ≤ v c) {X : (B → M) × Finset U → Prop}
    (hX : TenableC G tick P cap X) : TenableJ G tick w cap (downJ G X) := by
  refine ⟨fun L J h c hc => ?_, fun L J u h hu c hc => ?_, fun L J h c hc => ?_⟩
  · obtain ⟨L', hL', hle⟩ := h c hc
    exact le_trans hle (hX.1 L' J hL' c hc)
  · obtain ⟨L', hL', hle⟩ := h c hc
    obtain ⟨v, hv, hwv⟩ := hw u c hc
    exact ⟨_, hX.2.1 L' J u v hL' hu hv, add_le_add hle hwv⟩
  · obtain ⟨L', hL', hle⟩ := h c hc
    exact ⟨_, hX.2.2 L' J hL', hmono c hc hle⟩

/-- Substitut → plusieurs plans : `downJ` d'un ensemble tenable pour le substitut `w` est tenable
pour les plans, si chaque plan est sous `w` sur chaque coordonnée plafonnée. -/
theorem tenableC_downJ_of_J (hmono : ∀ c ∈ G, Monotone (tick c))
    (hP : ∀ u v, P u v → ∀ c ∈ G, v c ≤ w u c) {X : (B → M) × Finset U → Prop}
    (hX : TenableJ G tick w cap X) : TenableC G tick P cap (downJ G X) := by
  refine ⟨fun L J h c hc => ?_, fun L J u v h hu hv c hc => ?_, fun L J h c hc => ?_⟩
  · obtain ⟨L', hL', hle⟩ := h c hc
    exact le_trans hle (hX.1 L' J hL' c hc)
  · obtain ⟨L', hL', hle⟩ := h c hc
    exact ⟨_, hX.2.1 L' J u hL' hu, add_le_add hle (hP u v hv c hc)⟩
  · obtain ⟨L', hL', hle⟩ := h c hc
    exact ⟨_, hX.2.2 L' J hL', hmono c hc hle⟩

/-- ★ **Le pire cas se prend coordonnée par coordonnée.** Si, sur chaque coordonnée plafonnée,
le top est croissant, chaque plan d'une source est sous `w u` et un plan atteint `w u`, le plus
grand ensemble tenable à plans est celui du substitut `w`. -/
theorem regionC_iff (hmono : ∀ c ∈ G, Monotone (tick c))
    (hP : ∀ u v, P u v → ∀ c ∈ G, v c ≤ w u c) (hw : ∀ u, ∀ c ∈ G, ∃ v, P u v ∧ w u c ≤ v c)
    {q : (B → M) × Finset U} : RegionC G tick P cap q ↔ RegionJ G tick w cap q :=
  ⟨fun ⟨_, hX, hq⟩ => ⟨_, tenableJ_downJ_of_C hmono hw hX, downJ_self hq⟩,
    fun ⟨_, hX, hq⟩ => ⟨_, tenableC_downJ_of_J hmono hP hX, downJ_self hq⟩⟩

theorem viableC_iff (hmono : ∀ c ∈ G, Monotone (tick c))
    (hP : ∀ u v, P u v → ∀ c ∈ G, v c ≤ w u c) (hw : ∀ u, ∀ c ∈ G, ∃ v, P u v ∧ w u c ≤ v c) :
    ViableC G tick P cap ↔ ViableJ G tick w cap :=
  ⟨fun ⟨_, hX, q, hq⟩ => ⟨_, tenableJ_downJ_of_C hmono hw hX, q, downJ_self hq⟩,
    fun ⟨_, hX, q, hq⟩ => ⟨_, tenableC_downJ_of_J hmono hP hX, q, downJ_self hq⟩⟩

end Choice

/-! ## §3. Réserve et masse par coordonnée, sur un corps ordonné -/

section Field

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {B U : Type*} [DecidableEq B] [Fintype U] [DecidableEq U]

/-- La réserve vectorielle : sur chaque coordonnée plafonnée, la réserve de cette coordonnée. -/
def XresJ (G : Finset B) (eu : U → B → 𝕜) (cap : B → 𝕜) : (B → 𝕜) × Finset U → Prop :=
  fun q => ∀ c ∈ G, XresSetF (fun u => eu u c) (cap c) (q.1 c, q.2)

variable {G : Finset B} {tick : B → 𝕜 → 𝕜} {eu : U → B → 𝕜} {cap : B → 𝕜}

omit [IsStrictOrderedRing 𝕜] [DecidableEq B] in
/-- ★ Tout ensemble tenable vectoriel est contenu dans la réserve vectorielle (sans hypothèse de
signe). -/
theorem reserveJ_maximal {X : (B → 𝕜) × Finset U → Prop} (hX : TenableJ G tick eu cap X) :
    ∀ q, X q → XresJ G eu cap q := by
  rintro ⟨L, J⟩ hq c hc
  have hp : ControlledInvariantSetF (tick c) (fun u => eu u c) (cap c)
      (fun q => ∃ L', X (L', q.2) ∧ L' c = q.1) := tenableJ_proj hX hc
  exact reserveSetF_maximal hp (L c, J) ⟨L, hq, rfl⟩

/-- ★ Émissions ≥ 0 : la réserve vectorielle est tenable ssi, sur chaque coordonnée plafonnée,
le top restaure la réserve de cette coordonnée, `tick_c L + Σ_u eu u c ≤ cap c` pour
`L ≤ cap c`. -/
theorem reserveJ_tenable_iff (heu : ∀ u, ∀ c ∈ G, 0 ≤ eu u c) :
    TenableJ G tick eu cap (XresJ G eu cap) ↔
      ∀ c ∈ G, TopOKF (tick c) (∑ u, eu u c) 1 (cap c) := by
  constructor
  · intro hX c hc L hL
    have h1 : XresJ G eu cap (Function.update cap c L, Finset.univ) := by
      intro c' hc'
      show Function.update cap c L c' + ∑ u ∈ Finset.univᶜ, eu u c' ≤ cap c'
      rw [Finset.compl_univ, Finset.sum_empty, add_zero]
      rcases eq_or_ne c' c with rfl | hne
      · rw [Function.update_self]; exact hL
      · rw [Function.update_of_ne hne]
    have h2 := hX.2.2 _ _ h1 c hc
    change tick c (Function.update cap c L c) + ∑ u ∈ (∅ : Finset U)ᶜ, eu u c ≤ cap c at h2
    rw [Function.update_self, Finset.compl_empty] at h2
    simpa using h2
  · intro h
    exact tenableJ_lift fun c hc => (reserveSetF_ci_iff (fun u => heu u c hc)).mpr (h c hc)

omit [DecidableEq B] in
/-- ★ **Viabilité par plafond** (corps archimédien, émissions ≥ 0, top `tickOpF` sur chaque
coordonnée avec sa mémoire et son taux) : un ensemble tenable vectoriel non vide existe ssi,
sur chaque coordonnée plafonnée, la masse incontrôlable d'une période est sous le débit,
`Σ_u eu u c ≤ ρ_c`. -/
theorem viableJ_iff [Archimedean 𝕜] (mem : B → Memory) (r : B → 𝕜)
    (heu : ∀ u, ∀ c ∈ G, 0 ≤ eu u c) :
    ViableJ G (fun c => tickOpF (mem c) (r c)) eu cap ↔
      ∀ c ∈ G, ∑ u, eu u c ≤ rhoF (mem c) (r c) (cap c) := by
  rw [viableJ_iff_forall]
  exact forall₂_congr fun c hc => viableF_iff (mem c) (r c) (fun u => heu u c hc)

end Field

/-! ## §4. Émetteurs non couverts : le pire cas par coordonnée, non atteint conjointement -/

section Coverage

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {B ι Un : Type*} [Fintype ι] [DecidableEq ι] [Fintype Un] [DecidableEq Un]

/-- Émission (vectorielle) de l'émetteur `i` sous le profil mixte `t` : `(1 + t)/2` fois son
plan `+`, `(1 − t)/2` fois son plan `−`, sur chaque coordonnée. -/
def mixedEmit (aP aM : ι → B → 𝕜) (i : ι) (t : 𝕜) : B → 𝕜 :=
  fun c => (1 + t) / 2 * aP i c + (1 - t) / 2 * aM i c

/-- Ce que chaque source peut émettre en une occurrence : une source naturelle `n` émet
`enat n` ; un émetteur couvert (`i ∈ A`) n'émet rien que la règle ne puisse refuser ; un
émetteur non couvert émet le vecteur de n'importe quel profil mixte `t ∈ [−1, 1]`, choisi à
chaque période. -/
def choiceSrc (enat : Un → B → 𝕜) (aP aM : ι → B → 𝕜) (A : Finset ι) :
    Un ⊕ ι → (B → 𝕜) → Prop
  | .inl n, v => v = enat n
  | .inr i, v => if i ∈ A then v = 0 else ∃ t, -1 ≤ t ∧ t ≤ 1 ∧ v = mixedEmit aP aM i t

/-- Le substitut : chaque émetteur non couvert émet, sur chaque coordonnée, le maximum de ses deux
plans. Ce vecteur n'est en général l'émission d'aucun profil (`jointWorst_not_attained`). -/
def srcEmitJ (enat : Un → B → 𝕜) (aP aM : ι → B → 𝕜) (A : Finset ι) : Un ⊕ ι → B → 𝕜
  | .inl n => enat n
  | .inr i => if i ∈ A then 0 else fun c => max (aP i c) (aM i c)

/-- Masse incontrôlable des émetteurs non couverts sur la coordonnée `c`. -/
def uncMassJ (aP aM : ι → B → 𝕜) (A : Finset ι) (c : B) : 𝕜 :=
  ∑ i ∈ Aᶜ, max (aP i c) (aM i c)

omit [Fintype ι] [DecidableEq ι] in
theorem mixedEmit_le_max (aP aM : ι → B → 𝕜) (i : ι) {t : 𝕜} (h1 : -1 ≤ t) (h2 : t ≤ 1)
    (c : B) : mixedEmit aP aM i t c ≤ max (aP i c) (aM i c) := by
  have hP : aP i c ≤ max (aP i c) (aM i c) := le_max_left _ _
  have hM : aM i c ≤ max (aP i c) (aM i c) := le_max_right _ _
  have := mul_le_mul_of_nonneg_left hP (show (0 : 𝕜) ≤ (1 + t) / 2 by linarith)
  have := mul_le_mul_of_nonneg_left hM (show (0 : 𝕜) ≤ (1 - t) / 2 by linarith)
  show (1 + t) / 2 * aP i c + (1 - t) / 2 * aM i c ≤ _
  nlinarith

omit [Fintype ι] [Fintype Un] [DecidableEq Un] in
theorem choiceSrc_le (enat : Un → B → 𝕜) (aP aM : ι → B → 𝕜) (A : Finset ι) :
    ∀ u v, choiceSrc enat aP aM A u v → ∀ c, v c ≤ srcEmitJ enat aP aM A u c := by
  rintro (n | i) v h c
  · simp only [choiceSrc] at h
    simp [srcEmitJ, h]
  · simp only [choiceSrc] at h
    simp only [srcEmitJ]
    split_ifs at h ⊢ with hi
    · simp [h]
    · obtain ⟨t, h1, h2, rfl⟩ := h
      exact mixedEmit_le_max aP aM i h1 h2 c

omit [Fintype ι] [Fintype Un] [DecidableEq Un] in
theorem choiceSrc_attains (enat : Un → B → 𝕜) (aP aM : ι → B → 𝕜) (A : Finset ι) :
    ∀ u c, ∃ v, choiceSrc enat aP aM A u v ∧ srcEmitJ enat aP aM A u c ≤ v c := by
  rintro (n | i) c
  · exact ⟨enat n, rfl, le_rfl⟩
  · by_cases hi : i ∈ A
    · refine ⟨0, ?_, ?_⟩
      · simp [choiceSrc, hi]
      · simp [srcEmitJ, hi]
    · by_cases hc : aM i c ≤ aP i c
      · refine ⟨mixedEmit aP aM i 1, ?_, ?_⟩
        · simp only [choiceSrc, if_neg hi]
          exact ⟨1, by norm_num, le_rfl, rfl⟩
        · simp only [srcEmitJ, if_neg hi, mixedEmit, max_eq_left hc]
          norm_num
      · refine ⟨mixedEmit aP aM i (-1), ?_, ?_⟩
        · simp only [choiceSrc, if_neg hi]
          exact ⟨-1, le_rfl, by norm_num, rfl⟩
        · simp only [srcEmitJ, if_neg hi, mixedEmit, max_eq_right (le_of_not_ge hc)]
          norm_num

theorem tickOpF_mono (mem : Memory) (r : 𝕜) : Monotone (tickOpF mem r) := by
  intro a b h
  cases mem
  · exact h
  · exact max_le_max (sub_le_sub_right h r) le_rfl
  · exact le_rfl

omit [DecidableEq Un] [IsStrictOrderedRing 𝕜] in
theorem sum_srcEmitJ (enat : Un → B → 𝕜) (aP aM : ι → B → 𝕜) (A : Finset ι) (c : B) :
    ∑ u, srcEmitJ enat aP aM A u c = ∑ n, enat n c + uncMassJ aP aM A c := by
  rw [Fintype.sum_sum_type]
  congr 1
  rw [uncMassJ, ← Finset.sum_compl_add_sum A]
  have h1 : ∑ i ∈ A, srcEmitJ enat aP aM A (.inr i) c = 0 :=
    Finset.sum_eq_zero fun i hi => by simp [srcEmitJ, hi]
  have h2 : ∑ i ∈ Aᶜ, srcEmitJ enat aP aM A (.inr i) c = ∑ i ∈ Aᶜ, max (aP i c) (aM i c) :=
    Finset.sum_congr rfl fun i hi => by simp [srcEmitJ, Finset.mem_compl.mp hi]
  rw [h1, h2, add_zero]

omit [Fintype ι] [Fintype Un] [DecidableEq Un] [IsStrictOrderedRing 𝕜] in
theorem srcEmitJ_nonneg {G : Finset B} {enat : Un → B → 𝕜} {aP aM : ι → B → 𝕜} {A : Finset ι}
    (henat : ∀ n, ∀ c ∈ G, 0 ≤ enat n c) (ha : ∀ i, ∀ c ∈ G, 0 ≤ aP i c ∧ 0 ≤ aM i c) :
    ∀ u, ∀ c ∈ G, 0 ≤ srcEmitJ enat aP aM A u c := by
  rintro (n | i) c hc
  · exact henat n c hc
  · simp only [srcEmitJ]
    split_ifs
    · exact le_rfl
    · exact le_trans (ha i c hc).1 (le_max_left _ _)

variable [Archimedean 𝕜] (mem : B → Memory) (r cap : B → 𝕜) {G : Finset B}
  {enat : Un → B → 𝕜} {aP aM : ι → B → 𝕜} {A : Finset ι}

/-- ★ **Couverture par plafond, substitut** (corps archimédien, émissions ≥ 0 sur les
coordonnées plafonnées) : avec, pour sources, la nature et chaque émetteur non couvert émettant
sur chaque coordonnée le maximum de ses deux plans, un ensemble tenable non vide existe ssi
`E_nat,c + M_{A,c} ≤ ρ_c` pour chaque coordonnée plafonnée `c`. -/
theorem coverageJ_max_iff (henat : ∀ n, ∀ c ∈ G, 0 ≤ enat n c)
    (ha : ∀ i, ∀ c ∈ G, 0 ≤ aP i c ∧ 0 ≤ aM i c) :
    ViableJ G (fun c => tickOpF (mem c) (r c)) (srcEmitJ enat aP aM A) cap ↔
      ∀ c ∈ G, ∑ n, enat n c + uncMassJ aP aM A c ≤ rhoF (mem c) (r c) (cap c) := by
  rw [viableJ_iff mem r (srcEmitJ_nonneg henat ha)]
  exact forall₂_congr fun c _ => by rw [sum_srcEmitJ]

/-- ★ **Couverture par plafond, choix des émetteurs** : la même condition vaut quand chaque
émetteur non couvert choisit à chaque période un profil mixte, et donc un vecteur d'émissions
réellement émis, au lieu du substitut. -/
theorem coverageJ_iff (henat : ∀ n, ∀ c ∈ G, 0 ≤ enat n c)
    (ha : ∀ i, ∀ c ∈ G, 0 ≤ aP i c ∧ 0 ≤ aM i c) :
    ViableC G (fun c => tickOpF (mem c) (r c)) (choiceSrc enat aP aM A) cap ↔
      ∀ c ∈ G, ∑ n, enat n c + uncMassJ aP aM A c ≤ rhoF (mem c) (r c) (cap c) := by
  rw [viableC_iff (w := srcEmitJ enat aP aM A) (fun c _ => tickOpF_mono (mem c) (r c))
    (fun u v h c _ => choiceSrc_le enat aP aM A u v h c)
    (fun u c _ => choiceSrc_attains enat aP aM A u c)]
  exact coverageJ_max_iff mem r cap henat ha

/-- ★ **Couvrir plus ne nuit pas** : si la règle couvre `A ⊆ A'` et qu'un ensemble tenable non
vide existe en couvrant `A`, il en existe un en couvrant `A'`. -/
theorem coverageJ_mono (henat : ∀ n, ∀ c ∈ G, 0 ≤ enat n c)
    (ha : ∀ i, ∀ c ∈ G, 0 ≤ aP i c ∧ 0 ≤ aM i c) {A' : Finset ι} (hA : A ⊆ A')
    (h : ViableC G (fun c => tickOpF (mem c) (r c)) (choiceSrc enat aP aM A) cap) :
    ViableC G (fun c => tickOpF (mem c) (r c)) (choiceSrc enat aP aM A') cap := by
  rw [coverageJ_iff mem r cap henat ha] at h ⊢
  intro c hc
  have hs : uncMassJ aP aM A' c ≤ uncMassJ aP aM A c :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.compl_subset_compl.mpr hA)
      fun i _ _ => le_trans (ha i c hc).1 (le_max_left _ _)
  exact le_trans (add_le_add le_rfl hs) (h c hc)

end Coverage

/-! ## §5. Témoin et pont ℕ -/

/-- ★ **Le pire cas vectoriel n'est pas atteint.** Un émetteur, deux coordonnées : le plan `+`
émet `(1, 0)`, le plan `−` émet `(0, 1)`. Le substitut vaut `(1, 1)`, et aucun profil, mixte ou
pur, n'émet ce vecteur : l'analogue vectoriel de « some mixed profile attains `M_A(μ)` » est
faux. -/
theorem jointWorst_not_attained {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (t : 𝕜) :
    mixedEmit (fun (_ : Fin 1) => ![(1 : 𝕜), 0]) (fun _ => ![0, 1]) 0 t ≠
      fun c => max (![(1 : 𝕜), 0] c) (![0, 1] c) := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [mixedEmit] at h0 h1
  linarith

/-- ★ **Pont ℕ.** Dans ℕ, la viabilité vectorielle est la conjonction, sur les coordonnées
plafonnées, de la viabilité de `ReserveCoverage` (celle dont dépend la sûreté du papier 15). -/
theorem viableJ_nat_iff {B U : Type*} [Fintype U] [DecidableEq U] {G : Finset B}
    {tick : B → ℕ → ℕ} {eu : U → B → ℕ} {cap : B → ℕ} :
    ViableJ G tick eu cap ↔ ∀ c ∈ G, ReserveCoverage.Viable (tick c) (fun u => eu u c) (cap c) :=
  viableJ_iff_forall

/-! ### Témoins de non-vacuité (ℚ, deux coordonnées plafonnées) -/

section Witnesses

/-- Un seul plafond qui ne tient pas suffit : flux sur les deux coordonnées, plafonds `(2, 1)`,
une source qui émet `(2, 2)` ; la coordonnée 0 tiendrait, la coordonnée 1 non. -/
example : ¬ ViableJ (Finset.univ : Finset (Fin 2)) (fun _ => tickOpF .flow (0 : ℚ))
    (fun (_ : Unit) => ![2, 2]) ![2, 1] := by
  rw [viableJ_iff (fun _ => .flow) (fun _ => 0) (fun _ c _ => by fin_cases c <;> norm_num)]
  intro h
  have := h 1 (Finset.mem_univ _)
  norm_num [rhoF] at this

/-- Dans l'instance de `jointWorst_not_attained` (plafonds `(1, 1)`, flux, pas de source
naturelle, émetteur non couvert), un ensemble tenable non vide existe : le substitut `(1, 1)`
n'est émis par aucun profil, mais la condition par plafond décide. -/
example : ViableC (Finset.univ : Finset (Fin 2)) (fun _ => tickOpF .flow (0 : ℚ))
    (choiceSrc (Un := Empty) (fun n => n.elim) (fun (_ : Fin 1) => ![1, 0]) (fun _ => ![0, 1]) ∅)
    ![1, 1] := by
  rw [coverageJ_iff (fun _ => .flow) (fun _ => 0) ![1, 1] (fun n => n.elim)
    (fun _ c _ => by fin_cases c <;> norm_num)]
  intro c _
  fin_cases c <;> simp [uncMassJ, rhoF]

/-- … et il n'en existe plus si le plafond de la coordonnée 1 tombe à 0. -/
example : ¬ ViableC (Finset.univ : Finset (Fin 2)) (fun _ => tickOpF .flow (0 : ℚ))
    (choiceSrc (Un := Empty) (fun n => n.elim) (fun (_ : Fin 1) => ![1, 0]) (fun _ => ![0, 1]) ∅)
    ![1, 0] := by
  rw [coverageJ_iff (fun _ => .flow) (fun _ => 0) ![1, 0] (fun n => n.elim)
    (fun _ c _ => by fin_cases c <;> norm_num)]
  intro h
  have := h 1 (Finset.mem_univ _)
  norm_num [uncMassJ, rhoF] at this

end Witnesses

end JointReserve
