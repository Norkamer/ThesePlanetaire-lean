/-
  Karp's Algorithm for Maximum Cycle Mean in Max-Plus Algebra

  This module implements Karp's 1978 algorithm (O(|V|·|E|)) for computing the
  maximum cycle mean in a weighted directed graph, adapted to the max-plus
  semiring (Z_max). This replaces the spectral placeholder axioms in
  ExtensionInfinie.lean with a constructive, elementary proof.

  References:
  - Karp, R. M. (1978). "A characterization of the minimum cycle mean in a digraph". Discrete Mathematics 23(3): 309–311.
  - Baccelli, F., Cohen, G., Olsder, G. J., & Quadrat, J.-P. (1992). Synchronization and Linearity. Wiley.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Zip
import Mathlib.Data.Fin.SuccPred
import Mathlib.Tactic
import Mathlib.Order.WithBot
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Finite.List
import ThesePlanetaire.Z_max

open Z_max
open Finset

namespace KarpAlgorithm

/-- Edge set of a directed graph -/
structure EdgeSet (V : Type*) where
  edges : Finset (V × V)
  weight : V × V → Z_max

/-- Karp's value function: d_k(v) = max weight of a path of length k from s to v.
    In max-plus: d_0(s) = 1 (the ⊗-unit, = `ofInt 0`), d_0(v≠s) = ⊥ (negInf),
    d_{k+1}(v) = ⊕_u (d_k(u) ⊗ w(u,v)) = max_u (d_k(u) * w(u,v)).
    NB: `*` = ⊗ = integer addition on `Z_max`; using `+` (= ⊕ = `max`) would compute
    `max_u max(d_k(u), w(u,v))` instead of the max-plus path weight (§13.13.A).
    NB bis: the base case must be `(1 : Z_max)` (= `ofInt 0`), NOT `(0 : Z_max)`
    (which is `negInf` = ⊥, since `Zero Z_max = negInf` — see `zero_eq`); writing
    `(0 : Z_max)` makes `d_0(s) = ⊥` and collapses every `d_k` to `⊥` (§13.13.C). -/
def karp_d {V : Type*} [Fintype V] [DecidableEq V] (E : EdgeSet V) (s : V) (k : ℕ) : V → Z_max :=
  fun v =>
    if k = 0 then
      if v = s then (1 : Z_max) else Z_max.negInf
    else
      (Finset.univ : Finset V).sup (fun u =>
        (karp_d E s (k - 1)) u * E.weight (u, v))

/-! ## Caractérisation de `karp_d` comme poids maximal de chemin

    Helper T2 : `karp_d E s k v` = ⊕-sup des poids (⊗) des chemins de longueur `k`
    de `s` à `v`. C'est le pont sémantique sur lequel la preuve Karp (Semaines 2-3 :
    Direction A = raccourcissement par pigeonhole, Direction B = lasso-pumping) s'appuie
    pour raisonner sur `d_k(v)` comme « poids max d'un chemin de longueur k de s à v ». -/

/-- Poids max-plus d'un chemin de longueur `k` porté par `f : Fin (k+1) → V` :
    ⊗-produit des `k` arêtes consécutives `(f i, f (i+1))`. Le produit vide (k=0) vaut
    `1` (élément ⊗-unit de `Z_max` = `ofInt 0`), conforme à un chemin de longueur 0.
    `i.castSucc : Fin (k+1)` = valeur `i` (source), `i.succ : Fin (k+1)` = valeur `i+1`
    (cible) ; pour k=0, `Fin 0` est vide → produit vide = `1`. -/
def walkWeight {V : Type*} [Fintype V] [DecidableEq V] (E : EdgeSet V) (k : ℕ)
    (f : Fin (k+1) → V) : Z_max :=
  (Finset.univ : Finset (Fin k)).prod fun i => E.weight (f i.castSucc, f i.succ)

/-! ### Preuve de `karp_d_path_weight` (helper T2) — sous-lemmes

    `karp_d E s k v = ⊕-sup des poids ⊗ des chemins de longueur k de s à v`. Preuve par
    induction sur k : base (k=0, témoins directs — la réindexation `Fin 1 → V ≃ V` n'est
    pas utilisée) + pas (bijection `Fin(k+2)→V ≃ (Fin(k+1)→V)×V`, découpage
    `walkWeight_succ`, distribution `sup_mul_right`/`sup_sup_comm`, collapse de ⊕-sup
    inliné `by_cases + if_pos/if_neg + Finset.le_sup`). -/

/-- Découpe du ⊗-produit `walkWeight` quand on étend un chemin `g : Fin (k+1) → V` par une
    dernière arête vers `u` (via `Fin.snoc`) : les `k` premières arêtes forment
    `walkWeight E k g`, la dernière est `E.weight (g (Fin.last k), u)`. -/
lemma walkWeight_snoc {V : Type*} [Fintype V] [DecidableEq V] (E : EdgeSet V) (k : ℕ)
    (g : Fin (k+1) → V) (u : V) :
    walkWeight E (k+1) (Fin.snoc g u) =
      walkWeight E k g * E.weight (g (Fin.last k), u) := by
  -- On simplifie `Fin.snoc g u` directement sur le but principal (où il est déjà élaboré
  -- depuis l'énoncé comme `Fin (k+2) → V`) ; un `have` typé séparé ré-élabore la famille
  -- dépendante `α` de `Fin.snoc` depuis zéro et laisse `p x` en métavariables.
  simp only [walkWeight]
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]

/-- Découpe générale de `walkWeight E (k+1) f` : les `k` premières arêtes (préfixe
    `f ∘ Fin.castSucc : Fin (k+1) → V`) forment `walkWeight E k (f ∘ Fin.castSucc)`, la
    dernière arête ferme en `f (Fin.last (k+1))`. Miroir de `walkWeight_snoc` pour un `f`
    quelconque (utilisé pour le sens `RHS ≤ M` du pas d'induction). -/
lemma walkWeight_succ {V : Type*} [Fintype V] [DecidableEq V] (E : EdgeSet V) (k : ℕ)
    (f : Fin (k+2) → V) :
    walkWeight E (k+1) f =
      walkWeight E k (f ∘ Fin.castSucc) * E.weight (f (Fin.last k).castSucc, f (Fin.last (k+1))) :=
  by
  simp only [walkWeight]
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.succ_castSucc, Fin.succ_last, Function.comp_apply, Nat.succ_eq_add_one]

/-- Découpe « split first » de `walkWeight E (k+1) f` : la 1ʳᵉ arête `(f 0, f 1)` se
    détache, le reste est `walkWeight E k (fun i => f i.succ)` (préfixe décalé d'un cran
    via `Fin.succ`). Miroir de `walkWeight_succ` (qui détache la **dernière** arête via
    `Fin.last`), adapté à la décomposition par `List.ofFn_succ` (qui expose le **premier**
    sommet) utilisée dans le pont `walkWeight_eq_walkWeightL`. -/
lemma walkWeight_cons {V : Type*} [Fintype V] [DecidableEq V] (E : EdgeSet V) (k : ℕ)
    (f : Fin (k+2) → V) :
    walkWeight E (k+1) f =
      E.weight (f 0, f (Fin.succ (0 : Fin (k+1)))) * walkWeight E k (fun i => f i.succ) := by
  simp only [walkWeight]
  rw [Fin.prod_univ_succ]
  simp only [walkWeight, Fin.succ_castSucc, Fin.castSucc_zero]


/-- `f a ≤ ⨆ f` sur `univ` (universalité du sup : le sup majore chacun de ses éléments).
    Wrapper de `Finset.le_sup` qui évite la dance `@Finset.le_sup _ _ _ _` (les
    métavariables `s f b` implicites ne s'infèrent pas) — forme unifiée avec l'idiome
    tardif `Finset.le_sup (f := f)` (F4). -/
lemma le_sup_univ {α : Type*} [Fintype α] [DecidableEq α] {β : Type*}
    [SemilatticeSup β] [OrderBot β] (f : α → β) (a : α) :
    f a ≤ (Finset.univ : Finset α).sup f :=
  Finset.le_sup (f := f) (Finset.mem_univ a)

/-- `karp_d E s k v` = ⊕-sup des poids ⊗ des chemins de longueur `k` de `s` à `v`.
    Un chemin est une fonction `f : Fin (k+1) → V` ; il compte ssi `f 0 = s` (départ)
    et `f (Fin.last k) = v` (arrivée), auquel cas son poids est `walkWeight E k f` ;
    sinon il contribue `⊥` (identité de ⊕ = `max`). C'est exactement le calcul de
    `karp_d` (récursion `d_{k+1}(v) = ⊕_u (d_k(u) ⊗ w(u,v))`, base `d_0(s)=1`).

    **Schéma de preuve** (helper T2 — fallback plan : énoncé précis admis, preuve
    combinatoire différée à un focus dédié pour rester sous le seuil D3) :
      • Base `k = 0` : `Fin 1 → V`, condition `f 0 = s ∧ f 0 = v`, produit vide = `1`.
        Si `v = s` : ∃ f (= const `s`) contribuant `1`, et tout autre contribue `⊥` →
        `sup = 1`. Si `v ≠ s` : aucune f ne satisfait → `sup = ⊥`. Égale
        `if v = s then 1 else ⊥` = `karp_d E s 0 v`.
      • Pas `k+1` : par IH `karp_d E s k u = sup_g [if g 0=s ∧ g(last k)=u then W_k g]`.
        Donc `karp_d E s (k+1) v = sup_u (sup_g …) * E.weight(u,v)` ; on distribue `*`
        sur le ⊕-sup (`Z_max.sup_mul_right`) puis échange les sups (`sup_sup_comm`) :
        `= sup_{g,u} if (g 0=s ∧ g(last k)=u) then W_k g * E.weight(u,v)`.
        Via la bijection `Fin (k+2) → V ≃ (Fin (k+1) → V) × V` (`g = f ∘ castSucc`,
        `u = f (last (k+1))`), `W_{k+1} f = W_k g * E.weight(g(last k), u)` (le produit
        sur `Fin (k+1)` se coupe en `i<k` (arêtes internes = `W_k g`) et `i=last k`
        (arête fermante `g(last k) → u`)), et les conditions coïncident après collapse
        du sup sur `u` en son point discriminant (`sup_u (if u=x then a) = a`).
    Consommateur : preuve `maxCycleMeanKarp_correct` (Semaines 2-3, Direction A/B). -/
theorem karp_d_path_weight {V : Type*} [Fintype V] [DecidableEq V] (E : EdgeSet V)
    (s : V) (k : ℕ) (v : V) :
    karp_d E s k v =
      (Finset.univ : Finset (Fin (k+1) → V)).sup fun f =>
        if f 0 = s ∧ f (Fin.last k) = v then walkWeight E k f else (0 : Z_max) := by
  induction k generalizing v with
  | zero =>
    -- Base k = 0 : LHS = if v = s then 1 else 0 ; RHS = sup_f if (f 0 = s ∧ f 0 = v) then 1 else 0
    -- (walkWeight E 0 f = 1, Fin.last 0 = 0 via Subsingleton (Fin 1)). Preuve par le_antisymm
    -- avec témoins (évite la réindexation Fin 1 → V ≃ V dont le `@[simps]` ne se déclenche
    -- pas sur la coe `⇑` d'une réindexation par équivalence).
    have hkarp : karp_d E s 0 v = (if v = s then (1 : Z_max) else (0 : Z_max)) := by
      rw [karp_d, if_pos rfl, Z_max.zero_eq]
    rw [hkarp]
    have hlast : Fin.last 0 = (0 : Fin 1) := (Subsingleton.elim (0 : Fin 1) (Fin.last 0)).symm
    simp only [walkWeight, Fin.prod_univ_zero, hlast]
    -- but : if v = s then 1 else 0 = sup_f if (f 0 = s ∧ f 0 = v) then 1 else 0
    refine le_antisymm ?_ ?_
    · -- LHS ≤ RHS
      by_cases h : v = s
      · rw [if_pos h]
        have hw : (fun f : Fin 1 → V => if f 0 = s ∧ f 0 = v then (1 : Z_max) else (0 : Z_max))
            (fun _ => s) = 1 := by simp [h]
        exact hw.symm.le.trans
          (le_sup_univ (fun f : Fin 1 → V => if f 0 = s ∧ f 0 = v then (1 : Z_max) else (0 : Z_max))
            (fun _ => s))
      · rw [if_neg h]; exact bot_le
    · -- RHS ≤ LHS
      refine Finset.sup_le (fun f _ => ?_)
      by_cases hfv : f 0 = s ∧ f 0 = v
      · rw [if_pos hfv]
        have hvs : v = s := hfv.2.symm.trans hfv.1
        rw [hvs, if_pos rfl]
      · rw [if_neg hfv]; exact bot_le
  | succ k ih =>
    -- Pas k → k+1 : on prouve LHS = M et RHS = M (M = sup_g if g 0=s then W_k g * w(g(last k),v) else 0)
    -- via le_antisymm avec témoins (évite la distribution `ite_mul` absente de Mathlib).
    have hkarp : karp_d E s (k+1) v =
        (Finset.univ : Finset V).sup (fun u => karp_d E s k u * E.weight (u, v)) := by
      rw [karp_d, if_neg (Nat.succ_ne_zero k), show (k + 1) - 1 = k from by omega]
    rw [hkarp]
    let M := (Finset.univ : Finset (Fin (k+1) → V)).sup (fun g =>
      if g 0 = s then walkWeight E k g * E.weight (g (Fin.last k), v) else (0 : Z_max))
    have hL : (Finset.univ : Finset V).sup (fun u => karp_d E s k u * E.weight (u, v)) = M := by
      refine le_antisymm ?_ ?_
      · -- LHS ≤ M
        refine Finset.sup_le (fun u _ => ?_)
        rw [ih u, Z_max.sup_mul_right]
        refine Finset.sup_le (fun g _ => ?_)
        by_cases hgu : g 0 = s ∧ g (Fin.last k) = u
        · rw [if_pos hgu, ← hgu.2]
          have hkey : (fun g => if g 0 = s then walkWeight E k g * E.weight (g (Fin.last k), v)
              else (0 : Z_max)) g = walkWeight E k g * E.weight (g (Fin.last k), v) := if_pos hgu.1
          rw [← hkey]
          exact le_sup_univ
            (fun g => if g 0 = s then walkWeight E k g * E.weight (g (Fin.last k), v) else (0 : Z_max))
            g
        · rw [if_neg hgu, Z_max.zero_mul]; exact bot_le
      · -- M ≤ LHS
        refine Finset.sup_le (fun g _ => ?_)
        by_cases hg : g 0 = s
        · rw [if_pos hg]
          have h1 : walkWeight E k g * E.weight (g (Fin.last k), v) ≤
              karp_d E s k (g (Fin.last k)) * E.weight (g (Fin.last k), v) := by
            rw [ih (g (Fin.last k)), Z_max.sup_mul_right]
            have heq : (if g 0 = s ∧ g (Fin.last k) = g (Fin.last k) then walkWeight E k g
                else (0 : Z_max)) * E.weight (g (Fin.last k), v) =
                walkWeight E k g * E.weight (g (Fin.last k), v) := by
              rw [if_pos ⟨hg, rfl⟩]
            rw [← heq]
            exact le_sup_univ
              (fun g' => (if g' 0 = s ∧ g' (Fin.last k) = g (Fin.last k) then walkWeight E k g'
                else (0 : Z_max)) * E.weight (g (Fin.last k), v))
              g
          have h2 : karp_d E s k (g (Fin.last k)) * E.weight (g (Fin.last k), v) ≤
              (Finset.univ : Finset V).sup (fun u => karp_d E s k u * E.weight (u, v)) :=
            le_sup_univ (fun u => karp_d E s k u * E.weight (u, v)) (g (Fin.last k))
          exact h1.trans h2
        · rw [if_neg hg]; exact bot_le
    have hR : (Finset.univ : Finset (Fin (k+2) → V)).sup (fun f =>
        if f 0 = s ∧ f (Fin.last (k+1)) = v then walkWeight E (k+1) f else (0 : Z_max)) = M := by
      refine le_antisymm ?_ ?_
      · -- RHS ≤ M (témoins : préfixe f ∘ castSucc)
        refine Finset.sup_le (fun f _ => ?_)
        by_cases hf : f 0 = s ∧ f (Fin.last (k+1)) = v
        · rw [if_pos hf, walkWeight_succ, hf.2]
          have hg0 : (f ∘ Fin.castSucc) 0 = s := by
            rw [Function.comp_apply, Fin.castSucc_zero]; exact hf.1
          have hgeq : f (Fin.last k).castSucc = (f ∘ Fin.castSucc) (Fin.last k) := by
            rw [Function.comp_apply]
          rw [hgeq]
          have hkey : (fun g => if g 0 = s then walkWeight E k g * E.weight (g (Fin.last k), v)
              else (0 : Z_max)) (f ∘ Fin.castSucc) =
              walkWeight E k (f ∘ Fin.castSucc) * E.weight ((f ∘ Fin.castSucc) (Fin.last k), v) :=
            if_pos hg0
          rw [← hkey]
          exact le_sup_univ
            (fun g => if g 0 = s then walkWeight E k g * E.weight (g (Fin.last k), v) else (0 : Z_max))
            (f ∘ Fin.castSucc)
        · rw [if_neg hf]; exact bot_le
      · -- M ≤ RHS (témoins : Fin.snoc g v)
        refine Finset.sup_le (fun g _ => ?_)
        by_cases hg : g 0 = s
        · rw [if_pos hg]
          have hf0 : (@Fin.snoc (k+1) (fun _ => V) g v) 0 = s := by
            rw [Fin.snoc_apply_zero]; exact hg
          have hflast : (@Fin.snoc (k+1) (fun _ => V) g v) (Fin.last (k+1)) = v := by
            simp only [Fin.snoc_last]
          have hww : walkWeight E (k+1) (Fin.snoc g v) =
              walkWeight E k g * E.weight (g (Fin.last k), v) := walkWeight_snoc E k g v
          rw [← hww]
          have hcond : (@Fin.snoc (k+1) (fun _ => V) g v) 0 = s ∧
              (@Fin.snoc (k+1) (fun _ => V) g v) (Fin.last (k+1)) = v := ⟨hf0, hflast⟩
          have hkey : (fun f => if f 0 = s ∧ f (Fin.last (k+1)) = v then walkWeight E (k+1) f
              else (0 : Z_max)) (Fin.snoc g v) = walkWeight E (k+1) (Fin.snoc g v) := if_pos hcond
          rw [← hkey]
          exact le_sup_univ
            (fun f => if f 0 = s ∧ f (Fin.last (k+1)) = v then walkWeight E (k+1) f else (0 : Z_max))
            (Fin.snoc g v)
        · rw [if_neg hg]; exact bot_le
    exact hL.trans hR.symm

/-! ### Phase A-coh — A2 : attainment du `Finset.sup` (`karp_d` réalisé par un chemin)

    Le `Finset.sup` dans `karp_d_path_weight` est un ⊕-max sur `Fin (k+1) → V` (ensemble fini).
    Sous `karp_d E s k v ≠ ⊥`, le max est **atteint** par un chemin-vecteur `f` (ordre total de
    `Z_max`, transporté depuis `WithBot ℤ`), et cet `f` contribue `walkWeight E k f = karp_d E s k v`.
    C'est le témoin « argmax » dont la Direction A (A5) a besoin : le chemin de longueur `n` réalisant
    `d_n(v)` avant pigeonhole + retrait de cycle. `Z_max` n'a pas d'instance `LinearOrder` (on ne
    l'ajoute pas — risque D5 sur les preuves spectrales aval) : on dérive un `le_total` local par
    transport via `zmaxOrderIso` (avec `le_total` sur `WithBot ℤ`, qui est linéaire). -/

/-- `le_total` local pour `Z_max` par transport depuis `WithBot ℤ` (linéaire) via `zmaxOrderIso`.
    On n'ajoute PAS d'instance `LinearOrder Z_max` (D5 : éviter les diamants sur les preuves
    spectrales aval `cycleTEG_iff_edgeSetCycle`/T6/DualDAG) ; ce lemme isolé suffit à l'attainment. -/
private lemma le_total_Zmax (a b : Z_max) : a ≤ b ∨ b ≤ a := by
  have h := le_total (Z_max_toWithBot a) (Z_max_toWithBot b)
  simp only [toWithBot_le_iff] at h
  exact h

/-- Attainment du `Finset.sup` sur `Z_max` : sur un ensemble fini non-vide, le ⊕-sup est réalisé
    par un élément (ordre total via `le_total_Zmax`). Spécialisation de `Finset.sup_mem_of_nonempty`
    (qui exige `LinearOrder`) à `Z_max` sans instance globale. -/
private lemma Zmax_finset_sup_attained {α : Type*} [DecidableEq α] (s : Finset α) (f : α → Z_max)
    (hs : s.Nonempty) : ∃ a ∈ s, f a = s.sup f := by
  classical
  induction s using Finset.induction with
  | empty => simp at hs
  | insert a s has ih =>
    rw [Finset.sup_insert]
    cases s.eq_empty_or_nonempty with
    | inl hsempty =>
      rw [hsempty, Finset.sup_empty, sup_bot_eq]
      refine ⟨a, Finset.mem_insert_self _ _, rfl⟩
    | inr hne =>
      obtain ⟨b, hb, hbh⟩ := ih hne
      by_cases hab : f a ≤ s.sup f
      · rw [sup_eq_right.mpr hab]
        refine ⟨b, Finset.mem_insert_of_mem hb, hbh⟩
      · have hle : s.sup f ≤ f a := (le_total_Zmax (f a) (s.sup f)).resolve_left hab
        rw [sup_eq_left.mpr hle]
        refine ⟨a, Finset.mem_insert_self _ _, rfl⟩

/-- **A2** : si `karp_d E s k v ≠ ⊥`, le ⊕-sup des poids de chemins de longueur `k` de `s` à `v`
    est **atteint** par un chemin-vecteur `f` partant de `s`, finissant en `v`, de poids `walkWeight`
    exactement `karp_d E s k v`. C'est le témoin argmax de la Direction A (A5). La finitude de
    `karp_d_path_weight` (sup sur `Fin (k+1) → V` fini) + l'attainment (`Zmax_finset_sup_attained`,
    `V` non-vide via le témoin `v`) ferment l'existence. `g f ≠ ⊥` ⟹ la condition `f 0 = s ∧
    f (last k) = v` est vraie (sinon `g f = 0 = ⊥`), donc `walkWeight E k f = g f = karp_d`. -/
lemma exists_path_weight_eq_karp_d {V : Type*} [Fintype V] [DecidableEq V] (E : EdgeSet V)
    (s : V) (k : ℕ) (v : V) (h : karp_d E s k v ≠ (⊥ : Z_max)) :
    ∃ f : Fin (k+1) → V, f 0 = s ∧ f (Fin.last k) = v ∧ walkWeight E k f = karp_d E s k v := by
  set g : (Fin (k+1) → V) → Z_max :=
    (fun f => if f 0 = s ∧ f (Fin.last k) = v then walkWeight E k f else (0 : Z_max)) with hg
  have hne : (Finset.univ : Finset (Fin (k+1) → V)).Nonempty :=
    ⟨fun _ => v, Finset.mem_univ _⟩
  obtain ⟨f, hf, hfval⟩ := Zmax_finset_sup_attained Finset.univ g hne
  have hgv : Finset.sup (Finset.univ : Finset (Fin (k+1) → V)) g ≠ (⊥ : Z_max) := by
    rw [hg, ← karp_d_path_weight E s k v]; exact h
  have hgfne : g f ≠ (⊥ : Z_max) := by rw [hfval]; exact hgv
  by_cases hcond : f 0 = s ∧ f (Fin.last k) = v
  · refine ⟨f, hcond.1, hcond.2, ?_⟩
    have hgw : walkWeight E k f = g f := by
      show walkWeight E k f =
        (if f 0 = s ∧ f (Fin.last k) = v then walkWeight E k f else (0 : Z_max))
      rw [if_pos hcond]
    rw [hgw, hfval, hg, ← karp_d_path_weight E s k v]
  · exfalso
    have hgfne' : (if f 0 = s ∧ f (Fin.last k) = v then walkWeight E k f else (0 : Z_max)) ≠ (⊥ : Z_max) := by
      show g f ≠ ⊥; exact hgfne
    rw [if_neg hcond] at hgfne'
    exact hgfne' (by rfl)

/-! ## Helpers combinatoires pour la preuve Karp (Direction A)

    Lemmes purs sur `List` (pas de dépendance à `karp_d`), réutilisables pour la Direction A
    (raccourcissement par pigeonhole + extraction de cycle). -/

/-- Pigeonhole (Fintype) : une liste strictement plus longue que le cardinal du type
    contient deux éléments égaux à des positions distinctes `i < j`. Utilisé par la
    Direction A (un chemin de longueur `n > |V|` a un sommet répété, dont on extrait un
    cycle de mean ≤ μ*). Les bornes `hi`/`hj` sont des témoins explicites de l'∃ (les
    preuves `by omega` inline ne voient pas `i < j` en position de terme). -/
lemma exists_repeated_of_length_gt_card {α : Type*} [Fintype α] [DecidableEq α]
    (l : List α) (h : Fintype.card α < l.length) :
    ∃ (i j : ℕ) (hi : i < l.length) (hj : j < l.length),
      i < j ∧ l.get ⟨i, hi⟩ = l.get ⟨j, hj⟩ := by
  by_contra hcon
  push_neg at hcon
  -- hcon : ∀ i j hi hj, ¬ (i < j ∧ l.get ⟨i, hi⟩ = l.get ⟨j, hj⟩)
  have hnodup : l.Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_get]
    rintro i j hij heq
    exact hcon i.val j.val i.isLt j.isLt hij heq
  have hle : l.length ≤ Fintype.card α := List.Nodup.length_le_card hnodup
  omega

/-- Maximum cycle mean using Karp's formula:
    λ* = max_v min_{0 ≤ k < n} (d_n(v) - d_k(v)) / (n - k)   (Karp 1978).

    In max-plus, subtraction is standard integer subtraction and division by n-k
    corresponds to dividing the integer weight difference by (n-k).

    **Bug D corrigé (2026-07-22, pré-preuve Karp)** : l'ancien code utilisait `Finset.sup`
    sur `k` (= `max_v max_k`), masqué sous les poids totaux (max_k = min_k triviaux) ;
    le fix (a) (off-edge ⊥) l'exposait — l'énoncé aurait été faux. Karp exige le **min**
    sur `k`. Comme `Z_max` n'a pas de ⊤/+∞ pour ignorer les termes où `d_k(v) = ⊥`
    (pas de chemin de longueur `k`), on **filtre** les `k` de `d_k(v)` fini puis on prend
    `Finset.inf'` (min) sur l'ensemble non-vide. Sous `Irreducible E` (forte connexité,
    hypothèse de `maxCycleMeanKarp_correct`) : `d_n(v)` est fini pour tout `v` (chemin de
    longueur `n` existe) et l'ensemble filtré est non-vide (`s` atteint `v` en `< n` pas).
    Hors irréductibilité, la définition peut donner `⊥` (le théorème ne prétend l'égalité
    que sous `Irreducible E`) ; cas acyclique → `d_n(v) = ⊥` ∀v → `⊥` (#3). -/
noncomputable def maxCycleMeanKarp {V : Type*} [Fintype V] [DecidableEq V] (E : EdgeSet V) : WithBot ℝ :=
  if h : 0 < Fintype.card V then
    have h₁ : Nonempty V := by
      rw [Fintype.card_pos_iff] at h
      exact h
    let s : V := Classical.arbitrary V
    let n : ℕ := Fintype.card V
    -- λ* = max_v min_{0 ≤ k < n} (d_n(v) - d_k(v)) / (n - k)  (Karp 1978), en ℝ (NON planché).
    -- Relecture R1 (2026-07-29) : la valeur propre max-plus d'une matrice entière est
    -- **rationnelle** (BCOQ/Butkovič) ; `Z_max` (entiers) ne la représente pas, et le
    -- planchage `ofInt ((n_val-k_val)/(n-k))` = ⌊λ*⌋ rendait `#4` (réel↔planché) faux pour
    -- λ* fractionnaire et faisait passer les circuits Ponzi sous-unitaires (λ*∈(0,1)) au
    -- screening No-Ponzi. Les `karp_d`/`d_k` restent dans `Z_max` (poids de chemins = sommes
    -- entières) ; seul le **ratio** passe en ℝ (portage `Z_max → WithBot ℝ`, miroir de `Z_max`
    -- avec `⊥ = −∞` pour les cas acycliques / non-atteints). Le seuil `(0 : WithBot ℝ)` vaut
    -- maintenant `some 0` (le vrai zéro réel), pas `⊥ = −∞` comme `(0 : Z_max)`.
    Finset.sup (Finset.univ : Finset V) fun v =>
      let d_n : Z_max := (karp_d E s n) v
      match d_n with
      | Z_max.ofInt n_val =>
        -- k < n tels que d_k(v) est fini (il existe un chemin de longueur k de s à v).
        let ks : Finset ℕ :=
          (Finset.Iio n).filter (fun k => (karp_d E s k v) ≠ (⊥ : Z_max))
        if hks : ks.Nonempty then
          -- min sur ces k de (d_n(v) - d_k(v)) / (n - k)  (Karp's min_k), en ℝ
          ks.inf' hks (fun k =>
            match karp_d E s k v with
            | Z_max.ofInt k_val => WithBot.some (((n_val - k_val) : ℝ) / ((n - k) : ℝ))
            | _ => (⊥ : WithBot ℝ))
        else
          (⊥ : WithBot ℝ)
      | _ => (⊥ : WithBot ℝ)
  else
    (⊥ : WithBot ℝ)

/-! ## Helpers : ⊗-homomorphisme `ofInt`, conversion `toInt`, manipulation `List.get`/`IsChain`

    Le poids max-plus d'un chemin/cycle est le **produit ⊗** des poids d'arêtes (= somme
    entière, car `* = ⊗ = +` sur `Z_max`), NON la somme ⊕ (`= max`). `cycleWeight`
    ci-dessous utilise donc `Finset.prod` (⊗-fold). Le pont `∏ ofInt = ofInt (∑)` est la
    clé du portage de `cycleWeight_TEG_eq_Karp` (Semaine 4) — cf. bac-à-sable
    `test_cycle_proof.lean` (`ofInt_prod_eq_ofInt_sum`/`toInt_ofInt`, sorry-free).
    Les helpers `get_fin_*`/`isChain_iff_forall_get` (mêmes que `ExtensionInfinie.lean`,
    recopiés ici car `KarpAlgorithm` ne peut importer `ExtensionInfinie` — cycle
    d'imports) servent à `isCycle_iff_chain` et à la manipulation du RHS filtré de
    `maxCycleMeanKarp_correct` (Semaines 2-3). -/

/-- `Finset.prod s (ofInt ∘ f) = ofInt (Finset.sum s f)` : `ofInt` est un morphisme
    `(ℤ, +, 0) →* (Z_max, *, 1)` (`ofInt (a + b) = ofInt a * ofInt b` et `ofInt 0 = 1`
    sont `rfl` via `Z_max.mul` / instance `One`). Le produit ⊗ redonne la somme entière.
    (= helper T2 `cycleWeight_prod_eq_sum`, porté du bac-à-sable `test_cycle_proof.lean`.) -/
lemma ofInt_prod_eq_ofInt_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℤ) :
    (Finset.prod s fun i => Z_max.ofInt (f i)) = Z_max.ofInt (Finset.sum s fun i => f i) := by
  exact Finset.induction_on s
    (by rw [Finset.prod_empty, Finset.sum_empty]; rfl)
    (by intro a t hat hit; rw [Finset.prod_insert hat, Finset.sum_insert hat, hit]; rfl)

/-- `(ofInt n).toInt = n` par réduction du `match` (`rfl`). -/
@[simp] lemma toInt_ofInt (n : ℤ) : (Z_max.ofInt n).toInt = n := rfl

/-- Deux preuves d'index pour le même `i` donnent le même `List.get`. -/
theorem get_fin_irrel {α : Type*} (l : List α) (i : ℕ) (h₁ h₂ : i < l.length) :
    l.get ⟨i, h₁⟩ = l.get ⟨i, h₂⟩ := by
  have he : (⟨i, h₁⟩ : Fin l.length) = ⟨i, h₂⟩ := Fin.eq_of_val_eq (by rfl)
  rw [he]

/-- Égalité de `List.get` pour deux indices propositionnellement égaux `i = j`.
    La preuve d'index source `hi` est implicite (inférée depuis le terme ciblé par `rw`),
    ce qui permet de réécrire `l.get ⟨i, _⟩` (borne source non nommable) vers
    `l.get ⟨j, hj⟩` — utile quand la borne source provient d'un calcul (drop/take). -/
theorem get_fin_eq {α : Type*} (l : List α) {i j : ℕ} (hij : i = j)
    {hi : i < l.length} (hj : j < l.length) :
    l.get ⟨i, hi⟩ = l.get ⟨j, hj⟩ := by
  rw [show (⟨i, hi⟩ : Fin l.length) = ⟨j, hj⟩ from Fin.eq_of_val_eq hij]

/-- `(l₁ ++ l₂).get ⟨i, _⟩ = l₁.get ⟨i, h⟩` quand `i < l₁.length`. -/
theorem get_append_left_fin {α : Type*} {l₂ : List α} (l₁ : List α) {i : ℕ}
    (h : i < l₁.length) {h' : i < (l₁ ++ l₂).length} :
    (l₁ ++ l₂).get ⟨i, h'⟩ = l₁.get ⟨i, h⟩ := by
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_append_left h]

/-- `(l₁ ++ l₂).get ⟨i, _⟩ = l₂.get ⟨i - l₁.length, _⟩` quand `l₁.length ≤ i` (miroir droit de
    `get_append_left_fin`). Évite de réécrire `l₁.length` (le preuve `getElem_append_right` en
    dépend) : on garde `i - l₁.length` formé sur la longueur réelle, puis `get_drop_eq`/`get_fin_eq`
    règlent l'arithmétique d'index en monde Fin (preuves irrélevantes). -/
theorem get_append_right_fin {α : Type*} (l₁ l₂ : List α) {i : ℕ}
    (h : l₁.length ≤ i) {h' : i < (l₁ ++ l₂).length} :
    (l₁ ++ l₂).get ⟨i, h'⟩ = l₂.get ⟨i - l₁.length, by
      have hh := h'; rw [List.length_append] at hh; omega⟩ := by
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_append_right h]

/-- Pont `IsChain R l ↔ ∀ i, i+1 < l.length → R (l[i]) (l[i+1])` (forme par-index).
    Les preuves d'index sont des TERMES (`Nat.lt_of_succ_lt hi`, `hi`) — pas de
    `by omega` sous binder, qui ne voit pas l'hypothèse anonyme. -/
lemma isChain_iff_forall_get {α : Type*} (l : List α) (R : α → α → Prop) :
    l.IsChain R ↔
      ∀ (i : ℕ) (hi : i + 1 < l.length),
        R (l.get ⟨i, Nat.lt_of_succ_lt hi⟩) (l.get ⟨i + 1, hi⟩) := by
  rw [List.isChain_iff_forall₂, List.forall₂_iff_get]
  refine ⟨fun ⟨heq, h⟩ i hi => ?_, fun h => ⟨?_, fun i h₁ h₂ => ?_⟩⟩
  · have hd : i < l.dropLast.length := by simp; omega
    have ht : i < l.tail.length := by simp; omega
    have g1 : l.dropLast.get ⟨i, hd⟩ = l.get ⟨i, Nat.lt_of_succ_lt hi⟩ := by
      rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_dropLast]
    have g2 : l.tail.get ⟨i, ht⟩ = l.get ⟨i + 1, hi⟩ := by
      rw [List.get_tail l i ht hi]
    rw [← g1, ← g2]; exact h i hd ht
  · simp [List.length_dropLast, List.length_tail]
  · have hi : i + 1 < l.length := by
      have : i < l.tail.length := h₂
      simp [List.length_tail] at this
      omega
    have g1 : l.dropLast.get ⟨i, h₁⟩ = l.get ⟨i, Nat.lt_of_succ_lt hi⟩ := by
      rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_dropLast]
    have g2 : l.tail.get ⟨i, h₂⟩ = l.get ⟨i + 1, hi⟩ := by
      rw [List.get_tail l i h₂ hi]
    rw [g1, g2]; exact h i hi

/-- A cycle in an EdgeSet is a list of vertices where:
    1. Length ≥ 2
    2. Each consecutive pair is an edge in the set
    3. The first vertex equals the last -/
def isCycle {V : Type*} [DecidableEq V] (E : EdgeSet V) (c : List V) : Prop :=
  c.length ≥ 2 ∧
  (∀ (i : ℕ) (h_i : i < c.length - 1), (c.get ⟨i, by
    -- Prove i < c.length given i < c.length - 1
    have h_len : c.length ≥ 2 := by
      by_contra h
      have h₁ : c.length ≤ 1 := by omega
      have h₂ : c.length - 1 = 0 := by
        interval_cases c.length <;> simp_all [Nat.sub_eq_zero_iff_le]
        <;> aesop
      have h₃ : i < c.length - 1 := h_i
      rw [h₂] at h₃
      omega
    have h_lt : c.length - 1 < c.length := by
      have h₃ : c.length ≥ 2 := h_len
      omega
    omega⟩, c.get ⟨i + 1, by
    have h_len : c.length ≥ 2 := by
      by_contra h
      have h₁ : c.length ≤ 1 := by omega
      have h₂ : c.length - 1 = 0 := by
        interval_cases c.length <;> simp_all [Nat.sub_eq_zero_iff_le]
        <;> aesop
      have h₃ : i < c.length - 1 := h_i
      rw [h₂] at h₃
      omega
    have h_lt : c.length - 1 < c.length := by
      have h₃ : c.length ≥ 2 := h_len
      omega
    have h₂ : i + 1 < c.length := by
      have h₃ : i < c.length - 1 := h_i
      omega
    exact h₂⟩) ∈ E.edges) ∧
  (∀ (h_len : c.length ≥ 2), c.get ⟨0, by omega⟩ = c.get ⟨c.length - 1, by
    have h₁ : c.length - 1 < c.length := by
      have h₂ : c.length ≥ 2 := h_len
      omega
    exact h₁⟩)

/-- Weight of a cycle in an EdgeSet, in the max-plus sense.

    In max-plus algebra, the weight of a path/cycle is the **⊗-product** of its
    edge weights (not the ⊕-sum): since `* = ⊗ = integer +` on `Z_max`, the
    ⊗-fold of `ofInt aᵢ` is `ofInt (Σ aᵢ)` — i.e. the *regular integer sum* of
    the edge weights. Using `Finset.sum` here would instead compute the ⊕-fold
    (`max`, since `+ = ⊕`), which is **not** the cycle weight. Hence `Finset.prod`.

    `Fin (c.length - 1)` carries the bound proof `i < c.length - 1` natively. -/
def cycleWeight {V : Type*} [DecidableEq V] (E : EdgeSet V) (c : List V) : Z_max :=
  if h : c.length ≥ 2 then
    (Finset.univ : Finset (Fin (c.length - 1))).prod (fun i =>
      let i_val : ℕ := i.val
      have h₁ : i_val < c.length - 1 := i.isLt
      have h₂ : i_val + 1 < c.length := by
        have h₃ : c.length - 1 < c.length := by
          omega
        omega
      have h₃ : i_val < c.length := by
        omega
      E.weight (c.get ⟨i_val, by omega⟩, c.get ⟨i_val + 1, by omega⟩))
  else
    Z_max.negInf

/-- Mean weight of a cycle `c` = `cycleWeight / (c.length - 1)`, en ℝ (NON planché).
    `cycleWeight E c` reste dans `Z_max` (= somme ⊗-entière des poids d'arêtes,
    `c.length - 1` = nombre d'arêtes de la représentation fermée) ; on en extrait l'entier
    via `.toInt` puis on divise en ℝ. Relecture R1 (2026-07-29) : la moyenne de cycle est
    **rationnelle** (pas entière en général) ; l'ancien `ofInt (Σ / (c.length-1) : ℤ)`
    planchait en ⌊μ⌋, rendant `#4` (réel↔planché) faux pour μ fractionnaire et le screening
    No-Ponzi insensible aux circuits Ponzi sous-unitaires (μ∈(0,1)). Portage `Z_max → WithBot ℝ`
    (`⊥` pour `c.length < 2` = pas un cycle), miroir de `maxCycleMeanKarp`. -/
noncomputable def cycleMean {V : Type*} [DecidableEq V] (E : EdgeSet V) (c : List V) : WithBot ℝ :=
  if _h : c.length ≥ 2 then
    WithBot.some (((cycleWeight E c).toInt : ℝ) / ((c.length - 1) : ℝ))
  else
    (⊥ : WithBot ℝ)

/-- Équivalence entre `isCycle` et la forme `IsChain` + premier=dernier.
    L'hypothèse `(h : c.length ≥ 2)` factise la condition de borne (miroir du 3ᵉ conjoint
    `∀ hlen` de `isCycle`) : les preuves d'index `c.get ⟨0, …⟩` / `c.get ⟨c.length-1, …⟩`
    ne sont PAS déchargeables en position de terme sans cette hypothèse en scope
    (cf. ancien énoncé à 3 sorries, relecture code 2026-07-22). La preuve aligne les
    preuves d'index par `get_fin_irrel` (irrélevance de preuve sur `List.get`) — même
    technique que le bac-à-sable `test_cycle_proof.lean:cycleTEG_iff_edgeSetCycle`. -/
lemma isCycle_iff_chain {V : Type*} [DecidableEq V] (E : EdgeSet V) (c : List V)
    (h : c.length ≥ 2) :
    isCycle E c ↔
      c.IsChain (fun u v => (u, v) ∈ E.edges) ∧
      c.get ⟨0, by omega⟩ = c.get ⟨c.length - 1, by omega⟩ := by
  constructor
  · -- sens direct : isCycle E c → IsChain ∧ (premier = dernier)
    intro hc
    have hchain := hc.2.1   -- ∀ i (hi: i<c.length-1), (c[i], c[i+1]) ∈ E.edges
    refine ⟨?_, ?_⟩
    · -- IsChain via le pont par-index (preuves `Nat.lt_of_succ_lt hi`, `hi`)
      apply (isChain_iff_forall_get c (fun u v => (u, v) ∈ E.edges)).mpr
      intro i hi   -- hi : i + 1 < c.length
      have hi' : i < c.length - 1 := by omega
      have Hedge := hchain i hi'
      -- Hedge : (c.get ⟨i, _⟩, c.get ⟨i+1, _⟩) ∈ E.edges  (preuves = omega de la def)
      rw [get_fin_irrel c i _ (Nat.lt_of_succ_lt hi),
          get_fin_irrel c (i + 1) _ hi] at Hedge
      exact Hedge
    · -- premier = dernier : on instancie le 3ᵉ conjoint (∀ hlen) puis on aligne les preuves
      have hfl := hc.2.2 h
      rw [get_fin_irrel c 0 _ (by omega : 0 < c.length),
          get_fin_irrel c (c.length - 1) _ (by omega : c.length - 1 < c.length)] at hfl
      exact hfl
  · -- sens réciproque : IsChain ∧ (premier = dernier) → isCycle E c
    intro ⟨hchain, hclose⟩
    refine ⟨h, ?_, ?_⟩
    · -- 2ᵉ conjoint : ∀ i (hi: i<c.length-1), (c[i], c[i+1]) ∈ E.edges
      intro i hi   -- hi : i < c.length - 1
      have H := (isChain_iff_forall_get c (fun u v => (u, v) ∈ E.edges)).mp hchain
      have hi' : i + 1 < c.length := by omega
      have Hedge := H i hi'
      -- Hedge : (c.get ⟨i, Nat.lt_of_succ_lt hi'⟩, c.get ⟨i+1, hi'⟩) ∈ E.edges
      rw [get_fin_irrel c i (Nat.lt_of_succ_lt hi') (by omega : i < c.length),
          get_fin_irrel c (i + 1) hi' (by omega : i + 1 < c.length)] at Hedge
      exact Hedge
    · -- 3ᵉ conjoint : ∀ h_len, premier = dernier
      intro h_len
      rw [get_fin_irrel c 0 _ (by omega : 0 < c.length),
          get_fin_irrel c (c.length - 1) _ (by omega : c.length - 1 < c.length)] at hclose
      exact hclose

/-! ### Pièce 2 : extraction de cycle depuis un sommet répété d'une marche (Direction A) -/

/-- Extraction de cycle depuis un sommet répété d'une marche. Soit `l` une marche
    (toute paire consécutive `(l[k], l[k+1]) ∈ E.edges`), avec un sommet répété `l[i] = l[j]`
    (`i < j`) ; la sous-liste `l[i..j]` (incluse, via `drop i |>.take (j-i+1)`) est un cycle
    fermé `isCycle E`. Pièce 2 de la Direction A : le pigeonhole (`exists_repeated_of_length_gt_card`)
    donne `i < j`, ce lemme en fait un cycle (de mean borné par μ*). -/
lemma cycle_from_repeated {V : Type*} [DecidableEq V] (E : EdgeSet V) (l : List V)
    (i j : ℕ) (hi : i < l.length) (hj : j < l.length) (hij : i < j)
    (heq : l.get ⟨i, hi⟩ = l.get ⟨j, hj⟩)
    (hwalk : ∀ k (hk : k + 1 < l.length),
      (l.get ⟨k, Nat.lt_of_succ_lt hk⟩, l.get ⟨k + 1, hk⟩) ∈ E.edges) :
    isCycle E ((l.drop i).take (j - i + 1)) := by
  have hdlen : (l.drop i).length = l.length - i := by rw [List.length_drop]
  have htlen : ((l.drop i).take (j - i + 1)).length = j - i + 1 := by
    rw [List.length_take, hdlen, min_eq_left (by omega)]
  -- (l.drop i).take (j-i+1) .get ⟨k, hk⟩ = l.get ⟨i + k, _⟩
  have hcg : ∀ k (hk : k < ((l.drop i).take (j - i + 1)).length),
      ((l.drop i).take (j - i + 1)).get ⟨k, hk⟩ =
        l.get ⟨i + k, by have : k < ((l.drop i).take (j - i + 1)).length := hk; rw [htlen] at *; omega⟩ := by
    intro k hk
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp only [List.getElem_drop, List.getElem_take]
  refine ⟨?_, ?_, ?_⟩
  · -- longueur ≥ 2
    rw [htlen]; omega
  · -- arêtes consécutives : ∀ k (hk : k < c.length - 1), (c[k], c[k+1]) ∈ E.edges
    intro k hk
    have hk0 : k < ((l.drop i).take (j - i + 1)).length := lt_of_lt_of_le hk (by rw [htlen]; omega)
    have hk1 : k + 1 < ((l.drop i).take (j - i + 1)).length := by rw [htlen]; omega
    have hik : i + k + 1 < l.length := by have : k + 1 < ((l.drop i).take (j - i + 1)).length := hk1; rw [htlen] at *; omega
    have hw := hwalk (i + k) hik
    rw [hcg k hk0, hcg (k + 1) hk1]
    rw [get_fin_irrel l (i + k) _ (Nat.lt_of_succ_lt hik),
        get_fin_irrel l (i + k + 1) _ hik] at hw
    exact hw
  · -- premier = dernier : c.get 0 = c.get (c.length - 1)
    intro hlen
    have h0 : 0 < ((l.drop i).take (j - i + 1)).length := by rw [htlen]; omega
    have hlm : ((l.drop i).take (j - i + 1)).length - 1 <
        ((l.drop i).take (j - i + 1)).length := by rw [htlen]; omega
    rw [hcg 0 h0, hcg (((l.drop i).take (j - i + 1)).length - 1) hlm]
    rw [get_fin_eq l (show i + 0 = i from rfl) hi]
    rw [get_fin_eq l (by rw [htlen]; omega : i + (((l.drop i).take (j - i + 1)).length - 1) = j) hj]
    exact heq

/-! ### Pièce 3 : infrastructure de poids de chemin ouvert (Direction A)

    Poids max-plus d'un chemin **ouvert** vu comme `List V` (miroir ouvert de `cycleWeight`,
    fermé et exigeant `c.length ≥ 2`). Indépendant du choix d'anneau de la moyenne (relecture
    R1 2026-07-29) : c'est un ⊗-produit d'arêtes (= somme entière via `ofInt_prod_eq_ofInt_sum`
    quand les poids sont `ofInt`), pas une moyenne. La pièce 3 `path_shorten_by_cycle_removal`
    (Semaine 2) s'appuie sur `walkWeightL` + `IsWalk` pour relier `d_n` et `d_k` comme poids de
    chemins entiers (via `karp_d_path_weight`). Le pont `walkWeightL ↔ walkWeight` (monde `Fin`)
    et la décomposition de poids par retrait de cycle sont les sous-lemmas suivants (D3
    surveillé : index `Fin`/`List` à la couture). -/

/-- Poids max-plus d'un chemin ouvert `l : List V` : ⊗-produit des arêtes consécutives.
    Défini par **récursion structurelle sur la liste** (3 motifs disjoints couvrant tout
    `List V`) plutôt que par `Finset.prod` sur `Fin (l.length - 1)`. Ce choix **évide la
    couture `Fin`/`List`** qui bloquait le pont `walkWeight_eq_walkWeightL` : la décomposition
    se fait par `cons`, et le pont se prouve par induction sur `k` via `List.ofFn_succ` —
    sans jamais comparer `Fin ((ofFn f).length - 1)` à `Fin k` (non-defeq, car
    `List.length_ofFn`/`List.ofFn_succ` se prouvent par induction, pas `rfl`). Rend aussi
    `path_shorten_by_cycle_removal` naturel (découpe `cons`/`take`/`drop` au lieu de
    `Finset.prod_univ` sur `Fin (length-1)`). Sémantique identique à l'ancienne version :
    `1` (⊗-unit) pour 0 ou 1 sommet (0 arête), sinon `E.weight (a, b) ⊗` queue. -/
def walkWeightL {V : Type*} [DecidableEq V] (E : EdgeSet V) : List V → Z_max
  | [] => 1
  | [_] => 1
  | a :: b :: rest => E.weight (a, b) * walkWeightL E (b :: rest)

/-- Équation de récurrence « cons-cons » de `walkWeightL` : détacher la 1ʳᵉ arête d'un
    chemin de ≥ 2 sommets. Miroir « split first » de `walkWeight_cons`, forme nommée pour
    `rw` dans le pont (la réduction `simp [walkWeightL]` seule ne déclenche pas sur une
    liste en forme `ofFn` non-visible). -/
lemma walkWeightL_cons_cons {V : Type*} [DecidableEq V] (E : EdgeSet V) (a b : V)
    (l : List V) :
    walkWeightL E (a :: b :: l) = E.weight (a, b) * walkWeightL E (b :: l) := by
  simp [walkWeightL]

/-- Factorisation du poids d'une concaténation : `walkWeightL (l₁ ++ l₂)` = poids de `l₁`
    ⊗ arête de jonction `(l₁.getLast, l₂.head)` ⊗ poids de `l₂`, quand `l₁` et `l₂` sont
    non-vides. La jonction est exactement l'arête manquante entre la dernière arête de `l₁`
    et la première de `l₂`. Preuve par récursion `cons` sur `l₁` (généralisant `l₂`) :
    `[_]` (cas `l₁=[a]`, déplie `l₂=c::l₂'` via `l₂≠[]`) et `a::b::rest'` (cas ≥2 éléments,
    IH sur `rest'` + `getLast_cons` `(a::b::rest').getLast = (b::rest').getLast`). Réutilisé
    par `path_shorten` (Direction A pièce 3) pour le poids du chemin raccourci `l.take(i+1) ++ l.drop(j+1)`. -/
lemma walkWeightL_append {V : Type*} [DecidableEq V] (E : EdgeSet V) (l₁ l₂ : List V)
    (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    walkWeightL E (l₁ ++ l₂) =
      walkWeightL E l₁ * E.weight (l₁.getLast h₁, l₂.head h₂) * walkWeightL E l₂ := by
  induction l₁ generalizing l₂ with
  | nil => exact absurd rfl h₁
  | cons a rest ih =>
    by_cases hrest : rest = []
    · -- l₁ = [a] ; l₁ ++ l₂ = a :: l₂ ; l₂ = c :: l₂' (non-vide)
      subst hrest
      obtain ⟨c, l₂', rfl⟩ := List.exists_cons_of_ne_nil h₂
      -- Expose la forme `a :: c :: l₂'` (le but a `[a] ++ c :: l₂'`, defeq mais non syntaxique)
      rw [show [a] ++ (c :: l₂') = a :: c :: l₂' from rfl]
      -- walkWeightL (a::c::l₂') = E.weight(a,c) * walkWeightL(c::l₂') ; walkWeightL [a] = 1 ;
      -- [a].getLast = a ; (c::l₂').head = c ; 1 * x = x.
      simp only [walkWeightL, List.getLast_singleton, List.head_cons, one_mul]
    · -- l₁ = a :: b :: rest' ; but LHS = (a::b::rest') ++ l₂, à ramener en a :: b :: (rest' ++ l₂)
      obtain ⟨b, rest', rfl⟩ := List.exists_cons_of_ne_nil hrest
      rw [show (a :: b :: rest') ++ l₂ = a :: b :: (rest' ++ l₂) from rfl]
      have hih := ih l₂ (List.cons_ne_nil b rest') h₂
      -- (a::b::rest').getLast = (b::rest').getLast  [getLast_cons]
      have hlast : (a :: b :: rest').getLast (List.cons_ne_nil a (b :: rest')) =
          (b :: rest').getLast (List.cons_ne_nil b rest') := by simp [List.getLast_cons]
      -- (b::rest') ++ l₂ ≡ b :: (rest' ++ l₂)  (defeq, cas cons de append)
      have hcons_app : (b :: rest') ++ l₂ = b :: (rest' ++ l₂) := rfl
      -- Réductions isolées (évite que `rw` réduise les deux côtés à la fois)
      have hL : walkWeightL E (a :: b :: (rest' ++ l₂)) = E.weight (a, b) * walkWeightL E (b :: (rest' ++ l₂)) :=
        walkWeightL_cons_cons E a b (rest' ++ l₂)
      have hR : walkWeightL E (a :: b :: rest') = E.weight (a, b) * walkWeightL E (b :: rest') :=
        walkWeightL_cons_cons E a b rest'
      rw [hL, ← hcons_app, hih, hR, hlast]; ac_rfl

/-- Découpe du poids au point `n` : `walkWeightL l` = poids du préfixe `l.take n` ⊗ arête
    « pont » `E.weight (l[n-1], l[n])` ⊗ poids du suffixe `l.drop n`, pour `0 < n < l.length`.
    Cas spécialisé de `walkWeightL_append` sur `take_append_drop`, l'arête pont étant exactement
    l'arête d'indice `n-1` (jonction préfixe/suffixe). Réutilisé pour `path_shorten` (Direction A
    pièce 3) : découper `l` autour du cycle extrait. -/
lemma walkWeightL_take_drop {V : Type*} [DecidableEq V] (E : EdgeSet V) (l : List V) (n : ℕ)
    (h0 : 0 < n) (hn : n < l.length) :
    walkWeightL E l =
      walkWeightL E (l.take n) * E.weight (l.get ⟨n-1, by omega⟩, l.get ⟨n, hn⟩) * walkWeightL E (l.drop n) := by
  have htn : l.take n ≠ [] := by
    have hl : (l.take n).length = n := by rw [List.length_take, min_eq_left (le_of_lt hn)]
    rw [← List.length_pos_iff_ne_nil, hl]; omega
  have hdn : l.drop n ≠ [] := by
    have hl : (l.drop n).length = l.length - n := List.length_drop
    rw [← List.length_pos_iff_ne_nil, hl]; omega
  -- (take n).getLast = l.get ⟨n-1, _⟩ ; (drop n).head = l.get ⟨n, _⟩
  have hlt : (l.take n).length = n := by rw [List.length_take, min_eq_left (le_of_lt hn)]
  have hlast : (l.take n).getLast htn = l.get ⟨n-1, by omega⟩ := by
    rw [List.getLast_eq_getElem, List.get_eq_getElem]
    simp [List.getElem_take, hlt]
  have hhead : (l.drop n).head hdn = l.get ⟨n, hn⟩ := by
    rw [List.head_eq_getElem_zero, List.get_eq_getElem]
    simp [List.getElem_drop]
  -- Ne réécrit `l` que côté LHS (sinon le Fin `l.get ⟨n, hn⟩` côté RHS casse le motive)
  conv_lhs => rw [← List.take_append_drop n l]
  rw [walkWeightL_append _ _ _ htn hdn, hlast, hhead]

/-- `(l.drop n).get ⟨k, hk⟩ = l.get ⟨n + k, …⟩` : accès à un sous-liste décalé ramené à un
    accès direct sur `l` à l'indice `n + k`. Pont `Fin`/`List` pour les arêtes pont des
    découpages `take`/`drop` (la conversion `getElem_drop` seule laisse un indice `n + k` que
    `rw` ne peut pas réécrire sans casser la preuve Fin dépendante ; on referme par `congr 1`
    + `Fin.mk.injEq` + `omega`). -/
lemma get_drop_eq {α : Type*} (l : List α) (n k : ℕ) (hk : k < (l.drop n).length) :
    (l.drop n).get ⟨k, hk⟩ = l.get ⟨n + k, by rw [List.length_drop] at hk; omega⟩ := by
  simp [List.get_eq_getElem, List.getElem_drop]

/-- Découpe trois-segments (Forme « `drop j` », uniforme) : pour `i < j` et `j+1 < l.length`,
    `walkWeightL l` = poids du préfixe `l.take (i+1)` (arêtes `0..i-1`) ⊗ poids du cycle extrait
    `(l.drop i).take (j-i+1)` (arêtes `i..j-1`) ⊗ poids du suffixe `l.drop j` (arêtes `j..fin`).
    Les trois groupes d'arêtes sont **disjoints et couvrent toutes les arêtes de `l`** (les sommets
    de jonction `l[i]`, `l[j]` ne créent pas d'arêtes factices : on multiplie trois poids de chemins
    SÉPARÉS, pas une concaténation). Preuve : `walkWeightL_take_drop` à `i+1` et sur `drop(i+1)`
    à `j-i` (arêtes pont `l[i]→l[i+1]` et `l[j]→l[j+1]` réabsorbées via `walkWeightL_cons_cons`
    dans le cycle et le suffixe), puis `ac_rfl` (⊗ = `*` = `+ℤ` commutatif). Cœur de la Direction A
    pièce 3 : décomposer le poids d'un chemin long en préfixe ⊗ cycle ⊗ suffixe. -/
lemma walkWeightL_split {V : Type*} [DecidableEq V] (E : EdgeSet V) (l : List V) (i j : ℕ)
    (hij : i < j) (hj1 : j + 1 < l.length) :
    walkWeightL E l =
      walkWeightL E (l.take (i+1)) * walkWeightL E ((l.drop i).take (j - i + 1)) * walkWeightL E (l.drop j) := by
  have hi : i < l.length := by omega
  have hj : j < l.length := by omega
  have hi1 : i + 1 < l.length := by omega
  have hjp1 : j + 1 < l.length := hj1
  have hji : 0 < j - i := by omega
  have hji1 : 0 < j - i + 1 := by omega
  set T : List V := (l.drop (i+1)).take (j - i) with hTdef
  set T' : List V := (l.drop (i+2)).take (j - i - 1) with hT'def
  -- A : walkWeightL l = walkWeightL(take(i+1)) * E.weight(l[i], l[i+1]) * walkWeightL(drop(i+1))
  have hA := walkWeightL_take_drop E l (i+1) (by omega : 0 < i + 1) hi1
  -- B : walkWeightL(drop(i+1)) = walkWeightL(T) * E.weight(l[j], l[j+1]) * walkWeightL(drop(j+1))
  have hd1len : (l.drop (i+1)).length = l.length - (i+1) := List.length_drop
  have hBlen : (j - i) < (l.drop (i+1)).length := by rw [hd1len]; omega
  have hB := walkWeightL_take_drop E (l.drop (i+1)) (j - i) hji hBlen
  have hbjm1 : (l.drop (i+1)).get ⟨(j - i) - 1, by rw [hd1len]; omega⟩ = l.get ⟨j, hj⟩ := by
    rw [get_drop_eq]; congr 1; simp only [Fin.mk.injEq]; omega
  have hbj : (l.drop (i+1)).get ⟨j - i, hBlen⟩ = l.get ⟨j + 1, hjp1⟩ := by
    rw [get_drop_eq]; congr 1; simp only [Fin.mk.injEq]; omega
  have hBdrop : (l.drop (i+1)).drop (j - i) = l.drop (j + 1) := by
    rw [List.drop_drop]; congr 1; omega
  -- C : walkWeightL(c) = E.weight(l[i], l[i+1]) * walkWeightL(T),  c = l[i] :: l[i+1] :: T'
  have hdi : l.drop i = l.get ⟨i, hi⟩ :: l.drop (i+1) := List.drop_eq_getElem_cons hi
  have hdi1 : l.drop (i+1) = l.get ⟨i+1, hi1⟩ :: l.drop (i+2) := List.drop_eq_getElem_cons hi1
  have hc : (l.drop i).take (j - i + 1) = l.get ⟨i, hi⟩ :: l.get ⟨i+1, hi1⟩ :: T' := by
    rw [hdi, List.take_cons hji1, show j - i + 1 - 1 = j - i from by omega, hdi1, List.take_cons hji]
  have hT : T = l.get ⟨i+1, hi1⟩ :: T' := by
    rw [hTdef, hdi1, List.take_cons hji]
  have hC : walkWeightL E ((l.drop i).take (j - i + 1)) =
      E.weight (l.get ⟨i, hi⟩, l.get ⟨i+1, hi1⟩) * walkWeightL E T := by
    rw [hc, walkWeightL_cons_cons, hT]
  -- D : walkWeightL(drop j) = E.weight(l[j], l[j+1]) * walkWeightL(drop(j+1))
  have hdj : l.drop j = l.get ⟨j, hj⟩ :: l.drop (j+1) := List.drop_eq_getElem_cons hj
  have hdj1 : l.drop (j+1) = l.get ⟨j+1, hjp1⟩ :: l.drop (j+2) := List.drop_eq_getElem_cons hjp1
  have hD : walkWeightL E (l.drop j) = E.weight (l.get ⟨j, hj⟩, l.get ⟨j+1, hjp1⟩) * walkWeightL E (l.drop (j+1)) := by
    rw [hdj, hdj1, walkWeightL_cons_cons]
  -- Assemblage (⊗ = `*` commutatif → ac_rfl). Les ponts Fin `l.get ⟨k, _⟩` sont ramenés en
  -- getElem (`l.get_eq_getElem`) + `Fin.val_mk` (réduit `↑⟨k,_⟩ → k`), et `i + 1 - 1 → i`
  -- (`Nat.add_sub_cancel`) avant le `ac_rfl` (sinon le `-1` non-defeq bloque l'associativité).
  rw [hA, hB, hbjm1, hbj, hBdrop, hC, hD]
  simp only [List.get_eq_getElem, Fin.val_mk, Nat.add_sub_cancel]
  rw [← hTdef]
  ac_rfl

/-- **Direction A pièce 3 (cœur)** : identité de poids par retrait de cycle. Soit `l` une marche
    avec un sommet répété `l[i] = l[j]` (`i < j`, `j+1 < l.length` non-dégénéré) ; alors
    `walkWeightL l = walkWeightL l' * walkWeightL c` où `l' = l.take (i+1) ++ l.drop (j+1)` est
    le chemin raccourci (retrait du cycle `l[i..j]`, jonction `l[i]→l[j+1]` = `l[j]→l[j+1]` par
    `heq`) et `c = (l.drop i).take (j-i+1)` est le cycle extrait. En max-plus `* = ⊗ = +ℤ`
    (commutatif) : `walkWeightL l = walkWeightL l' + walkWeightL c`, soit `walkWeightL l ≥
    walkWeightL l'` si `walkWeightL c ≤ 0` (cycle de mean ≤ μ*). C'est l'identité qui transforme
    un chemin long en chemin plus court, en payant le poids du cycle retiré — base de la borne
    `d_k(v) ≥ d_n(v) − (n−k)·μ*` de Karp. Preuve : `walkWeightL_split` + `walkWeightL_append`
    (pour `l'`) + `heq` (aligne la jonction) + `ac_rfl`. -/
lemma path_shorten_weight {V : Type*} [DecidableEq V] (E : EdgeSet V) (l : List V) (i j : ℕ)
    (hi : i < l.length) (hj : j < l.length) (hij : i < j) (hj1 : j + 1 < l.length)
    (heq : l.get ⟨i, hi⟩ = l.get ⟨j, hj⟩) :
    walkWeightL E l =
      walkWeightL E (l.take (i+1) ++ l.drop (j+1)) * walkWeightL E ((l.drop i).take (j - i + 1)) := by
  have hi1 : i + 1 < l.length := by omega
  have hjp1 : j + 1 < l.length := hj1
  -- split : walkWeightL l = walkWeightL(take(i+1)) * walkWeightL c * walkWeightL(drop j)
  have hsplit := walkWeightL_split E l i j hij hj1
  -- D : walkWeightL(drop j) = E.weight(l[j], l[j+1]) * walkWeightL(drop(j+1))
  have hdj : l.drop j = l.get ⟨j, hj⟩ :: l.drop (j+1) := List.drop_eq_getElem_cons hj
  have hdj1 : l.drop (j+1) = l.get ⟨j+1, hjp1⟩ :: l.drop (j+2) := List.drop_eq_getElem_cons hjp1
  have hD : walkWeightL E (l.drop j) = E.weight (l.get ⟨j, hj⟩, l.get ⟨j+1, hjp1⟩) * walkWeightL E (l.drop (j+1)) := by
    rw [hdj, hdj1, walkWeightL_cons_cons]
  -- l' append weight : walkWeightL l' = walkWeightL(take(i+1)) * E.weight(l[i], l[j+1]) * walkWeightL(drop(j+1))
  have htn : l.take (i+1) ≠ [] := by
    have hl : (l.take (i+1)).length = i + 1 := by rw [List.length_take, min_eq_left (le_of_lt hi1)]
    rw [← List.length_pos_iff_ne_nil, hl]; omega
  have hdjn : l.drop (j+1) ≠ [] := by
    have hl : (l.drop (j+1)).length = l.length - (j+1) := List.length_drop
    rw [← List.length_pos_iff_ne_nil, hl]; omega
  have hlast : (l.take (i+1)).getLast htn = l.get ⟨i, hi⟩ := by
    rw [List.getLast_eq_getElem, List.get_eq_getElem]
    simp [List.getElem_take, List.length_take, min_eq_left (le_of_lt hi1), Nat.add_sub_cancel]
  have hhead : (l.drop (j+1)).head hdjn = l.get ⟨j+1, hjp1⟩ := by
    rw [List.head_eq_getElem_zero, List.get_eq_getElem]
    simp [List.getElem_drop]
  have hl' : walkWeightL E (l.take (i+1) ++ l.drop (j+1)) =
      walkWeightL E (l.take (i+1)) * E.weight (l.get ⟨i, hi⟩, l.get ⟨j+1, hjp1⟩) * walkWeightL E (l.drop (j+1)) := by
    rw [walkWeightL_append _ _ _ htn hdjn, hlast, hhead]
  -- Assemblage : heq aligne la jonction l[i]→l[j+1] avec l[j]→l[j+1] ; ⊗ commutatif → ac_rfl
  rw [hsplit, hD, hl', heq]; ac_rfl

/-! ### Pièce 3-bis : retrait de cycle dégénéré (cycle touchant le dernier sommet, Direction A)

    Cas dégénéré **requis** (non optionnel) du retrait de cycle, complément de `path_shorten_weight`
    (qui suppose `j+1 < l.length`). Quand le seul sommet répété du pigeonhole est l'extrémité `v`
    (i.e. `j + 1 = l.length`, le cycle extrait `c = l[i..j]` va jusqu'au dernier sommet), il n'y a
    pas de suffixe `l.drop (j+1)` à rejoindre : le chemin raccourci se réduit au préfixe `l.take (i+1)`
    finissant en `l[i] = l[j] = v`. L'identité de poids se simplifie (pas d'arête de jonction à
    aligner, donc pas de `heq`), mais reste un lemme séparé car `walkWeightL_split` exige
    `j+1 < l.length`. Clé : sous `j + 1 = l.length`, le cycle `c = (l.drop i).take (j-i+1)` coïncide
    avec `l.drop i` (même longueur `l.length - i = j - i + 1`). -/

/-- **A1** : identité de poids par retrait de cycle, cas dégénéré `j + 1 = l.length` (le sommet
    répété `l[i] = l[j]` est l'extrémité `v` de la marche). Le cycle extrait `c = (l.drop i).take
    (j-i+1)` égale `l.drop i` (sous `j+1 = l.length`, `(l.drop i).length = l.length - i = j-i+1`),
    donc `walkWeightL E l = walkWeightL E (l.take (i+1)) * walkWeightL E (l.drop i)` : on découpe
    `l` en `take (i+1)` (préfixe) ⊗ arête pont `(l[i], l[i+1])` ⊗ suffixe `l.drop (i+1)` via
    `walkWeightL_take_drop`, et `walkWeightL (l.drop i)` redonne cette même arête pont ⊗ suffixe.
    Pas d'hypothèse `heq` (pas de jonction à aligner, le suffixe est vide). La preuve du cycle
    (`isCycle E c`) est déjà couverte par `cycle_from_repeated` (valide pour `j+1 = l.length`). -/
lemma path_shorten_weight_last {V : Type*} [DecidableEq V] (E : EdgeSet V) (l : List V)
    (i j : ℕ) (hi : i < l.length) (hj : j < l.length) (hij : i < j) (hj1 : j + 1 = l.length) :
    walkWeightL E l =
      walkWeightL E (l.take (i+1)) * walkWeightL E ((l.drop i).take (j - i + 1)) := by
  have hi1 : i + 1 < l.length := by omega
  -- c = (l.drop i).take (j-i+1) = l.drop i  (car (l.drop i).length = l.length - i = j - i + 1)
  have hc : (l.drop i).take (j - i + 1) = l.drop i := by
    have hlen : (l.drop i).length = j - i + 1 := by rw [List.length_drop]; omega
    rw [← hlen, List.take_length]
  -- découpe l = walkWeightL(take(i+1)) ⊗ E.weight(l[i], l[i+1]) ⊗ walkWeightL(drop(i+1))
  have htd := walkWeightL_take_drop E l (i+1) (by omega) hi1
  -- walkWeightL(l.drop i) = E.weight(l[i], l[i+1]) ⊗ walkWeightL(drop(i+1))
  have hdi : l.drop i = l.get ⟨i, hi⟩ :: l.drop (i+1) := List.drop_eq_getElem_cons hi
  have hdi1 : l.drop (i+1) = l.get ⟨i+1, hi1⟩ :: l.drop (i+2) := List.drop_eq_getElem_cons hi1
  have h2 : walkWeightL E (l.drop i) =
      E.weight (l.get ⟨i, hi⟩, l.get ⟨i+1, hi1⟩) * walkWeightL E (l.drop (i+1)) := by
    conv_lhs => rw [hdi, hdi1, walkWeightL_cons_cons, ← hdi1]
  -- assemblage : hc ramène c à l.drop i, h2 déplie l.drop i, htd déplie l, puis alignement Fin
  rw [hc, h2, htd]
  simp only [Nat.add_sub_cancel]
  rw [get_fin_irrel l i _ hi]
  ac_rfl

/-- Une marche de `E` : toute paire consécutive de `l` est une arête de `E`. Forme par-index
    (miroir de `isChain_iff_forall_get`) ; c'est exactement l'hypothèse `hwalk` de
    `cycle_from_repeated`, nommée pour la Direction A. -/
def IsWalk {V : Type*} [DecidableEq V] (E : EdgeSet V) (l : List V) : Prop :=
  ∀ (i : ℕ) (hi : i + 1 < l.length),
    (l.get ⟨i, Nat.lt_of_succ_lt hi⟩, l.get ⟨i + 1, hi⟩) ∈ E.edges

/-- `IsWalk` coïncide avec `List.IsChain` sur la relation d'arête — pont vers l'API
    `List.IsChain` (déjà utilisée par `isCycle_iff_chain`/`cycle_from_repeated`). -/
lemma IsWalk_iff_isChain {V : Type*} [DecidableEq V] (E : EdgeSet V) (l : List V) :
    IsWalk E l ↔ l.IsChain (fun u v => (u, v) ∈ E.edges) := by
  unfold IsWalk
  rw [isChain_iff_forall_get]

/-- **Direction A pièce 3 (théorème opérationnel)** : pour une marche `l` de `E` avec un sommet
    répété `l[i] = l[j]` (`i < j`, cas non-dégénéré `j+1 < l.length`), retirer le cycle
    `c = (l.drop i).take (j-i+1)` (les sommets `l[i..j]`) donne un chemin raccourci
    `l' = l.take (i+1) ++ l.drop (j+1)` tel que (a) `c` est un cycle de `E` (`isCycle`),
    (b) `walkWeightL l = walkWeightL l' * walkWeightL c` (poids décomposé), (c) `l'` est encore
    une marche de `E`. La jonction `l[i]→l[j+1]` de `l'` coïncide avec l'arête `l[j]→l[j+1]`
    de `l` (par `heq`), donc est dans `E.edges`. (c) se prouve via `List.IsChain.append`
    (préfixe `take(i+1)` + suffixe `drop(j+1)` sont des sous-chaînes de `l`, jonction `R(l[i],l[j+1])`
    = `R(l[j],l[j+1])` ∈ E). C'est le raccourcissement par retrait de cycle qui, itéré via
    pigeonhole, donne la borne `d_k(v) ≥ d_n(v) − (n−k)·μ*` de Karp. -/
theorem path_shorten_by_cycle_removal {V : Type*} [DecidableEq V] (E : EdgeSet V) (l : List V)
    (i j : ℕ) (hi : i < l.length) (hj : j < l.length) (hij : i < j) (hj1 : j + 1 < l.length)
    (heq : l.get ⟨i, hi⟩ = l.get ⟨j, hj⟩) (hwalk : IsWalk E l) :
    isCycle E ((l.drop i).take (j - i + 1)) ∧
      walkWeightL E l = walkWeightL E (l.take (i+1) ++ l.drop (j+1)) * walkWeightL E ((l.drop i).take (j - i + 1)) ∧
      IsWalk E (l.take (i+1) ++ l.drop (j+1)) := by
  have hi1 : i + 1 < l.length := by omega
  have hjp1 : j + 1 < l.length := hj1
  refine ⟨?_, ?_, ?_⟩
  · -- (a) c est un cycle (pièce 2, déjà prouvée)
    exact cycle_from_repeated E l i j hi hj hij heq hwalk
  · -- (b) identité de poids (path_shorten_weight)
    exact path_shorten_weight E l i j hi hj hij hj1 heq
  · -- (c) l' est encore une marche, via IsChain.append (préfixe + suffixe + jonction)
    rw [IsWalk_iff_isChain]
    let R := fun (u v : V) => (u, v) ∈ E.edges
    have hchain0 : l.IsChain R := (IsWalk_iff_isChain E l).mp hwalk
    have hprefix : (l.take (i+1)).IsChain R := by
      have hsplit : l = l.take (i+1) ++ l.drop (i+1) := (List.take_append_drop (i+1) l).symm
      rw [hsplit] at hchain0; exact hchain0.left_of_append
    have hchain1 : l.IsChain R := (IsWalk_iff_isChain E l).mp hwalk
    have hsuffix : (l.drop (j+1)).IsChain R := by
      have hsplit : l = l.take (j+1) ++ l.drop (j+1) := (List.take_append_drop (j+1) l).symm
      rw [hsplit] at hchain1; exact hchain1.right_of_append
    -- jonction : (take(i+1)).getLast? = some l[i], (drop(j+1)).head? = some l[j+1]
    have hlp : (l.take (i+1)).getLast? = some (l.get ⟨i, hi⟩) := by
      simp only [List.getLast?_eq_getElem?, List.getElem?_take, List.length_take,
                 min_eq_left (le_of_lt hi1), List.get_eq_getElem]
      split_ifs <;> simp_all
    have hhp : (l.drop (j+1)).head? = some (l.get ⟨j+1, hjp1⟩) := by
      simp only [List.head?_eq_getElem?, List.getElem?_drop, List.get_eq_getElem, Nat.add_zero]
      simp [hjp1]
    apply List.IsChain.append hprefix hsuffix
    rw [hlp, hhp]
    intro x hx y hy
    -- `x ∈ some a` ↔ `a = x` (sans réduire `l.get` en getElem : on garde la forme Fin-get pour `rw [heq]`)
    simp only [Option.mem_def, Option.some.injEq] at hx hy
    subst hx; subst hy
    -- but : R(l[i], l[j+1]) ; rw [heq] → R(l[j], l[j+1]) ; arête j de l ∈ E (via hchain)
    rw [heq]
    have hedge := (isChain_iff_forall_get l R).mp hchain0 j hjp1
    have hfinj : l.get ⟨j, hj⟩ = l.get ⟨j, Nat.lt_of_succ_lt hjp1⟩ := get_fin_irrel l j hj (Nat.lt_of_succ_lt hjp1)
    rw [hfinj]; exact hedge

/-! ### Pont `walkWeight` (monde `Fin`) ↔ `walkWeightL` (monde `List`)

    `karp_d_path_weight` exprime `karp_d` comme un ⊕-sup sur `f : Fin (k+1) → V` pondéré par
    `walkWeight E k f` (monde `Fin`), tandis que le pigeonhole `exists_repeated_of_length_gt_card`
    et l'extraction `cycle_from_repeated` opèrent sur `List V` (monde `List`). Le pont
    `walkWeight E k f = walkWeightL E (List.ofFn f)` (longueur `k+1`) permet d'aller-retour
    entre les deux mondes : un chemin-vecteur `f` ↔ la liste de ses sommets `ofFn f`. La
    réciproque (`List.ofFn (List.get l) = l`, `ofFn_get`) referme la boucle côté `List → Fin`. --/

/-- Pont de poids : un chemin-vecteur `f : Fin (k+1) → V` et la liste de ses sommets
    `List.ofFn f` (longueur `k+1`) ont même poids max-plus ⊗. Preuve par **induction sur `k`**
    (`f` est auto-généralisé car `f : Fin (k+1) → V` dépend de `k` — `induction k` suffit, et
    `generalizing f` serait rejeté) via `List.ofFn_succ` (expose le 1er sommet) + `walkWeight_cons`
    (détache la 1ʳᵉ arête côté `Fin`) + `walkWeightL_cons_cons`
    (détache la 1ʳᵉ arête côté `List`). Évide la couture `Fin`/`List` D3 en décomposant par
    `cons` plutôt qu'en comparant `Fin ((ofFn f).length-1)` à `Fin k` (non-defeq). -/
lemma walkWeight_eq_walkWeightL {V : Type*} [Fintype V] [DecidableEq V] (E : EdgeSet V) (k : ℕ)
    (f : Fin (k+1) → V) :
    walkWeight E k f = walkWeightL E (List.ofFn f) := by
  induction k with
  | zero =>
    -- f : Fin 1 → V ; ofFn f = [f 0] (singleton) ; walkWeight E 0 f = ∏_{Fin 0} = 1 ;
    -- walkWeightL E [f 0] = 1 (motif singleton).
    rw [List.ofFn_succ, List.ofFn_zero]
    simp [walkWeight, walkWeightL]
  | succ k ih =>
    -- f : Fin (k+2) → V ; g := fun i : Fin (k+1) => f i.succ (préfixe décalé).
    -- (1) walkWeight E (k+1) f = E.weight (f 0, f 1) * walkWeight E k g          [walkWeight_cons]
    -- (2) ofFn f = f 0 :: ofFn g ; ofFn g = g 0 :: ofFn (fun i => g i.succ)       [ofFn_succ ×2]
    -- (3) walkWeightL (f 0 :: g 0 :: …) = E.weight (f 0, g 0) * walkWeightL (g 0 :: …)  [cons_cons]
    -- (4) re-fold g 0 :: ofFn (…) = ofFn g                                        [← ofFn_succ]
    -- (5) ih g : walkWeight E k g = walkWeightL E (ofFn g) ; g 0 = f 1.
    rw [walkWeight_cons]
    set g : Fin (k+1) → V := fun i => f i.succ
    rw [show List.ofFn f = f 0 :: List.ofFn g from by rw [List.ofFn_succ]]
    rw [show List.ofFn g = g 0 :: List.ofFn (fun i => g i.succ) from List.ofFn_succ]
    rw [walkWeightL_cons_cons, ← List.ofFn_succ, ih]
    -- Fermé par `rfl` : `g 0` (let `g := fun i => f i.succ`) est defeq `f (Fin.succ 0)` = `f 1`.

/-! ### Phase A-coh — A0 : cohérence `cycleWeight ↔ walkWeightL` (pont pièce-3 → cycleMean)

    La pièce 3 (retrait de cycle) raisonne en `walkWeightL` (monde `List`, récursion `cons`),
    tandis que le RHS de `maxCycleMeanKarp_correct` parle `cycleMean`/`cycleWeight` (monde `Fin`,
    `Finset.prod`). Cette lacune (aucune liaison n'existait — grep vide, relecture 2026-07-30)
    doit être comblée avant l'assemblage Direction A.

    **Résolu (2026-07-31) via la route zip-produit** — cf. `cache/difficultes_plan_ensemble.md`
    entrée [A0]. La voie initiale (« `walkWeight_eq_walkWeightL` + `List.ofFn` ») était bloquée
    pour un `c` de longueur variable : `walkWeight E k f` exige `f : Fin (k+1) → V`, or ramener
    `walkWeightL E c` à `walkWeight E (c.length-1) (c.get)` demanderait `Fin c.length ≡
    Fin (c.length-1+1)` par defeq — or `c.length - 1 + 1` ne se réduit **pas** définitionnellement
    en `c.length` (`Nat.sub` bloqué sur une variable), et `walkWeight` exigerait `Fintype V` (non
    désirable pour un pont indépendant du portage R1). La voie de repli (induction directe sur
    `c` + peel par `Fin.prod_univ_succ`) butait sur une **triple non-defeq** : index
    `Fin (c.length-1)` (`Nat.sub` bloqué sur variable) + corps `dite` opaque (preuves `by omega`
    dépendant de la garde `length ≥ 2`) + matcher `Fin.prod_univ_succ` n'abstrayant pas `?f`
    depuis `bodyL ∘ (finCongr h).symm` (`Function.comp` d'un corps `let`/`have`-lourd).

    **Levée** : prouver chaque côté égal à une forme commune `List`
      `zipWeight E c := ((c.zip c.tail).map (fun p => E.weight (p.1, p.2))).prod`
      • Côté `cycleWeight` (`cycleWeight_eq_zip_prod`) : `Finset.prod_equiv (finCongr hedges_len.symm)`
        — le métavar `?f` absorbe le corps opaque `dite` (truc §13.9), éludant `Fin.prod_univ_succ`.
        Fermeture par `Fin.prod_univ_fun_getElem` (pont getElem, évite le peel `cons`), `get_fin_irrel`
        (aligne les preuves d'index opaques du corps `dite` vs synthétisées getElem) et `show`
        (déplie le `let` du `dite`, uniformise les deux côtés en Fin-get). `DecidableEq V` seul.
      • Côté `walkWeightL` (`walkWeightL_eq_zip_prod`) : induction `List` 3 motifs (`cons` via
        `walkWeightL_cons_cons` + `map_cons`/`prod_cons`), aucune couture `Fin`/`dite`.
    `#print axioms` : baseline `[propext, Classical.choice, Quot.sound]`, **pas de `sorryAx`**.
    L'ancien helper d'épluchage `cycleWeight_cons` (admis) est désormais **obsolète** (la route
    zip n'a pas besoin du peel `cons`) et a été retiré. -/

/-- Côté `cycleWeight` : `cycleWeight E c = zipWeight E c` pour `c.length ≥ 2`, où
    `zipWeight E c := ((c.zip c.tail).map (fun p => E.weight (p.1, p.2))).prod`. Réindexation
    `Fin (c.length-1) ≃ Fin (c.zip c.tail).length` via `finCongr` + `Finset.prod_equiv` (le
    métavar `?f` absorbe le corps opaque `dite` de `cycleWeight`), puis fermeture par
    `Fin.prod_univ_fun_getElem` (pont getElem, évite `Fin.prod_univ_succ` = le mur) et
    `get_fin_irrel` (aligne les preuves d'index opaques du corps `dite` vs synthétisées getElem). -/
lemma cycleWeight_eq_zip_prod {V : Type*} [DecidableEq V] (E : EdgeSet V) (c : List V)
    (h : 2 ≤ c.length) :
    cycleWeight E c =
      ((c.zip c.tail).map (fun p => E.weight (p.1, p.2))).prod := by
  rw [cycleWeight, dif_pos h]
  set edges : List (V × V) := c.zip c.tail with hedges
  have hedges_len : edges.length = c.length - 1 := by
    rw [hedges, List.length_zip, List.length_tail]; omega
  -- RHS (edges.map f).prod  →  ∏ j : Fin edges.length, f edges[j.1]  (pont getElem)
  rw [← Fin.prod_univ_fun_getElem edges (fun p : V × V => E.weight (p.1, p.2))]
  -- Réindexation Fin (c.length-1) ≃ Fin edges.length  (l'opaque G va dans ?f via refine)
  refine Finset.prod_equiv (finCongr hedges_len.symm)
    (fun _ => by simp only [Finset.mem_univ]) ?hfg
  intro i _
  have hiv : i.val < c.length - 1 := i.isLt
  have hiv1 : i.val + 1 < c.length := by omega
  have htlen : c.tail.length = c.length - 1 := by rw [List.length_tail]
  have hivt : i.val < c.tail.length := by rw [htlen]; exact hiv
  -- c.tail[i.val] = c[i.val+1]  (get_tail ramène (c.tail).get⟨i.val,hivt⟩ → c.get⟨i.val+1,h'⟩,
  -- puis get_fin_irrel aligne h' vs la preuve getElem synthétisée de c[i.val+1] = hiv1).
  have htail : c.tail[i.val] = c[i.val + 1] := by
    have hgt := List.get_tail c i.val hivt
    rw [show c.tail[i.val] = (c.tail).get ⟨i.val, hivt⟩ from rfl, hgt]
    apply get_fin_irrel
  -- Développe la RHS : edges[(e i).1] → (c[↑i], c.tail[↑i]) → (c[↑i], c[↑i+1])
  --   getElem_zip + finCongr_apply_coe (e = finCongr (hedges_len.symm) ⇒ coe NON-symm) + htail.
  --   `contextual := true` décharge la garde (↑i < (c.zip c.tail).length) via hedges/hedges_len/hiv.
  --   La LHS (corps `dite` `let i_val := ↑i`) reste intacte (pas de zip/finCongr dedans).
  simp (config := {contextual := true}) only
    [finCongr_apply_coe, hedges, hedges_len, List.getElem_zip, List.length_zip, List.length_tail, htail]
  -- but : (let i_val := ↑i; …; E.weight(c.get⟨i_val,h₃⟩, c.get⟨i_val+1,h₂⟩)) = E.weight(c[↑i], c[↑i+1])
  -- `show` déplie le `let` du corps `dite` ET uniformise les deux côtés en Fin-get (les preuves `_`
  -- sont inférées par defeq : LHS ← h₃/h₂ du corps, RHS ← preuves getElem synthétisées).
  show E.weight (c.get ⟨i.val, _⟩, c.get ⟨i.val + 1, _⟩) =
    E.weight (c.get ⟨i.val, _⟩, c.get ⟨i.val + 1, _⟩)
  rfl

/-- Côté `walkWeightL` : `walkWeightL E c = zipWeight E c` par induction `List` (cons-récursion). -/
lemma walkWeightL_eq_zip_prod {V : Type*} [DecidableEq V] (E : EdgeSet V) : ∀ (c : List V),
    walkWeightL E c = ((c.zip c.tail).map (fun p => E.weight (p.1, p.2))).prod
  | [] => by
    show walkWeightL E [] = (([].zip ([] : List V).tail).map (fun p => E.weight (p.1, p.2))).prod
    rfl
  | [a] => by
    show walkWeightL E [a] =
      ((([a] : List V).zip ([a].tail)).map (fun p => E.weight (p.1, p.2))).prod
    rfl
  | a :: b :: rest => by
    rw [walkWeightL_cons_cons, walkWeightL_eq_zip_prod E (b :: rest)]
    -- LHS : E.weight(a,b) * ((b::rest).zip(b::rest).tail).map f|>.prod
    -- RHS : ((a::b::rest).zip(a::b::rest).tail).map f|>.prod
    rw [show (a :: b :: rest).tail = (b :: rest : List V) from rfl,
        show (a :: b :: rest).zip (b :: rest) = (a, b) :: ((b :: rest).zip rest) from rfl,
        List.map_cons, List.prod_cons,
        show (b :: rest).zip rest = (b :: rest).zip ((b :: rest).tail) from rfl]

/-- **A0** : sur un cycle `c` de `E`, le poids `cycleWeight E c` (`Finset.prod` sur `Fin (c.length-1)`
    des arêtes consécutives, monde `Fin`) coïncide avec `walkWeightL E c` (⊗-produit par récursion
    `cons`, monde `List`). Pont entre le langage de la pièce 3 (`walkWeightL`) et celui de
    `maxCycleMeanKarp_correct`/`cycleMean` (`cycleWeight`).

    Preuve : transitivité via la forme commune `zipWeight`
    (`cycleWeight_eq_zip_prod` + `walkWeightL_eq_zip_prod` ci-dessus). Sorry-free
    (`#print axioms` : `[propext, Classical.choice, Quot.sound]`, pas de `sorryAx`).
    Détail : `cache/difficultes_plan_ensemble.md` entrée [A0]. -/
lemma cycleWeight_eq_walkWeightL {V : Type*} [DecidableEq V] (E : EdgeSet V) (c : List V)
    (hc : isCycle E c) :
    cycleWeight E c = walkWeightL E c :=
  (cycleWeight_eq_zip_prod E c hc.1).trans (walkWeightL_eq_zip_prod E c).symm

/-! ## Phase A3 (Voie 5) — potentiel-excess `G_μ_fin` en ℝ pur via `toInt`

    Dérisquée dans `A3_scratch.lean` (sorry-free, 2026-07-31) puis portée ici. Voie 5
    (2 couches) : (1) cœur A3 — potentiel `G_μ_fin : ℝ` via `toInt` (rfl-clean sur
    `ofInt`), additivité close par `ring` (identité polynomiale ℝ pure, plus de WithBot) ;
    (2) couche finale WithBot (hors A3, réservée à `maxCycleMeanKarp_le`) — `toRealBot`
    préserve ⊥ (`negInf → ⊥`) et `toRealBot_mul` en fait un ⊗-morphisme `Z_max → WithBot ℝ`.
    Miroir de `cycleMean` (L650) : `WithBot.some (((cycleWeight).toInt : ℝ) / …)` — cœur
    `.toInt` ℝ, enveloppe `some` au bord. La couture WithBot que cette voie contourne
    (`ring` aveugle à `WithBot.some`) est documentée dans `cache/difficultes_plan_ensemble.md`.
    Leçons moteur Lean (rw auto-rfl strict, `simp only` ferme les buts rfl, `ring` aveugle
    à `some`) : cf. `lean4-proof-gotchas` (mémoire persistante). -/

section G_mu_fin

variable {V : Type*} [DecidableEq V] (E : EdgeSet V)

/-- Potentiel-excess `G_μ_fin(l) = toInt(walkWeightL E l) − (|l|−1)·μ : ℝ` (Voie 5).
    Edge-count = `l.length - 1` (nombre d'arêtes). Sur un chemin fini
    (`walkWeightL E l = ofInt w`), `toInt (ofInt w) = w` (rfl), donc `G_μ_fin` coïncide
    avec le poids réel `w − (|l|−1)·μ`. La singularité `toInt negInf = 0` n'est jamais
    atteinte dans le cas fini utilisé par A5 (chemin argmax de poids fini). -/
def G_μ_fin (μ : ℝ) (l : List V) : ℝ :=
  ((walkWeightL E l).toInt : ℝ) - ((l.length - 1 : ℕ) : ℝ) * μ

/-- Réduction de `G_μ_fin` dans le cas fini `walkWeightL E l = ofInt w` : après `rw [hw]`,
    `(ofInt w).toInt` iota-réduit en `w` via le lemme simp `toInt_ofInt` (rfl-prouvé). -/
lemma G_μ_fin_of_ofInt (μ : ℝ) (l : List V) (w : ℤ) (hw : walkWeightL E l = ofInt w) :
    G_μ_fin E μ l = ((w : ℝ) - ((l.length - 1 : ℕ) : ℝ) * μ) := by
  show ((walkWeightL E l).toInt : ℝ) - ((l.length - 1 : ℕ) : ℝ) * μ =
       ((w : ℝ) - ((l.length - 1 : ℕ) : ℝ) * μ)
  rw [hw, toInt_ofInt]

end G_mu_fin

/-! ### Couche finale WithBot (hors A3 — réservée à `maxCycleMeanKarp_le`)
    `toRealBot` préserve ⊥ (`negInf → ⊥`, contrairement à `toInt → 0`) ; `toRealBot_mul`
    en fait un ⊗-morphisme `Z_max → WithBot ℝ`. Enveloppe mince qui remonte `G_μ_fin` ℝ
    en `WithBot ℝ` uniquement au théorème final (A5/`maxCycleMeanKarp_le`), pas dans A3. -/

/-- Injection propre Z_max → WithBot ℝ (negInf → ⊥, ofInt n → some n). Préserve ⊥
    (contrairement à `toInt` qui envoie `negInf → 0`). -/
def toRealBot (z : Z_max) : WithBot ℝ :=
  match z with
  | Z_max.negInf => ⊥
  | Z_max.ofInt n => some (n : ℝ)

/-- `toRealBot` est un ⊗-morphisme `Z_max → WithBot ℝ` : `toRealBot (a * b) = toRealBot a + toRealBot b`
    (⊗ = `*` côté `Z_max`, `+` côté `WithBot ℝ`). Preuve par cas sur les deux arguments ;
    cas `ofInt`/`ofInt` clos par `push_cast; rfl` (`some ((a+b:ℤ):ℝ) = some ((a:ℝ)+(b:ℝ))`
    est defeq via l'instance `WithBot` `Add` `Option.lift₂`). -/
lemma toRealBot_mul (a b : Z_max) : toRealBot (a * b) = toRealBot a + toRealBot b := by
  cases a with
  | negInf => rfl
  | ofInt a =>
    cases b with
    | negInf => rfl
    | ofInt b =>
      show some ((a + b : ℤ) : ℝ) = some ((a : ℝ) + (b : ℝ))
      push_cast
      rfl

/-! ## A4 — pont ℤ/ℝ + extraction de cycle SIMPLE par premier-repeat (route α)

    A4 = le pont ℤ/ℝ (`cycleMean E c ≤ μ ↔ G_μ_fin E μ c ≤ 0`) + la borne cycle-mean ≤ μ*
    (Direction A, unilateral `maxCycleMeanKarp_le`). Route α (vs β, reportée à C1) : μ* = max
    des moyennes de cycles SIMPLES (B-att `Finset.sup`, réel concret, PAS de BddAbove) + on
    extrait un cycle SIMPLE par premier-repeat (pigeonhole raffiné). La borne `cycleMean E c ≤ μ*`
    devient `Finset.le_sup` (membre ≤ sup d'un Finset — trivial, PAS de BddAbove, PAS de
    décomposition closed-walk). La D2/D4 de [K] (BddAbove) est ainsi résolue pour A4 ; la
    décomposition closed-walk (route β) est reportée à C1 (égalité μ* = sSup sur tous les
    cycles, `isCycle` n'exige pas la simplicité). Dérisqué dans `A4_scratch.lean` (archive) ;
    difficultés documentées cache [L] (A4), [M] (Nodup-drop), gotchas #5/#6. -/

section A4

variable {V : Type*} [DecidableEq V] (E : EdgeSet V)

/-! ### A4-1 : pont ℤ/ℝ `cycleMean E c ≤ μ ↔ G_μ_fin E μ c ≤ 0` -/

/-- Pont ℤ/ℝ : pour un cycle `c`, sa moyenne (réelle, `WithBot ℝ`) est ≤ μ ssi le
    potentiel-excess `G_μ_fin E μ c = toInt(walkWeightL E c) − (|c|−1)·μ` est ≤ 0.
    Tient même si `cycleWeight E c = ⊥` (`toInt ⊥ = 0` ⟹ `some 0 ≤ μ ↔ 0 ≤ μ` et
    `−(L−1)μ ≤ 0 ↔ 0 ≤ μ`, équivalents) — pas de `h_edge` requis pour le pont.
    Décomposition : A0 (`cycleWeight = walkWeightL`) → `dif_pos` (cycleMean est un `dite`) →
    `coe_le_coe` (WithBot) → `div_le_iff₀` → `linarith` (`hcd` ponte les castes `↑c.length-1`
    vs `↑(c.length-1)` via `Nat.cast_sub`). Sorry-free, `#print axioms` propre. -/
lemma G_μ_fin_cycle_nonpos (c : List V) (hc : isCycle E c) (μ : ℝ) :
    cycleMean E c ≤ (μ : WithBot ℝ) ↔ G_μ_fin E μ c ≤ 0 := by
  have hlen : 2 ≤ c.length := hc.1
  have h1le : 1 ≤ c.length := le_trans (by decide) hlen
  have h1lt : 1 < c.length := by omega
  have hpos : (0 : ℝ) < ((c.length : ℕ) : ℝ) - 1 := by
    have h1 : (1 : ℝ) < ((c.length : ℕ) : ℝ) := by exact_mod_cast h1lt
    linarith
  -- `G_μ_fin` utilise `↑(c.length-1)` ; le pont (dépliage cycleMean) produit `↑c.length-1`.
  -- `hcd` relie les deux castes (linarith).
  have hcd : μ * (((c.length : ℕ) : ℝ) - 1) = ((c.length - 1 : ℕ) : ℝ) * μ := by
    rw [Nat.cast_sub h1le]; ring
  -- dépliage cycleMean (dite) : `simp only [cycleMean, dif_pos hlen]` produit
  -- `↑(((cycleWeight).toInt)/ (↑c.length - 1))` (forme normalisée coe, confirmée au build ;
  -- `some_eq_coe` est inutile — `dif_pos hlen` produit déjà la forme coe).
  simp only [cycleMean, dif_pos hlen]
  rw [cycleWeight_eq_walkWeightL E c hc, WithBot.coe_le_coe, div_le_iff₀ hpos]
  -- but : ((walkWeightL E c).toInt : ℝ) ≤ μ * (↑c.length-1)  ↔  G_μ_fin E μ c ≤ 0
  -- G_μ_fin E μ c defeq ((walkWeightL E c).toInt : ℝ) − ↑(c.length-1)*μ ; `hcd` ponte (linarith).
  show ((walkWeightL E c).toInt : ℝ) ≤ μ * (((c.length : ℕ) : ℝ) - 1) ↔
       ((walkWeightL E c).toInt : ℝ) - ((c.length - 1 : ℕ) : ℝ) * μ ≤ 0
  constructor
  · intro h; linarith
  · intro h; linarith

/-! ### A4-2 : extraction de cycle SIMPLE par premier-repeat (route α) -/

/-- Premier-repeat (pigeonhole raffiné). Une marche `l` plus longue que `|V|` contient un
    sommet répété `l[i] = l[j]` (`i < j`) tel que le préfixe `l.take j` est Nodup
    (`j` = premier indice fermant une répétition). Le segment `l[i..j]` est alors un cycle
    SIMPLE : `l[i..j-1]` est un sous-segment du préfixe Nodup `l.take j`. C'est le raffinement
    qui rend la borne triviale (`Finset.le_sup`).

    Preuve : `j` = longueur du préfixe Nodup maximal = `(Nat.find (¬ (l.take ·).Nodup)) − 1`.
    `Nat.find_min` donne `(l.take j).Nodup` directement ; `¬ (l.take (j+1)).Nodup` force le
    nouveau sommet `l[j]` à dupliquer un sommet du préfixe (sinon le préfixe s'étendrait).
    Sorry-free, `#print axioms` propre. -/
lemma exists_first_repeat [Fintype V] (l : List V) (h : Fintype.card V < l.length) :
    ∃ (i j : ℕ) (hi : i < l.length) (hj : j < l.length),
      i < j ∧ l.get ⟨i, hi⟩ = l.get ⟨j, hj⟩ ∧ (l.take j).Nodup := by
  have hnodup : ¬ l.Nodup := by
    intro hnd
    have := List.Nodup.length_le_card hnd
    omega
  -- P k := ¬ (l.take k).Nodup ; j = (Nat.find P) − 1 = longueur du préfixe Nodup maximal
  haveI hPdec : DecidablePred (fun k : ℕ => ¬ (l.take k).Nodup) :=
    fun k => inferInstanceAs (Decidable ¬(l.take k).Nodup)
  have hPex : ∃ k, ¬ (l.take k).Nodup := ⟨l.length, by rw [List.take_length]; exact hnodup⟩
  obtain ⟨k, hkP, hkmin⟩ := Nat.findX hPex
  -- k ≥ 1 (take 0 = [] est Nodup, contredit hkP si k = 0)
  have hk1 : 1 ≤ k := by
    by_contra hkc
    have h0 : k = 0 := by omega
    subst h0
    exact hkP (by simp [List.take_zero])
  -- k ≤ l.length (le préfixe plein l.take l.length = l n'est pas Nodup)
  have hPlen : ¬ (l.take l.length).Nodup := by rw [List.take_length]; exact hnodup
  have hklenn : k ≤ l.length := by
    by_contra hgt
    exact (hkmin l.length (by omega)) hPlen
  set j : ℕ := k - 1
  have hjk : j + 1 = k := by omega
  have hj : j < l.length := by omega
  have hjlen : (l.take j).length = j := by
    rw [List.length_take, min_eq_left (le_of_lt hj)]
  have hj1len : (l.take (j + 1)).length = j + 1 := by
    rw [List.length_take, min_eq_left (Nat.succ_le_of_lt hj)]
  -- (l.take j).Nodup (directement depuis Nat.find_min : ∀ m < k, (l.take m).Nodup)
  have hjnodup : (l.take j).Nodup := not_not.mp (hkmin j (by omega))
  -- le nouveau sommet l[j] (ajouté dans l.take k = l.take (j+1)) duplique un sommet du préfixe :
  -- ¬ (l.take (j+1)).Nodup ∧ (l.take j).Nodup ⟹ ∃ a < j, l[a] = l[j]
  have hrep : ∃ (i : ℕ) (hi : i < l.length), i < j ∧ l.get ⟨i, hi⟩ = l.get ⟨j, hj⟩ := by
    have hkj : k = j + 1 := by omega
    rw [hkj] at hkP
    rw [List.nodup_iff_getElem?_ne_getElem?] at hkP
    push_neg at hkP
    obtain ⟨a, b, hab, hbLk, heq⟩ := hkP
    rw [hj1len] at hbLk
    rw [List.nodup_iff_getElem?_ne_getElem?, hjlen] at hjnodup
    -- b = j : si b < j, alors a < b < j contredirait (l.take j).Nodup
    have hbj : b = j := by
      by_contra hne
      have hbj' : b < j := by omega
      have ha' : a < j := lt_trans hab hbj'
      have hmem : (l.take j)[a]? ≠ (l.take j)[b]? := hjnodup a b hab hbj'
      rw [List.getElem?_take_of_lt ha', List.getElem?_take_of_lt hbj'] at hmem
      rw [List.getElem?_take_of_lt (by omega : a < j + 1),
          List.getElem?_take_of_lt (by omega : b < j + 1)] at heq
      exact hmem heq
    have ha : a < j := by omega
    have haL : a < l.length := lt_trans ha hj
    refine ⟨a, haL, ha, ?_⟩
    have h1 : (l.take (j + 1))[a]? = l[a]? := List.getElem?_take_of_lt (by omega)
    have h2 : (l.take (j + 1))[j]? = l[j]? := List.getElem?_take_of_lt (by omega)
    rw [hbj] at heq
    rw [h1, h2] at heq
    rw [List.getElem?_eq_getElem haL, List.getElem?_eq_getElem hj] at heq
    exact Option.some.inj heq
  obtain ⟨i, hi, hij, heq⟩ := hrep
  exact ⟨i, j, hi, hj, hij, heq, hjnodup⟩

/-- Cycle simple = cycle fermé `isCycle` dont les sommets (hors retour) sont distincts. -/
def isSimpleCycle (c : List V) : Prop :=
  isCycle E c ∧ (c.take (c.length - 1)).Nodup

/-- Depuis un premier-repeat (i,j, l[i]=l[j], (l.take j).Nodup) + marche, le cycle extrait
    `c = (l.drop i).take (j-i+1)` (= segment l[i..j]) est SIMPLE : `isCycle` (pièce 2
    `cycle_from_repeated`) + Nodup du segment `l[i..j-1]` (sous-segment du préfixe Nodup
    `l.take j`). C'est le linchpin de la route α : borne `cycleMean E c ≤ μ*` = `Finset.le_sup`.
    Le dernier pas (Nodup préservé par `drop`/sublist) est CLOS (2026-08-01, analyse
    approfondie) : `drop i` ⟹ sublist (`List.drop_sublist`), Nodup préservé par
    `Nodup.sublist` (API canonique, Infix.lean:174/180 ; cf. `Nodup.of_append_left`
    Nodup.lean:154). La "difficulté D3/D5" initialement documentée (cache [M], gotcha #6)
    était un D5 auto-infligé : le grep cherchait `Sublist.nodup` (mauvais namespace) — le
    vrai lemme est `Nodup.sublist` (namespace `Nodup`, pas `Sublist`). Aucune recherche
    externe nécessaire : l'API est canonique et documentée dans Mathlib. -/
lemma simple_cycle_of_first_repeat (l : List V) (hwalk : IsWalk E l)
    (i j : ℕ) (hi : i < l.length) (hj : j < l.length) (hij : i < j)
    (heq : l.get ⟨i, hi⟩ = l.get ⟨j, hj⟩) (hjnodup : (l.take j).Nodup) :
    isSimpleCycle E ((l.drop i).take (j - i + 1)) := by
  let c := (l.drop i).take (j - i + 1)
  have hcyc : isCycle E c := cycle_from_repeated E l i j hi hj hij heq hwalk
  refine ⟨hcyc, ?_⟩
  -- c.take (c.length - 1) = (l.take j).drop i  (= segment l[i..j-1])
  have hle : (j - i + 1 : ℕ) ≤ l.length - i := by omega
  have hclen : c.length = j - i + 1 := by
    simp only [c, List.length_take, List.length_drop, min_eq_left hle]
  have hcl1 : c.length - 1 = j - i := by rw [hclen]; omega
  have hji : i + (j - i) = j := by omega
  have hctk : c.take (c.length - 1) = (l.take j).drop i := by
    rw [show c = (l.drop i).take (j - i + 1) from rfl, hcl1, List.take_take,
      min_eq_left (by omega), List.take_drop, hji]
  rw [hctk]
  -- (l.take j).drop i est Nodup : `drop i` ⟹ sublist (`List.drop_sublist`), Nodup préservé
  -- par `Nodup.sublist` (Infix.lean:174/180). `hjnodup.sublist` = `Nodup.sublist` en dot
  -- notation (type-driven, insère hjnodup au param `hn`, cf. `hn.sublist h.sublist` L174).
  -- Analyse approfondie 2026-08-01 : la "difficulté D3/D5" (cache [M], gotcha #6) était un
  -- D5 auto-infligé — grep `Sublist.nodup` = mauvais namespace ; le vrai lemme est `Nodup.sublist`.
  exact hjnodup.sublist (List.drop_sublist i (l.take j))

/-! ### A4-3 : stub B-att `maxCycleMeanSimple` (finitude sorry'd, API Finset vérifiée) -/

/-- Sous-type des cycles simples de `E`. `abbrev` (reducible) pour que la synthèse
    d'instance `Fintype (SimpleCycle E)` déplie vers le sous-type. L'instance `Fintype`
    (B-att : `V` Fintype ⟹ un cycle simple a `c.length ≤ |V|+1` ⟹ l'ensemble des cycles
    simples est fini) est CLOS (2026-08-01, route L : borne via `List.Nodup.length_le_card`
    + `Set.Finite.subset (List.finite_length_le)` + `Set.Finite.fintype`, noncomputable,
    `#print axioms` = `[propext, Classical.choice, Quot.sound]`, pas de `sorryAx`).
    Dérisqué dans `A4_batt_scratch.lean`. -/
abbrev SimpleCycle (E : EdgeSet V) := { c : List V // isSimpleCycle E c }

/-- B-att : `Fintype (SimpleCycle E)`. **Route L** (longueur-bornée + subset) :
    (1) borne `isSimpleCycle E c → c.length ≤ Fintype.card V + 1` — le préfixe
    `c.take (c.length-1)` est Nodup (`isSimpleCycle`), de longueur `c.length-1`
    (`min_eq_left (Nat.sub_le …)`), donc `c.length-1 ≤ |V|` par `List.Nodup.length_le_card` ;
    (2) `{c | isSimpleCycle E c} ⊆ {c | c.length ≤ |V|+1}`, ce dernier fini
    (`List.finite_length_le V (Fintype.card V + 1)`, `[Finite V]` depuis `[Fintype V]`) ;
    (3) `Set.Finite.subset` ⟹ fini, `Set.Finite.fintype` (noncomputable, choice) ⟹ `Fintype`.
    `exact hfin.fintype` unifie `Fintype ↥{c | isSimpleCycle E c}` avec `Fintype (SimpleCycle E)`
    (abbrev reducible + `Set.mem_setOf_eq` defeq). **Route S** écartée (injection « épine »
    `c ↦ c.take (c.length-1)` dans `{l // l.Nodup}` + `Fintype.ofInjective`) : aussi
    noncomputable + exige l'injectivité (couture D3). Rend `cycleMean_le_max` `sorryAx`-free
    (lève l'héritage `sorryAx` du stub). Dérisqué dans `A4_batt_scratch.lean` (build OK,
    `#print axioms` = `[propext, Classical.choice, Quot.sound]`). -/
noncomputable instance simpleCycleFintype [Fintype V] : Fintype (SimpleCycle E) := by
  have hbound : ∀ c : List V, isSimpleCycle E c → c.length ≤ Fintype.card V + 1 := by
    intro c h
    have hnd : (c.take (c.length - 1)).Nodup := h.2
    have htklen : (c.take (c.length - 1)).length = c.length - 1 := by
      rw [List.length_take, min_eq_left (Nat.sub_le c.length 1)]
    have hcard := List.Nodup.length_le_card hnd
    rw [htklen] at hcard
    omega
  have hsub : { c : List V | isSimpleCycle E c } ⊆
      { c : List V | c.length ≤ Fintype.card V + 1 } := by
    intro c h
    exact hbound c h
  have hfin : ({ c : List V | isSimpleCycle E c } : Set (List V)).Finite :=
    Set.Finite.subset (List.finite_length_le V (Fintype.card V + 1)) hsub
  exact hfin.fintype

/-- μ* = max des moyennes de cycles simples (atteint : `Finset.sup` sur un Finset, réel concret).
    Pas de `BddAbove` (contrairement au `sSup` abstrait) : le sup d'un Finset est toujours un
    élément / borne. L'annotation `: WithBot ℝ` fixe le porteur `OrderBot` (évite le metavar
    `OrderBot ?m`). -/
noncomputable def maxCycleMeanSimple [Fintype V] : WithBot ℝ :=
  (Finset.univ : Finset (SimpleCycle E)).sup
    (fun (c : SimpleCycle E) => (cycleMean E (↑c) : WithBot ℝ))

/-- Borne membre ≤ sup : pour un cycle simple `c`, `cycleMean E c ≤ maxCycleMeanSimple E`
    via `Finset.le_sup` (membre du Finset ≤ son sup). Trivial — PAS de BddAbove, PAS de
    décomposition closed-walk. C'est l'avantage de la route α (cycle simple extrait). -/
lemma cycleMean_le_max [Fintype V] {c : List V} (hsc : isSimpleCycle E c) :
    cycleMean E c ≤ maxCycleMeanSimple E := by
  have hmem : (⟨c, hsc⟩ : SimpleCycle E) ∈ (Finset.univ : Finset (SimpleCycle E)) :=
    Finset.mem_univ _
  -- `f := fun c => (cycleMean E ↑c : WithBot ℝ)` épingle le porteur `α = WithBot ℝ`
  -- (sinon `OrderBot α` reste metavar). `(↑⟨c, hsc⟩) = c` et `(Finset.univ).sup ... = maxCycleMeanSimple E`.
  exact Finset.le_sup (f := fun (c : SimpleCycle E) => (cycleMean E (↑c) : WithBot ℝ)) hmem

end A4

/-! ## A5 — Direction A effective : `maxCycleMeanKarp E ≤ maxCycleMeanSimple E` (route α, retrait unique)

    A5 = la moitié « facile » (≤) du théorème de Karp : la formule Karp ne surestime pas λ* =
    max cycle mean (max sustainable rent). Route α (vs β, reportée à C1) : extraction d'un cycle
    SIMPLE par premier-repeat (un seul retrait, D4 itération **évitée**), borne `cycleMean c* ≤
    maxCycleMeanSimple` = `Finset.le_sup` (trivial, PAS de BddAbove). Assemblage linéaire des
    pièces A0-A4 : argmax path (`exists_path_weight_eq_karp_d`) → `walkWeightL` (= `ofInt n_val`)
    → pigeonhole (`exists_first_repeat`) → cycle SIMPLE (`simple_cycle_of_first_repeat`) →
    additivité (`G_μ_fin_add_of_finite` / `_last`) → pont (`G_μ_fin_cycle_nonpos`) → borne
    (`cycleMean_le_max`) → arithmétique `(d_n−d_k)/(n−k) ≤ μ*`. Hypothèse `h_edge` (poids = ⊥
    hors-arêtes : chemin argmax ⊗-fini ⟹ arêtes ∈ E.edges ⟹ IsWalk), PAS d'`Irreducible` (v ⊥
    trivial, v fini = argmax). Dérisquage navigation LHS : `A5_scratch.lean` (archive). Cf. gotcha
    #8, cache [O], `cache/apprentissages_A5_directionA_route_alpha_2026-08-01.md`. -/

section A5

variable {V : Type*} [DecidableEq V] (E : EdgeSet V)

/-- `ofInt z ≠ (⊥ : Z_max)` (⊥ = negInf ; constructeurs distincts). -/
lemma Z_max.ofInt_ne_bot (z : ℤ) : (Z_max.ofInt z : Z_max) ≠ ⊥ := by
  intro h
  rw [show (⊥ : Z_max) = Z_max.negInf from rfl] at h
  exact Z_max.noConfusion h

/-- **F3** — Décodage de la partie non-bottom : `Z_max ≅ ℤ ∪ {−∞}`, la branche non-bottom
    est exactement `ofInt ℤ`. `z ≠ ⊥ ⟹ ∃ a, z = ofInt a`. Généralisation de la dance
    `by_contra + cases hL : z with` (isole la singularité `Zero Z_max = negInf`). -/
lemma Z_max.exists_ofInt_of_ne_bot (z : Z_max) (hz : z ≠ (⊥ : Z_max)) :
    ∃ a : ℤ, z = Z_max.ofInt a := by
  by_contra hc; push_neg at hc
  cases hL : z with
  | negInf => exact (hz (hL.trans Z_max.zero_eq.symm)).elim
  | ofInt n => exact (hc n hL).elim

/-- **FB-ofInt_le** — `ofInt a ≤ ofInt c ↔ a ≤ c` (décodage ℤ du ≤ Z_max, via
    `toWithBot_le_iff` + `Z_max_toWithBot` + `coe_le_coe` — la dance ×2 dans
    `per_v_ineq`/`excess_recurrence`). -/
lemma Z_max.ofInt_le_iff (a c : ℤ) : (Z_max.ofInt a ≤ Z_max.ofInt c) ↔ a ≤ c := by
  rw [← toWithBot_le_iff (Z_max.ofInt a) (Z_max.ofInt c)]
  simp only [Z_max_toWithBot, WithBot.coe_le_coe]

/-- **K2** : sous `h_edge` (poids = ⊥ hors-arêtes), un chemin de poids ⊗-fini (`walkWeightL E l ≠ ⊥`)
    est une marche `IsWalk E l`. Contraposée : si une arête consécutive `(l[i], l[i+1])` n'est pas
    dans `E.edges`, `h_edge` donne `weight = ⊥` ; ⊥ absorbant pour `*` (= ⊗ = + sur Z_max), donc
    `walkWeightL E l = ⊥` via `walkWeightL_take_drop` (découpe au pont `i+1`, arête pont =
    `(l[i], l[i+1])` = ⊥). -/
lemma walkWeightL_finite_imp_isWalk (h_edge : ∀ (p : V × V), p ∉ E.edges → E.weight p = (0 : Z_max))
    (l : List V) (hw : walkWeightL E l ≠ (0 : Z_max)) : IsWalk E l := by
  by_contra hwalk
  apply hw
  unfold IsWalk at hwalk
  push_neg at hwalk
  obtain ⟨i, hi, hne⟩ := hwalk
  have hw0 : E.weight (l.get ⟨i, Nat.lt_of_succ_lt hi⟩, l.get ⟨i+1, hi⟩) = (0:Z_max) := h_edge _ hne
  have htd := walkWeightL_take_drop E l (i+1) (by omega) hi
  rw [htd, get_fin_eq l (by omega : (i+1) - 1 = i) (Nat.lt_of_succ_lt hi), hw0, Z_max.mul_zero,
      Z_max.zero_mul]

end A5

/-- `(l.take n).get ⟨k, hk⟩ = l.get ⟨k, ?⟩` (forme par-index, miroir de `get_drop_eq`).
    Via `List.get_eq_getElem` + `List.getElem_take` (simp gère l'irrélevance de preuve getElem). -/
lemma get_take_fin {α : Type*} (l : List α) (n k : ℕ) (hk : k < (l.take n).length) :
    (l.take n).get ⟨k, hk⟩ = l.get ⟨k, by have h := hk; rw [List.length_take] at h; omega⟩ := by
  simp [List.get_eq_getElem, List.getElem_take]

/-- **K4-helper** : `karp_d E s k v ≥ walkWeightL E l'` quand `l'` est un chemin de longueur `k+1`
    de `s` à `v`. Témoin pour le `Finset.sup` de `karp_d_path_weight` : on relit `l'` comme un
    chemin-vecteur `g : Fin (k+1) → V` via `List.ofFn_get` + `List.ofFn_congr`, puis `Finset.le_sup`
    sur `g` (dont `g 0 = s`, `g (Fin.last k) = v`). -/
lemma karp_d_ge_walkWeightL {V : Type*} [Fintype V] [DecidableEq V] (E : EdgeSet V) (s : V)
    (k : ℕ) (v : V) (l' : List V) (hl'len : l'.length = k + 1) (hl'0 : 0 < l'.length)
    (hl'k : k < l'.length) (hl's : l'.get ⟨0, hl'0⟩ = s) (hl'v : l'.get ⟨k, hl'k⟩ = v) :
    karp_d E s k v ≥ walkWeightL E l' := by
  rw [karp_d_path_weight E s k v]
  let g : Fin (k+1) → V := fun i => l'.get (Fin.cast (hl'len.symm) i)
  have hog : List.ofFn g = l' := by
    have h := List.ofFn_get l'
    have hcg := List.ofFn_congr hl'len (l'.get)
    exact hcg.symm.trans h
  have hg0 : g 0 = s := by
    have heq : Fin.cast (hl'len.symm) (0 : Fin (k+1)) = ⟨0, hl'0⟩ := Fin.eq_of_val_eq rfl
    show l'.get (Fin.cast (hl'len.symm) (0 : Fin (k+1))) = s
    rw [heq]; exact hl's
  have hglast : g (Fin.last k) = v := by
    have heq : Fin.cast (hl'len.symm) (Fin.last k) = ⟨k, hl'k⟩ := Fin.eq_of_val_eq rfl
    show l'.get (Fin.cast (hl'len.symm) (Fin.last k)) = v
    rw [heq]; exact hl'v
  have hwg : walkWeight E k g = walkWeightL E l' := by
    rw [walkWeight_eq_walkWeightL E k g, hog]
  have hmem : g ∈ (Finset.univ : Finset (Fin (k+1) → V)) := Finset.mem_univ _
  have hle := Finset.le_sup
    (f := fun f => if f 0 = s ∧ f (Fin.last k) = v then walkWeight E k f else (0 : Z_max)) hmem
  dsimp only at hle
  rw [if_pos ⟨hg0, hglast⟩, hwg] at hle
  exact hle

/-- **Additivité G_μ généralisée** : `G_μ_fin E μ l = G_μ_fin E μ l' + G_μ_fin E μ c` quand
    `walkWeightL E l = walkWeightL E l' * walkWeightL E c` (retrait de cycle), `l` de poids fini,
    et arithmétique d'edge-count `(l.length-1) = (l'.length-1) + (c.length-1)`. Unifie les cas
    non-dégénéré (`path_shorten_weight`, déjà couvert par `G_μ_fin_add_of_finite`) et dégénéré
    (`path_shorten_weight_last`, l' = `l.take (i+1)`). -/
lemma G_μ_fin_add_general {V : Type*} [DecidableEq V] (E : EdgeSet V) (μ : ℝ) (l l' c : List V)
    (hw : walkWeightL E l = walkWeightL E l' * walkWeightL E c)
    (hf : walkWeightL E l ≠ (⊥ : Z_max))
    (hedge : (l.length - 1 : ℕ) = (l'.length - 1) + (c.length - 1)) :
    G_μ_fin E μ l = G_μ_fin E μ l' + G_μ_fin E μ c := by
  have hl'f : walkWeightL E l' ≠ (0 : Z_max) := by
    intro h; apply hf; rw [hw, h]; exact Z_max.zero_mul _
  have hcf : walkWeightL E c ≠ (0 : Z_max) := by
    intro h; apply hf; rw [hw, h]; exact Z_max.mul_zero _
  obtain ⟨w', hw'⟩ : ∃ w', walkWeightL E l' = ofInt w' :=
    Z_max.exists_ofInt_of_ne_bot (walkWeightL E l') hl'f
  obtain ⟨wc, hwc⟩ : ∃ wc, walkWeightL E c = ofInt wc :=
    Z_max.exists_ofInt_of_ne_bot (walkWeightL E c) hcf
  have hwl : walkWeightL E l = ofInt (w' + wc) := by rw [hw, hw', hwc]; rfl
  rw [G_μ_fin_of_ofInt E μ l (w' + wc) hwl,
      G_μ_fin_of_ofInt E μ l' w' hw',
      G_μ_fin_of_ofInt E μ c wc hwc, hedge]
  push_cast
  ring

/-- **A5 per-v (queue commune deg/non-deg)** : depuis l'argmax `l` (poids `ofInt n_val`, `n` arêtes),
    le raccourci `l'` (`k` arêtes), le cycle `c` (G_μ ≤ 0), et `karp_d E s k v ≥ walkWeightL E l'`,
    déroule l'inégalité de Karp `(d_n−d_k)/(n−k) ≤ μ*` puis `f k ≤ maxCycleMeanSimple E`.
    `d_k(v) = ofInt k_val ≥ walkWeightL E l' = ofInt w'` (témoin du sup), additivité `G_μ(l) = G_μ(l')+
    G_μ(c)` + `G_μ(c) ≤ 0` ⟹ `G_μ(l) ≤ G_μ(l')` ⟹ `(n_val−w')/(n−k) ≤ μ*`, et `k_val ≥ w'` ⟹
    `(n_val−k_val)/(n−k) ≤ μ*`. Le `match` sur `karp_d E s k v` se réduit par `hkdk`. -/
lemma per_v_ineq {V : Type*} [Fintype V] [DecidableEq V] (E : EdgeSet V) (s v : V)
    (l l' c : List V) (n_val : ℤ) (n k : ℕ) (k_val : ℤ) (μ : ℝ)
    (hμ : (μ : WithBot ℝ) = maxCycleMeanSimple E)
    (hgc : G_μ_fin E μ c ≤ 0)
    (hadd : G_μ_fin E μ l = G_μ_fin E μ l' + G_μ_fin E μ c)
    (hwl : walkWeightL E l = ofInt n_val)
    (hww : walkWeightL E l = walkWeightL E l' * walkWeightL E c)
    (hlen : l.length = n + 1) (hl'len : l'.length = k + 1)
    (hkdk : karp_d E s k v = ofInt k_val)
    (hge : karp_d E s k v ≥ walkWeightL E l')
    (hkltn : k < n) :
    (match karp_d E s k v with
     | Z_max.ofInt k_val' => WithBot.some (((n_val - k_val') : ℝ) / ((n - k) : ℝ))
     | _ => (⊥ : WithBot ℝ)) ≤ maxCycleMeanSimple E := by
  -- (a) walkWeightL E l' est fini (⊥ absorbant depuis hww + hwl) → ofInt w'
  have hl'ne : walkWeightL E l' ≠ (0 : Z_max) := by
    intro h
    apply Z_max.ofInt_ne_bot n_val
    rw [← hwl, hww, h]; exact Z_max.zero_mul _
  obtain ⟨w', hw'⟩ : ∃ w', walkWeightL E l' = ofInt w' :=
    Z_max.exists_ofInt_of_ne_bot (walkWeightL E l') hl'ne
  -- (b) d_k(v) = ofInt k_val ≥ ofInt w' (témoin) → w' ≤ k_val
  have hkw : (w' : ℤ) ≤ k_val := by
    have hh : ofInt w' ≤ ofInt k_val := by
      have := hge; rw [hkdk, hw'] at this; exact this
    exact (Z_max.ofInt_le_iff w' k_val).mp hh
  -- (c) G_μ(l) = n_val − n·μ , G_μ(l') = w' − k·μ
  have hlen1 : (l.length - 1 : ℕ) = n := by omega
  have hl'lenk : (l'.length - 1 : ℕ) = k := by omega
  have hGl : G_μ_fin E μ l = ((n_val : ℝ) - (n : ℝ) * μ) := by
    rw [G_μ_fin_of_ofInt E μ l n_val hwl, hlen1]
  have hGl' : G_μ_fin E μ l' = ((w' : ℝ) - (k : ℝ) * μ) := by
    rw [G_μ_fin_of_ofInt E μ l' w' hw', hl'lenk]
  -- (d) G_μ(c) ≤ 0 ⟹ G_μ(l) ≤ G_μ(l') ⟹ (n_val − w')/(n−k) ≤ μ
  have hle : G_μ_fin E μ l ≤ G_μ_fin E μ l' := by rw [hadd]; linarith
  have h1 : (n_val - w' : ℝ) ≤ (n - k) * μ := by
    have := hle; rw [hGl, hGl'] at this
    linarith [show (n - k : ℝ) * μ = (n : ℝ) * μ - (k : ℝ) * μ from by ring]
  have hkwR : (k_val : ℝ) ≥ (w' : ℝ) := by exact_mod_cast hkw
  have h2 : (n_val - k_val : ℝ) ≤ μ * (n - k) := by
    linarith [show (n - k : ℝ) * μ = μ * (n - k) from by ring]
  have hnkpos : (0 : ℝ) < (n - k : ℝ) := by
    have hkn : (k : ℝ) < (n : ℝ) := by exact_mod_cast hkltn
    linarith
  have hr : ((n_val - k_val : ℝ) / (n - k : ℝ)) ≤ μ := by
    rw [div_le_iff₀ hnkpos]; exact h2
  -- (e) match karp_d E s k v se réduit par hkdk → some(...) ≤ maxCycleMeanSimple E = ↑μ
  rw [hkdk]
  dsimp only
  rw [← hμ]
  exact WithBot.coe_le_coe.mpr hr

/-- **F2/FB-Queue** — géométrie du raccourci NON-dégénéré (retrait du cycle [i..j] quand
    `j+1 < l.length`), TRIPLIÉE (Dir A `maxCycleMeanKarp_le_simple`, Dir B
    `karp_d_ne_bot_lt_card`, Dir B `excess_n_le_excess_k`) : `l' = take(i+1) ++ drop(j+1)`
    est un chemin de `s` à `t` de longueur `k'+1` (k' = l.length − (j−i) − 1 < kk), avec
    `d_{k'}(t) ≥ walkWeightL l'` (témoin `karp_d_ge_walkWeightL`) et la décomposition
    `walkWeightL l = walkWeightL l' ⊗ walkWeightL c'` (`path_shorten_weight`). Chaque site
    ne fournit que `(kk, hleng, hkk_lt, hkk)` (kk = n avec `l.length = n+1`, ou kk = k avec
    `l.length = k+1`) et conclut son propre but depuis `hge`/`hww`. -/
lemma produce_shortened_walk {V : Type*} [Fintype V] [DecidableEq V] (E : EdgeSet V)
    (s : V) (t : V) (l : List V) (kk : ℕ) (i j : ℕ)
    (hi : i < l.length) (hj : j < l.length) (hij : i < j)
    (heq : l.get ⟨i, hi⟩ = l.get ⟨j, hj⟩) (hj1 : j + 1 < l.length)
    (hl0p : 0 < l.length) (hl0 : l.get ⟨0, hl0p⟩ = s)
    (hleng : l.length = kk + 1) (hkk_lt : kk < l.length) (hkk : l.get ⟨kk, hkk_lt⟩ = t) :
    ∃ (k' : ℕ) (l' : List V) (hl'0 : 0 < l'.length) (hl'k : k' < l'.length),
      l'.length = l.length - (j - i) ∧ l'.length = k' + 1 ∧
      l'.get ⟨0, hl'0⟩ = s ∧ l'.get ⟨k', hl'k⟩ = t ∧
      karp_d E s k' t ≥ walkWeightL E l' ∧
      walkWeightL E l = walkWeightL E l' * walkWeightL E ((l.drop i).take (j - i + 1)) := by
  set l' := l.take (i+1) ++ l.drop (j+1) with hl'def
  have hl'len0 : l'.length = l.length - (j - i) := by
    show (l.take (i+1) ++ l.drop (j+1)).length = l.length - (j - i)
    rw [List.length_append, List.length_take, List.length_drop,
        min_eq_left (by omega : (i+1) ≤ l.length)]
    omega
  have hl'0 : 0 < l'.length := by rw [hl'len0]; omega
  set k' := l'.length - 1 with hk'def
  have hl'len : l'.length = k' + 1 := by rw [hk'def]; omega
  have hl'k : k' < l'.length := by rw [hl'len]; omega
  have hl's : l'.get ⟨0, hl'0⟩ = s := by
    have h0tk : 0 < (l.take (i+1)).length := by
      rw [List.length_take, min_eq_left (by omega : (i+1) ≤ l.length)]; omega
    show (l.take (i+1) ++ l.drop (j+1)).get ⟨0, hl'0⟩ = s
    rw [get_append_left_fin (l.take (i+1)) h0tk, get_take_fin l (i+1) 0 h0tk,
        get_fin_irrel l 0 _ hl0p, hl0]
  have hl'v : l'.get ⟨k', hl'k⟩ = t := by
    have hle2 : (l.take (i+1)).length ≤ k' := by
      rw [List.length_take, min_eq_left (by omega : (i+1) ≤ l.length)]; omega
    have htklen : (l.take (i+1)).length = i + 1 := by
      rw [List.length_take, min_eq_left (by omega : (i+1) ≤ l.length)]
    have hkn : (j + 1) + (k' - (i + 1)) = kk := by
      rw [hk'def, hl'len0, hleng]
      omega
    have hidx : (j + 1) + (k' - (l.take (i+1)).length) = kk := by rw [htklen]; exact hkn
    show (l.take (i+1) ++ l.drop (j+1)).get ⟨k', hl'k⟩ = t
    rw [get_append_right_fin (l.take (i+1)) (l.drop (j+1)) hle2,
        get_drop_eq l (j+1) (k' - (l.take (i+1)).length)
          (by rw [List.length_drop, htklen]; omega),
        get_fin_eq l hidx hkk_lt, hkk]
  have hge := karp_d_ge_walkWeightL E s k' t l' hl'len hl'0 hl'k hl's hl'v
  have hww : walkWeightL E l = walkWeightL E l' * walkWeightL E ((l.drop i).take (j - i + 1)) :=
    path_shorten_weight E l i j hi hj hij hj1 heq
  exact ⟨k', l', hl'0, hl'k, hl'len0, hl'len, hl's, hl'v, hge, hww⟩

/-- **F2/FB-Queue** — géométrie du raccourci DÉGÉNÉRÉ (le repeat touche le dernier sommet :
    `j+1 = l.length`) : `l' = take(i+1)` est un chemin de `s` à `t` de longueur `i+1 < kk`,
    avec `d_i(t) ≥ walkWeightL l'` et `walkWeightL l = walkWeightL l' ⊗ walkWeightL c'`
    (`path_shorten_weight_last`). Miroir de `produce_shortened_walk` (mêmes 3 sites). -/
lemma produce_shortened_walk_last {V : Type*} [Fintype V] [DecidableEq V] (E : EdgeSet V)
    (s : V) (t : V) (l : List V) (kk : ℕ) (i j : ℕ)
    (hi : i < l.length) (hj : j < l.length) (hij : i < j)
    (heq : l.get ⟨i, hi⟩ = l.get ⟨j, hj⟩) (hj1eq : j + 1 = l.length)
    (hl0p : 0 < l.length) (hl0 : l.get ⟨0, hl0p⟩ = s)
    (hleng : l.length = kk + 1) (hkk_lt : kk < l.length) (hkk : l.get ⟨kk, hkk_lt⟩ = t) :
    ∃ (l' : List V) (hl'0 : 0 < l'.length) (hl'k : i < l'.length),
      l'.length = i + 1 ∧ l'.get ⟨0, hl'0⟩ = s ∧ l'.get ⟨i, hl'k⟩ = t ∧
      karp_d E s i t ≥ walkWeightL E l' ∧
      walkWeightL E l = walkWeightL E l' * walkWeightL E ((l.drop i).take (j - i + 1)) := by
  set l' := l.take (i+1) with hl'def
  have hjn : j = kk := by omega
  have hl'len : l'.length = i + 1 := by
    show (l.take (i+1)).length = i + 1
    rw [List.length_take, min_eq_left (by omega : (i+1) ≤ l.length)]
  have hl'0 : 0 < l'.length := by rw [hl'len]; omega
  have hl's : l'.get ⟨0, hl'0⟩ = s := by
    have h0tk : 0 < (l.take (i+1)).length := by
      rw [List.length_take, min_eq_left (by omega : (i+1) ≤ l.length)]; omega
    show (l.take (i+1)).get ⟨0, hl'0⟩ = s
    rw [get_take_fin l (i+1) 0 hl'0, get_fin_irrel l 0 _ hl0p, hl0]
  have hl'k : i < l'.length := by rw [hl'len]; omega
  have hl'v : l'.get ⟨i, hl'k⟩ = t := by
    show (l.take (i+1)).get ⟨i, hl'k⟩ = t
    rw [get_take_fin l (i+1) i hl'k, get_fin_irrel l i _ hi, heq,
        get_fin_eq l hjn hkk_lt, hkk]
  have hge := karp_d_ge_walkWeightL E s i t l' hl'len hl'0 hl'k hl's hl'v
  have hww : walkWeightL E l = walkWeightL E l' * walkWeightL E ((l.drop i).take (j - i + 1)) :=
    path_shorten_weight_last E l i j hi hj hij hj1eq
  exact ⟨l', hl'0, hl'k, hl'len, hl's, hl'v, hge, hww⟩

/-- **A5 effectif** — Direction A : la formule Karp ne surestime pas λ* = max cycle mean.
    `maxCycleMeanKarp E ≤ maxCycleMeanSimple E` sous `h_edge` (PAS d'`Irreducible`). Preuve :
    dépliage du LHS (`Finset.sup_le` sur `v` ; cas `d_n(v) = ⊥` trivial `bot_le` ; cas `ofInt n_val`
    fini, `ks` non-vide → `Finset.inf'_le_iff` → on produit un `k` témoin) ; pour chaque `v` à
    `d_n(v)` fini, le chemin argmax de longueur `n` (poids `ofInt n_val`) est raccourci par
    premier-repeat (cycle SIMPLE `c*` de mean ≤ μ*_simple), additivité `G_μ` + pont donnent
    `(d_n−d_k)/(n−k) ≤ μ*` pour le `k` du chemin raccourci, donc `f k ≤ maxCycleMeanSimple E`. -/
theorem maxCycleMeanKarp_le_simple {V : Type*} [Fintype V] [DecidableEq V] (E : EdgeSet V)
    (h_edge : ∀ (p : V × V), p ∉ E.edges → E.weight p = (0 : Z_max)) :
    maxCycleMeanKarp E ≤ maxCycleMeanSimple E := by
  unfold maxCycleMeanKarp
  split
  · -- isTrue : 0 < Fintype.card V
    rename_i hpos
    haveI : Nonempty V := Fintype.card_pos_iff.mp hpos
    refine Finset.sup_le (fun v _ => ?_)
    dsimp only
    set s := Classical.arbitrary V with hs
    set n := Fintype.card V with hn
    -- cas `d_n(v)` : negInf (⊥ ≤ _, trivial) vs ofInt n_val (fini, ks non-vide → inégalité per-v)
    cases hdn : karp_d E s n v with
    | negInf =>
      dsimp only
      exact (bot_le : (⊥ : WithBot ℝ) ≤ maxCycleMeanSimple E)
    | ofInt n_val =>
      dsimp only
      set ks := (Finset.Iio n).filter (fun k => karp_d E s k v ≠ (⊥ : Z_max)) with hksdef
      by_cases hks : ks.Nonempty
      · -- ks non-vide : on produit un k témoin (longueur du chemin raccourci)
        rw [dif_pos hks, Finset.inf'_le_iff]
        -- (1) chemin argmax de longueur n finissant en v (existe : d_n(v) = ofInt n_val ≠ ⊥)
        have hdn_ne : karp_d E s n v ≠ (⊥ : Z_max) := by
          rw [hdn]; exact Z_max.ofInt_ne_bot n_val
        obtain ⟨f, hf0, hflast, hfw⟩ := exists_path_weight_eq_karp_d E s n v hdn_ne
        set l := List.ofFn f with hldef
        have hlen : l.length = n + 1 := by rw [hldef, List.length_ofFn]
        have hwl : walkWeightL E l = ofInt n_val := by
          rw [hldef, ← walkWeight_eq_walkWeightL E n f, hfw, hdn]
        have hwl_ne : walkWeightL E l ≠ (⊥ : Z_max) := by rw [hwl]; exact Z_max.ofInt_ne_bot n_val
        have hwalk : IsWalk E l := walkWeightL_finite_imp_isWalk E h_edge l hwl_ne
        -- (2) extrémités de l : l[0] = s, l[n] = v  (l = ofFn f, f 0 = s, f (Fin.last n) = v)
        have hl0p : 0 < l.length := by omega
        have hl0 : l.get ⟨0, hl0p⟩ = s := by
          show (List.ofFn f).get ⟨0, hl0p⟩ = s
          rw [List.get_ofFn]
          exact (congrArg f (Fin.eq_of_val_eq rfl) : f _ = f (0 : Fin (n + 1))).trans hf0
        have hlnp : n < l.length := by omega
        have hln : l.get ⟨n, hlnp⟩ = v := by
          show (List.ofFn f).get ⟨n, hlnp⟩ = v
          rw [List.get_ofFn]
          exact (congrArg f (Fin.eq_of_val_eq rfl) : f _ = f (Fin.last n)).trans hflast
        -- (3) pigeonhole : l plus long que |V| → premier-repeat (i, j), préfixe Nodup
        have hcard : Fintype.card V < l.length := by rw [hlen, hn]; omega
        obtain ⟨i, j, hi, hj, hij, heq, hjnodup⟩ := exists_first_repeat l hcard
        -- (4) cycle SIMPLE c* extrait ; μ* extraction (c* témoin ⟹ maxCycleMeanSimple ≠ ⊥)
        have hcyc : isCycle E ((l.drop i).take (j - i + 1)) :=
          cycle_from_repeated E l i j hi hj hij heq hwalk
        have hsc : isSimpleCycle E ((l.drop i).take (j - i + 1)) :=
          simple_cycle_of_first_repeat E l hwalk i j hi hj hij heq hjnodup
        have hcm_ne : cycleMean E ((l.drop i).take (j - i + 1)) ≠ (⊥ : WithBot ℝ) := by
          have hclen : 2 ≤ ((l.drop i).take (j - i + 1)).length := hcyc.1
          rw [cycleMean, dif_pos hclen]; exact WithBot.coe_ne_bot
        have hcm : cycleMean E ((l.drop i).take (j - i + 1)) ≤ maxCycleMeanSimple E :=
          cycleMean_le_max E hsc
        have hsup_ne : maxCycleMeanSimple E ≠ (⊥ : WithBot ℝ) := by
          intro h
          apply hcm_ne
          have hh : cycleMean E ((l.drop i).take (j - i + 1)) ≤ ⊥ := h ▸ hcm
          exact le_antisymm hh bot_le
        obtain ⟨μ, hμ⟩ := WithBot.ne_bot_iff_exists.mp hsup_ne  -- hμ : ↑μ = maxCycleMeanSimple E
        -- (5) borne G_μ(c*) ≤ 0 (cycleMean c* ≤ μ* via le pont)
        have hgc : G_μ_fin E μ ((l.drop i).take (j - i + 1)) ≤ 0 := by
          rw [← G_μ_fin_cycle_nonpos E ((l.drop i).take (j - i + 1)) hcyc μ]
          exact hcm.trans hμ.symm.le
        -- (6) dégénéré (j+1 = l.length) vs non-dégénéré (j+1 < l.length)
        by_cases hj1 : j + 1 < l.length
        · -- NON-dégénéré : k' = l'.length − 1, l' = take(i+1) ++ drop(j+1)  (FB-Queue)
          obtain ⟨k, l', hl'0, hl'k, hl'len0, hl'len, hl's, hl'v, hge, hww⟩ :=
            produce_shortened_walk E s v l n i j hi hj hij heq hj1 hl0p hl0 hlen hlnp hln
          have hkltn : k < n := by omega
          have hadd : G_μ_fin E μ l = G_μ_fin E μ l' + G_μ_fin E μ ((l.drop i).take (j - i + 1)) := by
            refine G_μ_fin_add_general E μ l l' ((l.drop i).take (j - i + 1)) hww hwl_ne ?_
            have hclen : ((l.drop i).take (j - i + 1)).length = j - i + 1 := by
              rw [List.length_take, List.length_drop,
                  min_eq_left (by omega : (j - i + 1) ≤ l.length - i)]
            rw [hl'len, hclen]; omega
          -- (7) queue per-v : production du k témoin (le chemin raccourci l' a poids fini ⟹ d_k ≠ ⊥)
          have hkmem : k ∈ ks := by
            rw [hksdef]
            refine Finset.mem_filter.mpr ⟨Finset.mem_Iio.mpr hkltn, ?_⟩
            intro h
            rw [h] at hge
            have hl'bot : walkWeightL E l' = (⊥ : Z_max) := le_antisymm hge bot_le
            exact Z_max.ofInt_ne_bot n_val (by rw [← hwl, hww, hl'bot]; exact Z_max.zero_mul _)
          cases hkdk : karp_d E s k v with
          | negInf =>
            rw [hkdk] at hge
            have hl'bot : walkWeightL E l' = (⊥ : Z_max) := le_antisymm hge bot_le
            exact absurd (by rw [← hwl, hww, hl'bot]; exact Z_max.zero_mul _) (Z_max.ofInt_ne_bot n_val)
          | ofInt k_val =>
            refine ⟨k, hkmem, ?_⟩
            exact per_v_ineq E s v l l' ((l.drop i).take (j - i + 1)) n_val n k k_val μ hμ hgc
              hadd hwl hww hlen hl'len hkdk hge hkltn
        · -- DÉGÉNÉRÉ : j+1 = l.length, k = i, l' = take(i+1)  (FB-Queue)
          have hj1eq : j + 1 = l.length := by omega
          have hkltn : i < n := by omega
          obtain ⟨l', hl'0, hl'k, hl'len, hl's, hl'v, hge, hww⟩ :=
            produce_shortened_walk_last E s v l n i j hi hj hij heq hj1eq hl0p hl0 hlen hlnp hln
          have hadd : G_μ_fin E μ l = G_μ_fin E μ l' + G_μ_fin E μ ((l.drop i).take (j - i + 1)) := by
            refine G_μ_fin_add_general E μ l l' ((l.drop i).take (j - i + 1)) hww hwl_ne ?_
            have hclen : ((l.drop i).take (j - i + 1)).length = j - i + 1 := by
              rw [List.length_take, List.length_drop, min_eq_left (by omega : (j - i + 1) ≤ l.length - i)]
            rw [hl'len, hclen]; omega
          have hkmem : i ∈ ks := by
            rw [hksdef]
            refine Finset.mem_filter.mpr ⟨Finset.mem_Iio.mpr hkltn, ?_⟩
            intro h
            rw [h] at hge
            have hl'bot : walkWeightL E l' = (⊥ : Z_max) := le_antisymm hge bot_le
            exact Z_max.ofInt_ne_bot n_val (by rw [← hwl, hww, hl'bot]; exact Z_max.zero_mul _)
          cases hkdk : karp_d E s i v with
          | negInf =>
            rw [hkdk] at hge
            have hl'bot : walkWeightL E l' = (⊥ : Z_max) := le_antisymm hge bot_le
            exact absurd (by rw [← hwl, hww, hl'bot]; exact Z_max.zero_mul _) (Z_max.ofInt_ne_bot n_val)
          | ofInt k_val =>
            refine ⟨i, hkmem, ?_⟩
            exact per_v_ineq E s v l l' ((l.drop i).take (j - i + 1)) n_val n i k_val μ hμ hgc
              hadd hwl hww hlen hl'len hkdk hge hkltn
      · -- ks vide → (⊥ : WithBot ℝ) ≤ _
        rw [dif_neg hks]
        exact (bot_le : (⊥ : WithBot ℝ) ≤ maxCycleMeanSimple E)
  · -- isFalse : ¬ (0 < card V) → maxCycleMeanKarp = (⊥ : WithBot ℝ) ≤ _
    exact (bot_le : (⊥ : WithBot ℝ) ≤ maxCycleMeanSimple E)

/-! ## Irréductibilité (forte connexité) — décision (i) / dimension (c)

    Miroir côté `EdgeSet` de `TropicalPerronFrobenius.Irreducible` (matrice :
    `∀ i j, ∃ k, (A^k) i j ≠ ⊥`), sous l'alignage `tegEdgeSet.weight = tegToZmaxMatrix`
    (découverte #4, post-fix (a)). Requis par l'énoncé **général** `maxCycleMeanKarp_correct`
    (décision (i)) : la formule Karp single-source (`Classical.arbitrary V` + `n = Fintype.card V`)
    n'est correcte que pour un graphe fortement connexe — sinon `D_n(v)=⊥` pour les sommets
    hors du SCC de la source, et le LHS est faux (contre-ex. SCC `B↔C` mean 1 + `A` self-boucle
    mean 10 inaccessible, `n=3`, source `B` → LHS ⊥ vs RHS 10). Aligne avec #5 `h_irred` + BCOQ
    (eigenvalue = max cycle mean sous irréductibilité) ; **#4 hérite** de l'hypothèse. -/

/-- Un `EdgeSet` est **irréductible** (= fortement connexe) si pour tout couple de sommets
    `(s, v)`, il existe un chemin de `s` à `v` de poids fini : `∃ k, karp_d E s k v ≠ ⊥`.
    `karp_d E s k v ≠ ⊥` équivaut à « ∃ chemin de longueur `k` de `s` à `v` de poids fini »
    (cf. `karp_d_path_weight`) — soit exactement la forte connexité. Miroir `EdgeSet` de
    `TropicalPerronFrobenius.Irreducible` (`∃ k, (A^k) i j ≠ ⊥`). -/
def Irreducible {V : Type*} [Fintype V] [DecidableEq V] (E : EdgeSet V) : Prop :=
  ∀ (s v : V), ∃ (k : ℕ), karp_d E s k v ≠ (⊥ : Z_max)

/-! ## C1 — pont `sSup`{cycleMean | isCycle} = `maxCycleMeanSimple` (dérisqué sorry-free)

    C1 est le pont entre la moyenne de cycle maximale sur les cycles SIMPLES
    (`maxCycleMeanSimple` = `Finset.sup` sur `SimpleCycle E`, concret, atteint — PAS de `BddAbove`)
    et le supremum abstrait sur TOUS les cycles (RHS de l'énoncé-cible `maxCycleMeanKarp_correct`).
    C1 active ensuite A5 (`maxCycleMeanKarp_le_simple`) pour la Direction A de la cible
    (`maxCycleMeanKarp E ≤ sSup{...}` se déduit de ≤ `maxCycleMeanSimple` + C1), et ramène la
    Direction B à `maxCycleMeanSimple ≤ maxCycleMeanKarp` (témoin concret, D2/BddAbove ÉVITÉE).

    **Math.** Tout cycle `c` (closed walk, pas simple) se décompose en un sous-cycle `c'`
    + un reste `l'` (tous deux cycles, strictement plus courts) ; `cycleMean c` = moyenne
    pondérée de `cycleMean c'` et `cycleMean l'` ≤ max des deux ≤ `maxCycleMeanSimple`
    (récurrence forte sur `c.length`). Inégalité inverse : cycles simples ⊂ cycles.
    La décomposition (sous-cycle + reste + identité de poids + reste est une marche) est
    DÉJÀ PROUVÉE sorry-free par `path_shorten_by_cycle_removal` (pièce 3). Pour un CYCLE
    `c` (c[0]=c[n]), tout repeat `a<b<n=c.length-1` vérifie `b+1 ≤ n < c.length` ⟹ la
    condition non-dégénérée `j+1<l.length` de `path_shorten` est satisfaite, et `l'` (marche
    fermée) est `isCycle` (via `isCycle_iff_chain`).

    **Hypothèse `h_finite` SEULE** (cf. plan). `h_edge` REDONDANT : `isCycle E c` exige déjà
    `(c[i],c[i+1]) ∈ E.edges`, donc les sous-marches `c'`/`l'` héritent `∈ E.edges` sans
    `h_edge` (qui ne contraint que les poids **off-edge**, absents d'un cycle). `h_finite`
    est une simplification JUSTIFIÉE : le piège `toInt(⊥)=0` (cf. `Z_max`) brise l'additivité
    `toInt(cycleWeight c) = toInt(cycleWeight c') + toInt(cycleWeight l')` quand une arête est
    `⊥` (⊗ absorbant ⟹ `cycleWeight = ⊥` ⟹ `toInt = 0`, mais le produit partitionné donne
    `toInt(c') + toInt(l') ≠ 0` en général). `h_finite` (toute arête on-edge est `ofInt`)
    élimine ce cas : `cycleWeight` fini ⟹ `toInt` additif ⟹ moyenne pondérée propre.

    **PIVOT G_μ** (vs route directe) : la moyenne pondérée directe en ℝ est INTRACTABLE
    (`(n-1:ℝ)` s'élabore en `↑n-1` cast-then-sub, opaque à `omega`/`linarith`/`positivity` via
    `Int.subNatNat` ; cf. [[lean4-proof-gotchas]] #10). La route G_μ **évite `cast_sub`** :
    `G_μ_fin` utilise `((length-1:ℕ):ℝ)` (sub-then-cast) systématiquement + `Nat.cast_add`
    (compte d'arêtes), `ring` ferme l'additivité `G_μ_fin c = G_μ_fin l' + G_μ_fin c'`.
    Dérisqué sorry-free dans `C1_scratch.lean` (`#print axioms` = `[propext, Classical.choice,
    Quot.sound]`), porté ici. -/

section C1

variable {V : Type*} [DecidableEq V] (E : EdgeSet V)

/-! ### Helpers C1 : ponts `isCycle`↔`IsWalk`, finitude `walkWeightL`, extraction de repeat -/

/-- `isCycle E c → IsWalk E c`. La 2e conjointe de `isCycle` (paires consécutives ∈ E.edges)
    est exactement la condition `IsWalk`, pontée par `isCycle_iff_chain` + `IsWalk_iff_isChain`. -/
lemma isCycle.isWalk {c : List V} (hc : isCycle E c) : IsWalk E c :=
  (IsWalk_iff_isChain E c).mpr ((isCycle_iff_chain E c hc.1).mp hc).1

/-- Une marche fermée (`IsWalk` + premier=dernier) de longueur ≥ 2 est un `isCycle`. -/
lemma IsWalk.isCycle_of_closed {l : List V} (hw : IsWalk E l) (hlen : 2 ≤ l.length)
    (hclose : l.get ⟨0, by omega⟩ = l.get ⟨l.length - 1, by omega⟩) : isCycle E l :=
  (isCycle_iff_chain E l hlen).mpr ⟨(IsWalk_iff_isChain E l).mp hw, hclose⟩

/-- Sous `h_finite`, le poids max-plus d'une marche `IsWalk` est fini (`ofInt`) :
    récurrence structurelle sur la liste ; chaque arête `(a,b) ∈ E.edges` (IsWalk) ⟹
    `E.weight (a,b) = ofInt z` (`h_finite`), produit ⊗ = `ofInt (Σ z)`. -/
lemma walkWeightL_finite (h_finite : ∀ (p : V × V), p ∈ E.edges → ∃ (z : ℤ), E.weight p = Z_max.ofInt z)
    (l : List V) (hw : IsWalk E l) :
    ∃ (W : ℤ), walkWeightL E l = Z_max.ofInt W := by
  induction l with
  | nil => exact ⟨0, rfl⟩                       -- walkWeightL [] = 1 = ofInt 0
  | cons a rest ih =>
    by_cases hrest : rest = []
    · subst hrest; exact ⟨0, rfl⟩               -- walkWeightL [a] = 1 = ofInt 0
    · obtain ⟨b, rest', rfl⟩ := List.exists_cons_of_ne_nil hrest
      have hlen : (a :: b :: rest').length = (b :: rest').length + 1 := by simp [List.length]
      have hbrlen : 0 < (b :: rest').length := by simp
      have hab : (a, b) ∈ E.edges := by
        have hkey := hw 0 (by omega)
        simpa [List.get_cons_zero, List.get_cons_succ] using hkey
      obtain ⟨z, hz⟩ := h_finite (a, b) hab
      have hw' : IsWalk E (b :: rest') := by
        intro i hi
        have hkey := hw (i + 1) (by omega)
        simpa [List.get_cons_zero, List.get_cons_succ] using hkey
      obtain ⟨W', hW'⟩ := ih hw'
      refine ⟨z + W', ?_⟩
      rw [walkWeightL_cons_cons, hz, hW']        -- ofInt z * ofInt W' = ofInt (z + W')
      rfl

/-- Depuis `¬ l.Nodup`, un sommet répété `a < b`, `b < l.length`, `l[a] = l[b]`.
    Contraposée de `List.nodup_iff_getElem?_ne_getElem? : l.Nodup ↔ ∀ i j, i<j → j<l.length → l[i]?≠l[j]?`. -/
lemma exists_repeat_of_not_nodup {α : Type*} [DecidableEq α] (l : List α) (h : ¬ l.Nodup) :
    ∃ (a b : ℕ) (ha : a < l.length) (hb : b < l.length),
      a < b ∧ l.get ⟨a, ha⟩ = l.get ⟨b, hb⟩ := by
  rw [List.nodup_iff_getElem?_ne_getElem?] at h
  push_neg at h
  obtain ⟨a, b, hab, hb, heq⟩ := h
  have ha : a < l.length := by omega
  refine ⟨a, b, ha, hb, hab, ?_⟩
  rw [List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb] at heq
  exact Option.some.inj heq

/-! ### Lemme-clé : `cycleMean E c ≤ maxCycleMeanSimple E` (récurrence forte sur `c.length`) -/

/-- Sous `h_finite`, la moyenne d'un cycle est `some` (non-⊥) : `cycleWeight = ofInt`
    (arêtes on-edge toutes `ofInt` ⟹ produit ⊗ = somme entière) ⟹ `cycleMean = some (réel)`. -/
lemma cycleMean_ne_bot_of_finite
    (h_finite : ∀ (p : V × V), p ∈ E.edges → ∃ (z : ℤ), E.weight p = Z_max.ofInt z)
    (c : List V) (hc : isCycle E c) : cycleMean E c ≠ (⊥ : WithBot ℝ) := by
  rw [cycleMean, dif_pos hc.1]
  have hW : ∃ W, cycleWeight E c = Z_max.ofInt W := by
    rw [cycleWeight_eq_walkWeightL E c hc]
    exact walkWeightL_finite E h_finite c (isCycle.isWalk E hc)
  obtain ⟨W, hW⟩ := hW
  rw [hW]
  exact WithBot.coe_ne_bot

/-- Tout cycle contient un cycle simple de longueur ≤ la sienne (récurrence forte
    structurelle sur `c.length`, SANS `h_finite`). Simple : `c` lui-même. Non-simple :
    repeat ⟹ `path_shorten` extrait `c'` strictement plus court ⟹ `ih c'` donne un simple. -/
lemma isCycle.contains_simple (c : List V) (hc : isCycle E c) :
    ∃ sc : SimpleCycle E, sc.val.length ≤ c.length := by
  have key : ∀ (n : ℕ) (c : List V), c.length ≤ n → isCycle E c →
      ∃ sc : SimpleCycle E, sc.val.length ≤ c.length := by
    intro n
    refine Nat.strongRecOn n (fun m ih c hlen hc => ?_)
    have hcn : 2 ≤ c.length := hc.1
    by_cases hnd : (c.take (c.length - 1)).Nodup
    · exact ⟨⟨c, ⟨hc, hnd⟩⟩, Nat.le_refl _⟩
    · set nedges := c.length - 1
      have htklen : (c.take nedges).length = nedges := by
        rw [List.length_take, min_eq_left (by omega : (nedges : ℕ) ≤ c.length)]
      obtain ⟨a, b, ha_take, hb_take, hab, heqtk⟩ := exists_repeat_of_not_nodup (c.take nedges) hnd
      have haL : a < c.length := by omega
      have hbL : b < c.length := by omega
      have hca : c.get ⟨a, haL⟩ = c.get ⟨b, hbL⟩ := by
        have hga := get_take_fin c nedges a ha_take
        have hgb := get_take_fin c nedges b hb_take
        rw [hga, hgb] at heqtk; exact heqtk
      have hwalk : IsWalk E c := isCycle.isWalk E hc
      have hb1 : b + 1 < c.length := by omega
      set c' := (c.drop a).take (b - a + 1) with hc'def
      obtain ⟨hc', hwt, hl'walk⟩ := path_shorten_by_cycle_removal E c a b haL hbL hab hb1 hca hwalk
      have hc'len : c'.length = b - a + 1 := by
        rw [hc'def, List.length_take, List.length_drop, min_eq_left (by omega)]
      have hc'lt : c'.length < c.length := by rw [hc'len]; omega
      obtain ⟨sc, hsc⟩ := ih c'.length (by omega) c' (Nat.le_refl c'.length) hc'
      exact ⟨sc, hsc.trans hc'lt.le⟩
  exact key c.length c (Nat.le_refl c.length) hc

/-- Tout cycle a sa moyenne ≤ `maxCycleMeanSimple`. Récurrence forte sur `c.length`.
    `maxCycleMeanSimple ≠ ⊥` (car `c` contient un cycle simple `sc`, `cycleMean sc ≤ max`,
    `cycleMean sc ≠ ⊥` via `h_finite`), d'où `max = ↑μ`. Simple : `cycleMean_le_max`.
    Non-simple : `path_shorten` en `c'`+`l'`, pont `G_μ_fin_cycle_nonpos`
    (`cycleMean ≤ ↑μ ↔ G_μ_fin ≤ 0`), additivité `G_μ_fin c = G_μ_fin l' + G_μ_fin c'`
    (sous `h_finite` : `ofInt` + `Nat.cast_add`, SANS `Nat.cast_sub` — G_μ_fin utilise
    systématiquement le cast sub-then-cast `↑(length - 1)`), `ih` ⟹ `G_μ_fin c'`, `l' ≤ 0`. -/
lemma cycleMean_le_maxCycleMeanSimple [Fintype V]
    (h_finite : ∀ (p : V × V), p ∈ E.edges → ∃ (z : ℤ), E.weight p = Z_max.ofInt z)
    (c : List V) (hc : isCycle E c) :
    cycleMean E c ≤ maxCycleMeanSimple E := by
  -- maxCycleMeanSimple ≠ ⊥ : c contient un cycle simple sc ; cycleMean sc ≤ max ; ≠ ⊥
  obtain ⟨sc⟩ := isCycle.contains_simple E c hc
  have hle_sc : cycleMean E sc.val ≤ maxCycleMeanSimple E := cycleMean_le_max E sc.2
  have hscm_ne : cycleMean E sc.val ≠ (⊥ : WithBot ℝ) :=
    cycleMean_ne_bot_of_finite E h_finite sc.val sc.2.1
  have hmax_ne : maxCycleMeanSimple E ≠ (⊥ : WithBot ℝ) := by
    intro h; rw [h] at hle_sc; exact hscm_ne (le_antisymm hle_sc bot_le)
  obtain ⟨μ, hμ⟩ := WithBot.ne_bot_iff_exists.mp hmax_ne   -- hμ : ↑μ = maxCycleMeanSimple E
  -- récurrence forte : ∀ c (isCycle), cycleMean E c ≤ ↑μ  (≤ max via hμ)
  have hkey : ∀ (n : ℕ) (c : List V), c.length ≤ n → isCycle E c →
      cycleMean E c ≤ (μ : WithBot ℝ) := by
    intro n
    refine Nat.strongRecOn n (fun m ih c hlen hc => ?_)
    -- ih : ∀ k < m, ∀ c', c'.length ≤ k → isCycle E c' → cycleMean E c' ≤ ↑μ
    have hcn : 2 ≤ c.length := hc.1
    by_cases hnd : (c.take (c.length - 1)).Nodup
    · -- cas simple : cycleMean_le_max ≤ max = ↑μ
      have hle := cycleMean_le_max E ⟨hc, hnd⟩
      rwa [← hμ] at hle
    · -- cas non-simple : G_μ bridge
      set nedges := c.length - 1
      have htklen : (c.take nedges).length = nedges := by
        rw [List.length_take, min_eq_left (by omega : (nedges : ℕ) ≤ c.length)]
      obtain ⟨a, b, ha_take, hb_take, hab, heqtk⟩ := exists_repeat_of_not_nodup (c.take nedges) hnd
      have haL : a < c.length := by omega
      have hbL : b < c.length := by omega
      have hca : c.get ⟨a, haL⟩ = c.get ⟨b, hbL⟩ := by
        have hga := get_take_fin c nedges a ha_take
        have hgb := get_take_fin c nedges b hb_take
        rw [hga, hgb] at heqtk; exact heqtk
      have hwalk : IsWalk E c := isCycle.isWalk E hc
      have hb1 : b + 1 < c.length := by omega
      set c' := (c.drop a).take (b - a + 1) with hc'def
      set l' := c.take (a + 1) ++ c.drop (b + 1) with hl'def
      obtain ⟨hc', hwt, hl'walk⟩ :=
        path_shorten_by_cycle_removal E c a b haL hbL hab hb1 hca hwalk
      have hc'len : c'.length = b - a + 1 := by
        rw [hc'def, List.length_take, List.length_drop, min_eq_left (by omega)]
      have hl'len : l'.length = c.length - (b - a) := by
        rw [hl'def, List.length_append, List.length_take, min_eq_left (by omega),
          List.length_drop]
        omega
      have hc'2 : 2 ≤ c'.length := by rw [hc'len]; omega
      have hl'2 : 2 ≤ l'.length := by rw [hl'len]; omega
      have hl'close : l'.get ⟨0, by omega⟩ = l'.get ⟨l'.length - 1, by omega⟩ := by
        -- l'[0] = c[0]  (jonction via get_append_left_fin + get_take_fin, miroir A5 L1834)
        have htklen2 : (c.take (a + 1)).length = a + 1 := by
          rw [List.length_take, min_eq_left (by omega : (a + 1 : ℕ) ≤ c.length)]
        have h0tk : 0 < (c.take (a + 1)).length := by rw [htklen2]; omega
        have hl'len_pos : 0 < (c.take (a + 1) ++ c.drop (b + 1)).length := by
          rw [List.length_append, htklen2]; omega
        have hl'last_pos : (c.take (a + 1) ++ c.drop (b + 1)).length - 1 <
            (c.take (a + 1) ++ c.drop (b + 1)).length := by
          rw [List.length_append, htklen2]; omega
        have hc0 : 0 < c.length := by omega
        have hcLast : c.length - 1 < c.length := by omega
        have hL0 : l'.get ⟨0, by omega⟩ = c.get ⟨0, by omega⟩ := by
          show (c.take (a + 1) ++ c.drop (b + 1)).get ⟨0, hl'len_pos⟩ = c.get ⟨0, hc0⟩
          rw [get_append_left_fin (c.take (a + 1)) h0tk, get_take_fin c (a + 1) 0 h0tk]
        -- l'[last] = c[c.length-1]  (jonction via get_append_right_fin + get_drop_eq + get_fin_eq)
        have hle2 : (c.take (a + 1)).length ≤ l'.length - 1 := by rw [htklen2]; omega
        have hidx : (b + 1) + ((l'.length - 1) - (c.take (a + 1)).length) = c.length - 1 := by
          rw [htklen2]; omega
        have hRlast : l'.get ⟨l'.length - 1, by omega⟩ = c.get ⟨c.length - 1, by omega⟩ := by
          show (c.take (a + 1) ++ c.drop (b + 1)).get ⟨l'.length - 1, hl'last_pos⟩ =
            c.get ⟨c.length - 1, hcLast⟩
          rw [get_append_right_fin (c.take (a + 1)) (c.drop (b + 1)) hle2,
              get_drop_eq c (b + 1) ((l'.length - 1) - (c.take (a + 1)).length)
                (by rw [List.length_drop, htklen2]; omega),
              get_fin_eq c hidx hcLast]
        -- c[0] = c[c.length-1]  (fermeture du cycle, 3e conjoint de isCycle)
        rw [hL0, hRlast]; exact hc.2.2 hc.1
      have hl'cyc : isCycle E l' := IsWalk.isCycle_of_closed E hl'walk hl'2 hl'close
      -- IH : cycleMean c', l' ≤ ↑μ → G_μ_fin c', l' ≤ 0 (pont A4)
      have hIc' : cycleMean E c' ≤ (μ : WithBot ℝ) :=
        ih c'.length (by omega) c' (Nat.le_refl c'.length) hc'
      have hIl' : cycleMean E l' ≤ (μ : WithBot ℝ) :=
        ih l'.length (by omega) l' (Nat.le_refl l'.length) hl'cyc
      have hGc' : G_μ_fin E μ c' ≤ 0 := (G_μ_fin_cycle_nonpos E c' hc' μ).mp hIc'
      have hGl' : G_μ_fin E μ l' ≤ 0 := (G_μ_fin_cycle_nonpos E l' hl'cyc μ).mp hIl'
      -- but : cycleMean c ≤ ↑μ ↔ G_μ_fin c ≤ 0  (pont)
      rw [G_μ_fin_cycle_nonpos E c hc μ]
      -- additivité : G_μ_fin c = G_μ_fin l' + G_μ_fin c'  (G_μ_fin_add_general — cocycle A5, F1)
      have hGadd : G_μ_fin E μ c = G_μ_fin E μ l' + G_μ_fin E μ c' := by
        refine G_μ_fin_add_general E μ c l' c' hwt ?_ ?_
        · -- finitude : walkWeightL E c ≠ ⊥ (h_finite sur les facteurs + hwt)
          obtain ⟨Wl, hWl⟩ := walkWeightL_finite E h_finite l' hl'walk
          obtain ⟨Wc', hWc'⟩ := walkWeightL_finite E h_finite c' (isCycle.isWalk E hc')
          rw [hwt, hWl, hWc']
          rw [show Z_max.ofInt Wl * Z_max.ofInt Wc' = Z_max.ofInt (Wl + Wc') from rfl]
          exact Z_max.ofInt_ne_bot (Wl + Wc')
        · -- edge-count : (c.length-1) = (l'.length-1) + (c'.length-1)
          omega
      rw [hGadd]; linarith
  exact (hkey c.length c (Nat.le_refl c.length) hc).trans hμ.le

/-! ### C1 : égalité sSup = maxCycleMeanSimple -/

/-- C1 : le supremum sur tous les cycles (avec ⊥ inséré) égale `maxCycleMeanSimple`.
    ≤ : le lemme-clé donne `maxCycleMeanSimple` majorant concret de `insert ⊥ S`.
    ≥ : cycles simples ⊂ cycles ⟹ `Finset.sup ≤ sSup` (`le_csSup` sur chaque élément).
    La forme `sSup (insert ⊥ {…})` est exactement le RHS de l'énoncé-cible
    `maxCycleMeanKarp_correct` (C1 active sa Direction A via `maxCycleMeanKarp_le_simple`). -/
lemma C1_sSup_eq [Fintype V]
    (h_finite : ∀ (p : V × V), p ∈ E.edges → ∃ (z : ℤ), E.weight p = Z_max.ofInt z) :
    sSup (insert (⊥ : WithBot ℝ)
      { x : WithBot ℝ | ∃ c : List V, isCycle E c ∧ x = cycleMean E c }) = maxCycleMeanSimple E := by
  -- S = { cycleMean E c | isCycle E c } ; maxCycleMeanSimple = majorant concret (lemme-clé + bot_le)
  have hS_le : ∀ x ∈ insert (⊥ : WithBot ℝ)
      { x | ∃ c : List V, isCycle E c ∧ x = cycleMean E c }, x ≤ maxCycleMeanSimple E := by
    intro x hx
    obtain rfl | hx := Set.mem_insert_iff.mp hx
    · exact bot_le
    · obtain ⟨c, hc, rfl⟩ := hx
      exact cycleMean_le_maxCycleMeanSimple E h_finite c hc
  have hS_ne : (insert (⊥ : WithBot ℝ)
      { x | ∃ c : List V, isCycle E c ∧ x = cycleMean E c }).Nonempty :=
    ⟨⊥, Set.mem_insert _ _⟩
  have hS_bdd : BddAbove (insert (⊥ : WithBot ℝ)
      { x | ∃ c : List V, isCycle E c ∧ x = cycleMean E c }) :=
    ⟨maxCycleMeanSimple E, hS_le⟩
  refine le_antisymm ?_ ?_
  · -- ≤ : sSup ≤ maxCycleMeanSimple (majorant concret, csSup_le)
    exact csSup_le hS_ne hS_le
  · -- ≥ : maxCycleMeanSimple ≤ sSup (cycles simples ⊂ cycles, Finset.sup_le + le_csSup)
    rw [maxCycleMeanSimple]
    refine Finset.sup_le (fun sc _ => ?_)
    have hmem : cycleMean E sc.val ∈ insert (⊥ : WithBot ℝ)
        { x | ∃ c : List V, isCycle E c ∧ x = cycleMean E c } := by
      right; exact ⟨sc.val, sc.2.1, rfl⟩
    exact le_csSup hS_bdd hmem

end C1

/-! ## Théorème de Karp — assemblage Direction A + Direction B (`le_antisymm`)

    `maxCycleMeanKarp_correct = le_antisymm maxCycleMeanKarp_le_sSup maxCycleMeanKarp_ge_sSup`.
    Direction A (≤) est **sorry-free** (A5 `maxCycleMeanKarp_le_simple` + C1 `C1_sSup_eq`) ;
    Direction B (≥) est **sorry-free** (section Direction B : potentiel décalé + propagation,
    portée de `DirectionB2_scratch.lean` 2026-08-05, un-sorried P2-P7). La cible passe le
    `#print axioms` gate. -/

/-- **Direction A** du théorème de Karp : `maxCycleMeanKarp E ≤ sSup{cycleMean | isCycle}`.
    Composition `maxCycleMeanKarp_le_simple` (A5 : `maxCycleMeanKarp E ≤ maxCycleMeanSimple E`,
    sous `h_edge` seul) puis `C1_sSup_eq.symm.le` (C1 : `maxCycleMeanSimple E ≤ sSup{…}`,
    sous `h_finite` seul) — miroir de la composition `hcm.trans hμ.symm.le` (L1816).
    Ne requiert PAS `h_irred` (la Direction A tient sans forte connexité, comme A5 et C1).
    Sorry-free, `#print axioms` = `[propext, Classical.choice, Quot.sound]`. -/
theorem maxCycleMeanKarp_le_sSup {V : Type*} [Fintype V] [DecidableEq V] (E : EdgeSet V)
    (h_edge : ∀ (p : V × V), p ∉ E.edges → E.weight p = (0 : Z_max))
    (h_finite : ∀ (p : V × V), p ∈ E.edges → ∃ (z : ℤ), E.weight p = Z_max.ofInt z) :
    maxCycleMeanKarp E ≤ sSup (insert (⊥ : WithBot ℝ)
      { x : WithBot ℝ | ∃ c : List V, isCycle E c ∧ x = cycleMean E c }) :=
  (maxCycleMeanKarp_le_simple E h_edge).trans (C1_sSup_eq E h_finite).symm.le

/-! ### Direction B — potentiel décalé (porté de `DirectionB2_scratch.lean`, 2026-08-05)

    Voie **récurrence + propagation** (pas le lasso-liste géant) : `karp_d` (L45) est DÉFINI par
    la récurrence max-plus `d_{k+1}(v) = sup_u (d_k(u) * w(u,v))` (⊗ = +). On propage le potentiel
    décalé `π(v) := max_{k<n} (toRealBot(d_k(v)) − k·μ*)` LE LONG DES ARÊTES du cycle critique
    `c*` (induction sur le nombre d'arêtes pompées, `pump`), sans construire la marche géante
    `P(w) + m·c* + préfixe`. L'additivité `G_μ_fin_add_general` est ACCESSOIRE : seul
    `G_μ_fin(c*) = 0` (de `cycleMean(c*) = μ*`) est requis, pour la tightness.

    Décomposition (Karp 1978 / BCOQ Th. 2.19 §2.3.2), `n = |V|`, `m = c*.length − 1` :
      (excess_recurrence)  e_{k+1}(v) ≥ e_k(u) + shift_w(u,v)         [def karp_d + ⊗=+ + Finset.le_sup]
      (hFact2 / Dir A)     e_n(v) ≤ π(v) ∀v                          [pigeonhole n-marche → <n, cycleMean ≤ μ*]
      (edge_ineq)          π(v) ≥ π(u) + shift_w(u,v)                [attainment + recurrence + hFact2 (cas j=n−1)]
      (tightness)          π(c[i+1]) = π(c[i]) + shift_w sur c*      [edge_ineq + Σ télscopique = G_μ_fin(c*) = 0 + c[m]=c[0]]
      (pump)               ∃ v*, e_n(v*) ≥ π(v*)                     [induction sur L ; v* = c.get((n−k0) mod m)]
      (conclure)           μ* ≤ maxCycleMeanKarp                     [per_k_ineq + le_inf'_iff + le_sup]
    **`r ≠ 0` (n−k0 mod m) ABSORBÉ** : `v* = c[r]` atterrit en plein cycle, choisi après coup,
    aucune divisibilité requise. Note : `WithBot ℝ` a `Add` mais PAS `Sub`/`Neg` (⊥ casse les
    inverses) ⟹ `excess`/`shift_w` par **match sur `karp_d`/`E.weight`** (arithmétique ℝ dans
    `some`, miroir de `maxCycleMeanKarp` L482-497), récurrence via `+`. Aucun `WithBot ℝ − WithBot ℝ`.
    Cf. `cache/analyse_directionB2_derisque_2026-08-05.md` (dérisquage, leçons #18-#27). -/

section DirectionB

variable {V : Type*} [Fintype V] [DecidableEq V] (E : EdgeSet V) (s : V)

/-! #### Excess `e_k(v)` + poids d'arête décalé `shift_w` (match, évite `Sub (WithBot ℝ)`) -/

/-- Excess (potentiel décalé) : `e_k(v) = toRealBot(d_k(v)) − k·μ*`. Défini par match sur
    `karp_d` (arithmétique ℝ dans `some`), car `WithBot ℝ` n'a pas de `Sub`. -/
def excess (μstar : ℝ) (k : ℕ) (v : V) : WithBot ℝ :=
  match karp_d E s k v with
  | Z_max.negInf => (⊥ : WithBot ℝ)
  | Z_max.ofInt a => WithBot.some ((a : ℝ) - (k : ℝ) * μstar)

/-- Poids d'arête décalé `shift_w(u,v) = toRealBot(w(u,v)) − μ*` (match sur `E.weight`). -/
def shift_w (μstar : ℝ) (p : V × V) : WithBot ℝ :=
  match E.weight p with
  | Z_max.negInf => (⊥ : WithBot ℝ)
  | Z_max.ofInt b => WithBot.some ((b : ℝ) - μstar)

lemma excess_of_negInf (μstar : ℝ) (k : ℕ) (v : V)
    (h : karp_d E s k v = Z_max.negInf) : excess E s μstar k v = (⊥ : WithBot ℝ) := by
  unfold excess; rw [h]

lemma excess_of_ofInt (μstar : ℝ) (k : ℕ) (v : V) (a : ℤ)
    (h : karp_d E s k v = Z_max.ofInt a) :
    excess E s μstar k v = WithBot.some ((a : ℝ) - (k : ℝ) * μstar) := by
  unfold excess; rw [h]

lemma shift_w_of_negInf (μstar : ℝ) (p : V × V)
    (h : E.weight p = Z_max.negInf) : shift_w E μstar p = (⊥ : WithBot ℝ) := by
  unfold shift_w; rw [h]

lemma shift_w_of_ofInt (μstar : ℝ) (p : V × V) (b : ℤ)
    (h : E.weight p = Z_max.ofInt b) : shift_w E μstar p = WithBot.some ((b : ℝ) - μstar) := by
  unfold shift_w; rw [h]

/-- **Récurrence de l'excess** : `e_{k+1}(v) ≥ e_k(u) + shift_w(u,v)`.
    Clé : `karp_d` (L45) est `d_{k+1}(v) = sup_u (d_k(u) * w(u,v))`, donc `≥ d_k(u) * w(u,v)` via
    `Finset.le_sup` ; `⊗ = +` ⟹ `ofInt a * ofInt b = ofInt(a+b)`. Cas fini : `e_{k+1}(v) =
    some(c − (k+1)μ) ≥ some(a+b − (k+1)μ) = (some(a − kμ) + some(b − μ))` car `c ≥ a+b`. -/
lemma excess_recurrence (μstar : ℝ) (k : ℕ) (u v : V) :
    excess E s μstar (k+1) v ≥ excess E s μstar k u + shift_w E μstar (u, v) := by
  -- d_{k+1}(v) = sup_u (d_k(u) * w(u,v)) ≥ d_k(u) * w(u,v)
  have hkarp : karp_d E s (k+1) v =
      (Finset.univ : Finset V).sup (fun u' => karp_d E s k u' * E.weight (u', v)) := by
    rw [karp_d, if_neg (Nat.succ_ne_zero k), show (k + 1) - 1 = k from by omega]
  have hge : karp_d E s k u * E.weight (u, v) ≤ karp_d E s (k+1) v := by
    rw [hkarp]
    exact Finset.le_sup (f := fun u' => karp_d E s k u' * E.weight (u', v)) (Finset.mem_univ u)
  cases hdk : karp_d E s k u with
  | negInf =>
    have he : excess E s μstar k u = (⊥ : WithBot ℝ) := excess_of_negInf E s μstar k u hdk
    have hR : excess E s μstar k u + shift_w E μstar (u, v) = (⊥ : WithBot ℝ) := by
      rw [he]; rfl
    rw [hR]; exact bot_le
  | ofInt a =>
    cases hw : E.weight (u, v) with
    | negInf =>
      have hek : excess E s μstar k u = WithBot.some ((a : ℝ) - (k : ℝ) * μstar) :=
        excess_of_ofInt E s μstar k u a hdk
      have hsw : shift_w E μstar (u, v) = (⊥ : WithBot ℝ) := shift_w_of_negInf E μstar (u, v) hw
      have hR : excess E s μstar k u + shift_w E μstar (u, v) = (⊥ : WithBot ℝ) := by
        rw [hek, hsw]; rfl
      rw [hR]; exact bot_le
    | ofInt b =>
      have hmul : karp_d E s k u * E.weight (u, v) = Z_max.ofInt (a + b) := by rw [hdk, hw]; rfl
      have hge2 : Z_max.ofInt (a + b) ≤ karp_d E s (k+1) v := hmul ▸ hge
      cases hdk1 : karp_d E s (k+1) v with
      | negInf =>
        exfalso
        rw [hdk1] at hge2
        have hmb : Z_max.ofInt (a + b) = (⊥ : Z_max) := le_bot_iff.mp hge2
        exact Z_max.ofInt_ne_bot (a + b) hmb
      | ofInt c =>
        have hca : a + b ≤ c := by
          have hh : Z_max.ofInt (a + b) ≤ Z_max.ofInt c := by rw [hdk1] at hge2; exact hge2
          exact (Z_max.ofInt_le_iff (a + b) c).mp hh
        have hcaR : ((a + b) : ℝ) ≤ c := by exact_mod_cast hca
        have hLHS := excess_of_ofInt E s μstar (k+1) v c hdk1
        have hek := excess_of_ofInt E s μstar k u a hdk
        have hsw := shift_w_of_ofInt E μstar (u, v) b hw
        rw [hLHS, hek, hsw]
        -- goal: some(c - (k+1)μ) ≥ some(a - kμ) + some(b - μ)
        -- RHS = some((a - kμ) + (b - μ))
        rw [show WithBot.some ((a : ℝ) - (k : ℝ) * μstar) + WithBot.some ((b : ℝ) - μstar) =
              WithBot.some (((a : ℝ) - (k : ℝ) * μstar) + ((b : ℝ) - μstar)) from rfl]
        refine WithBot.coe_le_coe.mpr ?_
        push_cast
        linarith [hcaR]

/-! #### Potentiel `π(v) = max_{k<n} e_k(v)` + domination + atteinte -/

/-- Potentiel décalé : `π(v) = max_{k<n} e_k(v)` (sup sur `Finset.Iio n`). `WithBot ℝ` est
    `LinearOrder`+`OrderBot`, `Finset.sup` = max fini (les termes `e_k = ⊥` sont le bottom). -/
def pot (μstar : ℝ) (n : ℕ) (v : V) : WithBot ℝ :=
  (Finset.Iio n).sup (fun k => excess E s μstar k v)

/-- `e_k(v) ≤ π(v)` pour `k < n` (le sup majore ses éléments). -/
lemma excess_le_pot (μstar : ℝ) (n : ℕ) (k : ℕ) (v : V) (hk : k < n) :
    excess E s μstar k v ≤ pot E s μstar n v :=
  Finset.le_sup (f := fun k' => excess E s μstar k' v) (Finset.mem_Iio.mpr hk)

/-- Atteinte du sup : `π(v) = e_{k0}(v)` pour quelque `k0 < n` (Finset.max atteint sur un Finset non-vide). -/
lemma pot_attained (μstar : ℝ) (n : ℕ) (v : V) (hn : 0 < n) :
    ∃ k, k < n ∧ pot E s μstar n v = excess E s μstar k v := by
  have hne : (Finset.Iio n).Nonempty := ⟨0, Finset.mem_Iio.mpr hn⟩
  obtain ⟨k, hkmem, hk_eq⟩ :=
    Finset.exists_mem_eq_sup (s := Finset.Iio n) hne (f := fun k' => excess E s μstar k' v)
  exact ⟨k, Finset.mem_Iio.mp hkmem, hk_eq⟩

/-! #### Fact 3 — inégalité d'arête `π(v) ≥ π(u) + shift_w(u,v)` -/

/-- **Fact 3 (inégalité d'arête)** : `π(v) ≥ π(u) + shift_w(u,v)` pour toute arête `(u,v)`.
    Preuve : (1) atteinte `π(u) = e_j(u)` pour quelque `j < n` (`pot_attained`) ;
    (2) récurrence `e_{j+1}(v) ≥ e_j(u) + shift_w = π(u) + shift_w` (`excess_recurrence`) ;
    (3) `π(v) ≥ e_{j+1}(v)` — si `j+1 < n` (`excess_le_pot`), si `j+1 = n` (Fact 2 / Dir A,
    passé en hypothèse `hFact2` pour isoler la correction de la preuve du pigeonhole).
    Fonctionne uniformément même si `π(u) = ⊥` (alors `π(u) + shift_w = ⊥ ≤ π(v)`). -/
lemma edge_ineq (μstar : ℝ) (n : ℕ) (u v : V) (hn : 0 < n)
    (hFact2 : ∀ w : V, excess E s μstar n w ≤ pot E s μstar n w) :
    pot E s μstar n v ≥ pot E s μstar n u + shift_w E μstar (u, v) := by
  obtain ⟨j, hjlt, hj_eq⟩ := pot_attained E s μstar n u hn
  have hrec : excess E s μstar (j+1) v ≥ excess E s μstar j u + shift_w E μstar (u, v) :=
    excess_recurrence E s μstar j u v
  rw [← hj_eq] at hrec  -- hrec : excess (j+1) v ≥ π(u) + shift_w
  by_cases hj1 : j + 1 < n
  · have hle : excess E s μstar (j+1) v ≤ pot E s μstar n v :=
      excess_le_pot E s μstar n (j+1) v hj1
    exact le_trans hrec hle
  · have hj1_eq : j + 1 = n := by omega
    rw [hj1_eq] at hrec  -- hrec : excess n v ≥ π(u) + shift_w
    have hle : excess E s μstar n v ≤ pot E s μstar n v := hFact2 v
    exact le_trans hrec hle

/-! #### `G_μ_fin(c*) = 0` depuis `cycleMean(c*) = μ*` (égalité, pour la tightness) -/

/-- Si `cycleMean E c = some μ*` (cycle critique c*), alors `G_μ_fin E μ* c = 0`.
    Dépliage : `cycleMean = some(toInt(cycleWeight)/((c.length:ℝ)−1)) = some μ*` ⟹
    `toInt(cycleWeight) = ((c.length:ℝ)−1)·μ*` ; via `Nat.cast_sub`+`Nat.cast_one` on unifie
    `↑(c.length−1) = (c.length:ℝ)−1` (le mur `cast_sub` #10, navigué ici), et `G_μ_fin =
    toInt(walkWeightL) − ↑(c.length−1)·μ* = 0` (via `cycleWeight_eq_walkWeightL`). -/
lemma G_μ_fin_eq_zero_of_cycleMean (c : List V) (hc : isCycle E c) (μstar : ℝ)
    (hcm : cycleMean E c = some μstar) : G_μ_fin E μstar c = 0 := by
  have hlen := hc.1  -- 2 ≤ c.length
  unfold cycleMean at hcm
  rw [dif_pos hlen] at hcm
  injection hcm with hdiv
  -- hdiv : ((cycleWeight E c).toInt : ℝ) / ((c.length : ℝ) - 1) = μstar   [cast-then-sub]
  have hcast : ((c.length - 1 : ℕ) : ℝ) = ((c.length : ℝ) - 1) := by
    rw [Nat.cast_sub (by omega : 1 ≤ c.length), Nat.cast_one]
  have hpos2 : (0 : ℝ) < ((c.length : ℝ) - 1) :=
    hcast ▸ (by exact_mod_cast (by omega : 0 < c.length - 1))
  have hne : ((c.length : ℝ) - 1) ≠ 0 := hpos2.ne'
  -- toInt(cycleWeight) = (↑c.length - 1) * μ* = ↑(c.length-1) * μ*  (via hcast)
  have hcw_cs : ((cycleWeight E c).toInt : ℝ) = ((c.length : ℝ) - 1) * μstar := by
    have hcancel := div_mul_cancel₀ ((cycleWeight E c).toInt : ℝ) hne
    rw [hdiv] at hcancel
    linarith [hcancel]
  have hcw : ((cycleWeight E c).toInt : ℝ) = ((c.length - 1 : ℕ) : ℝ) * μstar := by
    rw [← hcast] at hcw_cs; linarith [hcw_cs]
  show G_μ_fin E μstar c = 0
  unfold G_μ_fin
  rw [← cycleWeight_eq_walkWeightL E c hc]
  -- goal: ((cycleWeight E c).toInt : ℝ) - ((c.length-1:ℕ):ℝ)*μstar = 0 ; ferme depuis hcw
  linarith [hcw]

/-! #### Caractérisation `excess`/`pot` ⊥ + fermeture + indexation modulaire du cycle

    `excess k v = ⊥` ⟺ `karp_d k v = ⊥` (le match envoie `negInf→⊥`, `ofInt→some`).
    `pot n v ≠ ⊥` ⟺ `∃ k < n, karp_d k v ≠ ⊥` (contrapositive `Finset.sup_eq_bot_iff`).
    Fermeture `c.get 0 = c.get (c.length-1)` (3ᵉ conjoint `isCycle`) + indexation modulaire
    `c.get (j mod m + 1) = c.get ((j+1) mod m)` (`m = c.length-1` arêtes). -/

lemma mod_lt_of (c : List V) (h2 : 2 ≤ c.length) (j : ℕ) :
    j % (c.length - 1) < c.length := by
  have hjm := Nat.mod_lt j (by omega : 0 < c.length - 1); omega

lemma mod_succ_lt_of (c : List V) (h2 : 2 ≤ c.length) (j : ℕ) :
    j % (c.length - 1) + 1 < c.length := by
  have hjm := Nat.mod_lt j (by omega : 0 < c.length - 1); omega

lemma excess_eq_bot_iff (μstar : ℝ) (k : ℕ) (v : V) :
    excess E s μstar k v = (⊥ : WithBot ℝ) ↔ karp_d E s k v = (⊥ : Z_max) := by
  constructor
  · intro h
    by_contra hneg
    obtain ⟨a, ha⟩ : ∃ a, karp_d E s k v = Z_max.ofInt a :=
      Z_max.exists_ofInt_of_ne_bot (karp_d E s k v) hneg
    rw [excess_of_ofInt E s μstar k v a ha] at h
    exact WithBot.coe_ne_bot h
  · intro h
    have hneg : karp_d E s k v = Z_max.negInf := h
    exact excess_of_negInf E s μstar k v hneg

/-- `pot n v ≠ ⊥` ⟺ `∃ k < n, karp_d k v ≠ ⊥` (via `Finset.sup_eq_bot_iff` contrapositive). -/
lemma pot_ne_bot_iff (μstar : ℝ) (n : ℕ) (v : V) :
    pot E s μstar n v ≠ (⊥ : WithBot ℝ) ↔ ∃ k, k < n ∧ karp_d E s k v ≠ (⊥ : Z_max) := by
  constructor
  · intro h
    by_contra hneg; push_neg at hneg
    apply h; unfold pot
    rw [Finset.sup_eq_bot_iff (fun k' => excess E s μstar k' v)]
    intro k' hk'
    exact (excess_eq_bot_iff E s μstar k' v).mpr (hneg k' (Finset.mem_Iio.mp hk'))
  · rintro ⟨k, hklt, hknbot⟩
    unfold pot; intro hbot
    rw [Finset.sup_eq_bot_iff (fun k' => excess E s μstar k' v)] at hbot
    exact hknbot ((excess_eq_bot_iff E s μstar k v).mp (hbot k (Finset.mem_Iio.mpr hklt)))

/- Indexation modulaire : `c.get (j mod m + 1) = c.get ((j+1) mod m)`, `m = c.length - 1`.
    Cas `j mod m < m-1` : `(j+1) mod m = (j mod m) + 1` (`← Nat.mod_add_mod` + `Nat.mod_eq_of_lt`).
    Cas `j mod m = m-1` : `(j mod m)+1 = c.length-1`, `(j+1) mod m = 0` (`Nat.mod_self`), fermeture. -/
lemma cycle_get_mod_succ (c : List V) (h2 : 2 ≤ c.length) (hc : isCycle E c) (j : ℕ) :
    c.get ⟨(j % (c.length - 1)) + 1, mod_succ_lt_of c h2 j⟩ =
      c.get ⟨(j + 1) % (c.length - 1), mod_lt_of c h2 (j + 1)⟩ := by
  have hclose : c.get ⟨0, by omega⟩ = c.get ⟨c.length - 1, by omega⟩ := hc.2.2 hc.1
  have hm : 0 < c.length - 1 := by omega
  have hjm_lt : j % (c.length - 1) < c.length - 1 := Nat.mod_lt j hm
  by_cases hjm : j % (c.length - 1) < c.length - 2
  · have hkey : (j + 1) % (c.length - 1) = (j % (c.length - 1)) + 1 := by
      rw [← Nat.mod_add_mod, Nat.mod_eq_of_lt (by omega)]
    exact get_fin_eq c hkey.symm (mod_lt_of c h2 (j + 1))
  · have hjm_eq : j % (c.length - 1) = c.length - 2 := by omega
    have he1 : (j % (c.length - 1)) + 1 = c.length - 1 := by omega
    have hkey : (j + 1) % (c.length - 1) = 0 := by
      rw [← Nat.mod_add_mod, he1, Nat.mod_self]
    have hL := get_fin_eq c he1 (hi := mod_succ_lt_of c h2 j) (by omega : c.length - 1 < c.length)
    have hR := get_fin_eq c hkey (hi := mod_lt_of c h2 (j + 1)) (by omega : 0 < c.length)
    rw [hL, hR]
    exact hclose.symm

/-! #### B3 arithmétique miroir — `(d_n − n·μ*) ≥ (d_k − k·μ*)` ⟹ `μ* ≤ (d_n − d_k)/(n − k)`

    Recette `per_v_ineq` (cast-then-sub `(n-k:ℝ) = ↑n − ↑k`, linarith-friendly), énoncé en forme
    `≤` (friendly pour `le_div_iff₀`). -/

lemma dirB_arith (μstar : ℝ) (d_n d_k : ℤ) (n k : ℕ) (hk : k < n)
    (hshift : (d_n : ℝ) - (n : ℝ) * μstar ≥ (d_k : ℝ) - (k : ℝ) * μstar) :
    μstar ≤ (d_n - d_k : ℝ) / (n - k : ℝ) := by
  have hnkpos : (0 : ℝ) < (n - k : ℝ) := by
    have hkn : (k : ℝ) < (n : ℝ) := by exact_mod_cast hk
    linarith
  rw [le_div_iff₀ hnkpos]
  linarith [show μstar * (n - k : ℝ) = (n : ℝ) * μstar - (k : ℝ) * μstar from by ring]

/-! #### Fact 5 — pompage (le cœur) : ∃ v*, `e_n(v*) ≥ π(v*)`

    Induction simple sur `L` (nombre d'arêtes pompées) : `e_{k0+L}(c.get(L mod m)) ≥ π(c.get(L mod m))`.
    Base `L=0` : atteinte `π(c[0]) = e_{k0}(c[0])` ⟹ `≥`. Pas `L→L+1` : récurrence `excess_recurrence`
    le long de l'arête `(c.get(L mod m), c.get((L mod m)+1))` (=`c.get((L+1) mod m)` via `cycle_get_mod_succ`)
    + tightness `π(c.get(L mod m)+1) = π(c.get(L mod m)) + shift_w` + monotonie de `+` sur `WithBot ℝ`.
    **PAS de borne supérieure `e_k ≤ π`** : seul le sens `≥` (récurrence + tightness) est utilisé —
    le pompage est purement « lower-bound ». Spécialisation `L = n - k0` (`k0 + (n-k0) = n`) ⟹ `v* = c.get((n-k0) mod m)`.
    `r ≠ 0` ABSORBÉ : `v* = c.get((n-k0) mod m)` atterrit en plein cycle, aucune divisibilité requise.
    Le témoin `v` est exposé dans la conclusion (conjonction d'égalité) pour que l'appelant puisse
    identifier `v*` comme sommet du cycle (requis par `hdn` : `hπfin` à l'indice `(n−k0) mod m`). -/

lemma pump (c : List V) (hc : isCycle E c) (h2 : 2 ≤ c.length) (μstar : ℝ) (n k0 : ℕ)
    (hk0 : k0 < n)
    (htight : ∀ i, (hi : i < c.length - 1) →
      pot E s μstar n (c.get ⟨i + 1, by omega⟩) =
      pot E s μstar n (c.get ⟨i, by omega⟩) +
        shift_w E μstar (c.get ⟨i, by omega⟩, c.get ⟨i + 1, by omega⟩))
    (hatt : pot E s μstar n (c.get ⟨0, by omega⟩) = excess E s μstar k0 (c.get ⟨0, by omega⟩)) :
    ∃ v : V, v = c.get ⟨(n - k0) % (c.length - 1), mod_lt_of c h2 (n - k0)⟩ ∧
      excess E s μstar n v ≥ pot E s μstar n v := by
  have hpump : ∀ L,
      excess E s μstar (k0 + L) (c.get ⟨L % (c.length - 1), mod_lt_of c h2 L⟩) ≥
        pot E s μstar n (c.get ⟨L % (c.length - 1), mod_lt_of c h2 L⟩) := by
    intro L
    induction L with
    | zero =>
      have h0 : 0 % (c.length - 1) = 0 := Nat.zero_mod _
      have hget : c.get ⟨0 % (c.length - 1), mod_lt_of c h2 0⟩ = c.get ⟨0, by omega⟩ :=
        get_fin_eq c h0 (by omega : 0 < c.length)
      rw [hget, Nat.add_zero]
      exact hatt.le
    | succ L ih =>
      have hm : 0 < c.length - 1 := by omega
      have hedge_idx : L % (c.length - 1) < c.length - 1 := Nat.mod_lt L hm
      have he : c.get ⟨(L % (c.length - 1)) + 1, mod_succ_lt_of c h2 L⟩ =
          c.get ⟨(L + 1) % (c.length - 1), mod_lt_of c h2 (L + 1)⟩ :=
        cycle_get_mod_succ E c h2 hc L
      have hrec := excess_recurrence E s μstar (k0 + L)
        (c.get ⟨L % (c.length - 1), mod_lt_of c h2 L⟩)
        (c.get ⟨(L % (c.length - 1)) + 1, mod_succ_lt_of c h2 L⟩)
      rw [he] at hrec
      have hti := htight (L % (c.length - 1)) hedge_idx
      rw [he] at hti
      have hfinal : excess E s μstar ((k0 + L) + 1)
          (c.get ⟨(L + 1) % (c.length - 1), mod_lt_of c h2 (L + 1)⟩) ≥
          pot E s μstar n (c.get ⟨(L + 1) % (c.length - 1), mod_lt_of c h2 (L + 1)⟩) := by
        refine le_trans ?_ hrec.le
        rw [hti]
        exact add_le_add_left ih (shift_w E μstar
          (c.get ⟨L % (c.length - 1), mod_lt_of c h2 L⟩,
           c.get ⟨(L + 1) % (c.length - 1), mod_lt_of c h2 (L + 1)⟩))
      rw [Nat.add_assoc] at hfinal
      exact hfinal
  have hadd : k0 + (n - k0) = n := by omega
  have hL := hpump (n - k0)
  rw [hadd] at hL
  exact ⟨c.get ⟨(n - k0) % (c.length - 1), mod_lt_of c h2 (n - k0)⟩, rfl, hL⟩

/-! #### Fact 4 — tightness sur c* : `π(c[i+1]) = π(c[i]) + shift_w` (télscopique + G_μ_fin(c*)=0)

    Chaque arête du cycle donne `π(c[i+1]) ≥ π(c[i]) + shift_w` (Fact 3 / `edge_ineq`). Somme
    télscopique sur le cycle : `Σ (π(c[i+1]) − π(c[i])) = 0` (fermeture `c[m]=c[0]`) et
    `Σ shift_w = G_μ_fin(c*) = 0` (de `cycleMean(c*) = μ*`, `G_μ_fin_eq_zero_of_cycleMean`). Comme
    chaque terme `d_i := π(c[i+1]) − π(c[i]) − shift_w ≥ 0` et `Σ d_i = 0`, chaque `d_i = 0` ⟹
    égalité (tightness). Couture = soustraction `WithBot ℝ` (pas de `Sub`) : résolue via `hπfin`
    (π fini sur les sommets du cycle ⟹ descente dans ℝ via `unbot` où `Sub` existe). Le `≥` du
    Fact 3 se retourne en `=` par cette finitude. -/

/-- **Somme des `shift_w` sur les arêtes du cycle = `G_μ_fin E μ* c`** (la pièce télscopique de
    la tightness). Sur `Fin (c.length − 1)` (l'index natif de `cycleWeight`) : chaque poids
    d'arête est `ofInt z_i` (`h_finite` + appartenance `hc.2.1`) ⟹
    `Σ_i (toInt w_i − μ*) = Σ_i z_i − m·μ* = toInt(cycleWeight c) − m·μ*`
    (`ofInt_prod_eq_ofInt_sum` : `∏ ofInt z_i = ofInt (Σ z_i)` sur le Finset `Fin m`) ;
    puis `cycleWeight_eq_walkWeightL` ⟹ `= G_μ_fin`. -/
lemma G_μ_fin_eq_sum_shift (c : List V) (hc : isCycle E c) (μstar : ℝ)
    (h_finite : ∀ (p : V × V), p ∈ E.edges → ∃ (z : ℤ), E.weight p = Z_max.ofInt z) :
    (Finset.univ : Finset (Fin (c.length - 1))).sum (fun i =>
      ((E.weight (c.get ⟨i.1, by omega⟩, c.get ⟨i.1 + 1, by omega⟩)).toInt : ℝ) - μstar) =
    G_μ_fin E μstar c := by
  have hlen : 2 ≤ c.length := hc.1
  -- z_i : le poids entier de l'arête i (h_finite + arête du cycle hc.2.1)
  let z : (i : Fin (c.length - 1)) → ℤ := fun i =>
    (h_finite (c.get ⟨i.1, by omega⟩, c.get ⟨i.1 + 1, by omega⟩) (hc.2.1 i.1 i.2)).choose
  -- (1) cycleWeight c = ∏ des poids (def) = ∏ ofInt z_i (congr) = ofInt (Σ z_i) (ofInt_prod_eq_ofInt_sum)
  have hcw1 : cycleWeight E c =
      (Finset.univ : Finset (Fin (c.length - 1))).prod (fun i =>
        E.weight (c.get ⟨i.1, by omega⟩, c.get ⟨i.1 + 1, by omega⟩)) := by
    -- le corps du `dite` de cycleWeight (les `let`/`have` se déplient) est defeq à cette forme
    unfold cycleWeight
    rw [dif_pos hlen]
  have hcw : cycleWeight E c = Z_max.ofInt ((Finset.univ : Finset (Fin (c.length - 1))).sum z) := by
    rw [hcw1]
    rw [← ofInt_prod_eq_ofInt_sum]
    refine Finset.prod_congr rfl ?_
    intro i hi
    exact (h_finite (c.get ⟨i.1, by omega⟩, c.get ⟨i.1 + 1, by omega⟩) (hc.2.1 i.1 i.2)).choose_spec
  -- (2) Σ_i toInt w_i = Σ_i z_i
  have hsum_z : (Finset.univ : Finset (Fin (c.length - 1))).sum
      (fun i => ((E.weight (c.get ⟨i.1, by omega⟩, c.get ⟨i.1 + 1, by omega⟩)).toInt : ℝ)) =
      (Finset.univ : Finset (Fin (c.length - 1))).sum (fun i => (z i : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [show E.weight (c.get ⟨i.1, by omega⟩, c.get ⟨i.1 + 1, by omega⟩) = Z_max.ofInt (z i) from
      (h_finite (c.get ⟨i.1, by omega⟩, c.get ⟨i.1 + 1, by omega⟩) (hc.2.1 i.1 i.2)).choose_spec]
    rw [toInt_ofInt]
  -- (3) Σ_i (toInt w_i − μ*) = Σ_i toInt w_i − m·μ* = toInt(cycleWeight) − m·μ*
  have hsum_shift : (Finset.univ : Finset (Fin (c.length - 1))).sum (fun i =>
      ((E.weight (c.get ⟨i.1, by omega⟩, c.get ⟨i.1 + 1, by omega⟩)).toInt : ℝ) - μstar) =
      ((cycleWeight E c).toInt : ℝ) - ((c.length - 1 : ℕ) : ℝ) * μstar := by
    rw [Finset.sum_sub_distrib]
    rw [hsum_z, hcw, toInt_ofInt]
    -- (Σ (z i : ℝ)) − (∑ _ , μstar) = ((Σ z : ℤ) : ℝ) − m·μ*
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- (4) G_μ_fin E μ* c = toInt(walkWeightL c) − m·μ* = toInt(cycleWeight c) − m·μ*
  rw [hsum_shift]
  show ((cycleWeight E c).toInt : ℝ) - ((c.length - 1 : ℕ) : ℝ) * μstar = G_μ_fin E μstar c
  unfold G_μ_fin
  rw [cycleWeight_eq_walkWeightL E c hc]

/-- **Fact 4 (tightness)** : `π(c[i+1]) = π(c[i]) + shift_w` sur les arêtes du cycle `c*`.
    Descente ℝ (`a_j := unbot π(c[j])`, `s_j := toInt(w(c[j],c[j+1])) − μ*`) : chaque arête
    donne `a(j+1) ≥ a j + s j` (edge_ineq + formes some) ⟹ `d_j := a(j+1) − a j − s j ≥ 0` ;
    `Σ d_j = 0` (télscopage `Finset.sum_range_sub` + fermeture `a_m = a_0` + `Σ s = G_μ(c*) = 0`
    via `G_μ_fin_eq_sum_shift` + `G_μ_fin_eq_zero_of_cycleMean`) ⟹ chaque `d_j = 0`
    (`Finset.sum_eq_zero_iff_of_nonneg`) ⟹ remontée WithBot. -/
lemma tightness (c : List V) (hc : isCycle E c) (h2 : 2 ≤ c.length) (μstar : ℝ) (n : ℕ)
    (hn : 0 < n)
    (h_finite : ∀ (p : V × V), p ∈ E.edges → ∃ (z : ℤ), E.weight p = Z_max.ofInt z)
    (hcm : cycleMean E c = some μstar)
    (hπfin : ∀ i, (hi : i < c.length) →
      pot E s μstar n (c.get ⟨i, by omega⟩) ≠ (⊥ : WithBot ℝ))
    (hFact2 : ∀ w : V, excess E s μstar n w ≤ pot E s μstar n w) :
    ∀ i, (hi : i < c.length - 1) →
      pot E s μstar n (c.get ⟨i + 1, by omega⟩) =
      pot E s μstar n (c.get ⟨i, by omega⟩) +
        shift_w E μstar (c.get ⟨i, by omega⟩, c.get ⟨i + 1, by omega⟩) := by
  intro i hi
  set m := c.length - 1 with hmdef
  -- descente ℝ : a_j = unbot π(c[j]) (0 hors bornes), sw_j = toInt(w(c[j],c[j+1])) − μ* (0 hors bornes)
  let a : ℕ → ℝ := fun j => if hj : j < c.length then
      (pot E s μstar n (c.get ⟨j, hj⟩)).unbot (hπfin j hj) else 0
  let sw : ℕ → ℝ := fun j => if hj : j < c.length - 1 then
      ((E.weight (c.get ⟨j, by omega⟩, c.get ⟨j + 1, by omega⟩)).toInt : ℝ) - μstar else 0
  -- FB-tightness-coe : le bloc `dsimp [a]; rw [dif_pos hj]; exact coe_unbot` ×6 ci-dessous
  have hcoef : ∀ (j : ℕ) (hj : j < c.length),
      (hπ : pot E s μstar n (c.get ⟨j, hj⟩) ≠ (⊥ : WithBot ℝ)) →
      a j = (pot E s μstar n (c.get ⟨j, hj⟩)).unbot hπ →
      (a j : WithBot ℝ) = pot E s μstar n (c.get ⟨j, hj⟩) := by
    intro j hj hπ ha
    rw [ha]
    exact WithBot.coe_unbot _ hπ
  -- (1) fermeture : a_m = a_0 (c[m] = c[0], hc.2.2 hc.1, et m = c.length − 1)
  have hcl : c.get ⟨m, by omega⟩ = c.get ⟨0, by omega⟩ := by
    exact (get_fin_eq c hmdef.symm (by omega : m < c.length)).symm.trans (hc.2.2 hc.1).symm
  have hcoem : (a m : WithBot ℝ) = pot E s μstar n (c.get ⟨m, by omega⟩) := by
    exact hcoef m (by omega) (hπfin m (by omega))
      (by dsimp [a]; rw [dif_pos (by omega : m < c.length)])
  have hcoe0 : (a 0 : WithBot ℝ) = pot E s μstar n (c.get ⟨0, by omega⟩) := by
    exact hcoef 0 (by omega) (hπfin 0 (by omega))
      (by dsimp [a]; rw [dif_pos (by omega : 0 < c.length)])
  have hcoeeq : (a m : WithBot ℝ) = (a 0 : WithBot ℝ) := by
    rw [hcoem, hcl, ← hcoe0]
  have ha_m0 : a m = a 0 := Option.some.inj hcoeeq
  -- (2) Σ_{j < m} sw j = Σ shift_w = G_μ(c*) = 0
  have hsum_s : (Finset.range m).sum sw = 0 := by
    rw [hmdef]
    rw [← Fin.sum_univ_eq_sum_range (f := sw) (n := c.length - 1)]
    have h1 : (Finset.univ : Finset (Fin (c.length - 1))).sum (fun i => sw i.1) =
        (Finset.univ : Finset (Fin (c.length - 1))).sum (fun i =>
          ((E.weight (c.get ⟨i.1, by omega⟩, c.get ⟨i.1 + 1, by omega⟩)).toInt : ℝ) - μstar) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      dsimp [sw]
      rw [dif_pos j.2]
    rw [h1, G_μ_fin_eq_sum_shift E c hc μstar h_finite, G_μ_fin_eq_zero_of_cycleMean E c hc μstar hcm]
  -- (3) par arête j < m : π(c[j+1]) ≥ π(c[j]) + shift_w (edge_ineq) ⟹ d_j ≥ 0
  have hd : ∀ j ∈ Finset.range m, 0 ≤ a (j+1) - a j - sw j := by
    intro j hj
    have hjm : j < c.length - 1 := by
      rw [hmdef] at hj
      exact Finset.mem_range.mp hj
    have hπj : pot E s μstar n (c.get ⟨j, by omega⟩) ≠ (⊥ : WithBot ℝ) := hπfin j (by omega)
    have hπj1 : pot E s μstar n (c.get ⟨j + 1, by omega⟩) ≠ (⊥ : WithBot ℝ) := hπfin (j + 1) (by omega)
    have hedge_mem : (c.get ⟨j, by omega⟩, c.get ⟨j + 1, by omega⟩) ∈ E.edges := by
      show (c.get ⟨j, _⟩, c.get ⟨j + 1, _⟩) ∈ E.edges
      exact hc.2.1 j hjm
    obtain ⟨z, hz⟩ := h_finite (c.get ⟨j, by omega⟩, c.get ⟨j + 1, by omega⟩) hedge_mem
    have hsw : shift_w E μstar (c.get ⟨j, by omega⟩, c.get ⟨j + 1, by omega⟩) =
        WithBot.some (((z : ℤ) : ℝ) - μstar) :=
      shift_w_of_ofInt E μstar (c.get ⟨j, by omega⟩, c.get ⟨j + 1, by omega⟩) z hz
    have hE := edge_ineq E s μstar n (c.get ⟨j, by omega⟩) (c.get ⟨j + 1, by omega⟩) hn hFact2
    have hcoej : (a j : WithBot ℝ) = pot E s μstar n (c.get ⟨j, by omega⟩) := by
      exact hcoef j (by omega) (hπfin j (by omega))
        (by dsimp [a]; rw [dif_pos (by omega : j < c.length)])
    have hcoej1 : (a (j+1) : WithBot ℝ) = pot E s μstar n (c.get ⟨j + 1, by omega⟩) := by
      exact hcoef (j+1) (by omega) (hπfin (j + 1) (by omega))
        (by dsimp [a]; rw [dif_pos (by omega : j + 1 < c.length)])
    have hcoes : (sw j : WithBot ℝ) = WithBot.some (((z : ℤ) : ℝ) - μstar) := by
      dsimp [sw]
      rw [dif_pos hjm]
      show WithBot.some (((E.weight (c.get ⟨j, _⟩, c.get ⟨j + 1, _⟩)).toInt : ℝ) - μstar) =
        WithBot.some (((z : ℤ) : ℝ) - μstar)
      rw [hz, toInt_ofInt]
    have hsw_j : sw j = ((z : ℤ) : ℝ) - μstar := Option.some.inj hcoes
    have hE0 : (a (j+1) : WithBot ℝ) ≥
        (a j : WithBot ℝ) + shift_w E μstar (c.get ⟨j, by omega⟩, c.get ⟨j + 1, by omega⟩) := by
      rw [hcoej1, hcoej]
      exact hE
    have hE' : a (j+1) ≥ a j + (((z : ℤ) : ℝ) - μstar) := by
      rw [hsw] at hE0
      have hE0' : WithBot.some (a j + (((z : ℤ) : ℝ) - μstar)) ≤ (a (j+1) : WithBot ℝ) := by
        rw [show WithBot.some (a j + (((z : ℤ) : ℝ) - μstar)) =
            (a j : WithBot ℝ) + WithBot.some (((z : ℤ) : ℝ) - μstar) from rfl]
        exact hE0
      exact WithBot.coe_le_coe.mp hE0'
    rw [hsw_j]
    linarith [hE']
  -- (4) Σ d_j = 0 (télscopage + fermeture + Σ sw = 0)
  have hsum0 : (Finset.range m).sum (fun j => a (j+1) - a j - sw j) = 0 := by
    rw [Finset.sum_sub_distrib (fun j => a (j+1) - a j) sw]
    rw [Finset.sum_range_sub]
    rw [ha_m0]
    rw [hsum_s]
    ring
  -- (5) chaque d_j = 0 (Finset.sum_eq_zero_iff_of_nonneg) ; à l'indice i : a(i+1) = a i + sw i
  have hall : ∀ j ∈ Finset.range m, a (j+1) - a j - sw j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.range m) (f := fun j => a (j+1) - a j - sw j) hd).mp hsum0
  have hi_m : i < m := by rw [hmdef]; exact hi
  have hdi : a (i+1) - a i - sw i = 0 := hall i (Finset.mem_range.mpr hi_m)
  have hEq : a (i+1) = a i + sw i := by linarith
  -- (6) remontée WithBot à l'indice i
  have hπi1 : pot E s μstar n (c.get ⟨i + 1, by omega⟩) ≠ (⊥ : WithBot ℝ) := hπfin (i + 1) (by omega)
  have hπi : pot E s μstar n (c.get ⟨i, by omega⟩) ≠ (⊥ : WithBot ℝ) := hπfin i (by omega)
  have hcoei1 : (a (i+1) : WithBot ℝ) = pot E s μstar n (c.get ⟨i + 1, by omega⟩) := by
    exact hcoef (i+1) (by omega) (hπfin (i + 1) (by omega))
      (by dsimp [a]; rw [dif_pos (by omega : i + 1 < c.length)])
  have hcoei : (a i : WithBot ℝ) = pot E s μstar n (c.get ⟨i, by omega⟩) := by
    exact hcoef i (by omega) (hπfin i (by omega))
      (by dsimp [a]; rw [dif_pos (by omega : i < c.length)])
  have hedge_mem : (c.get ⟨i, by omega⟩, c.get ⟨i + 1, by omega⟩) ∈ E.edges := by
    show (c.get ⟨i, _⟩, c.get ⟨i + 1, _⟩) ∈ E.edges
    exact hc.2.1 i hi
  obtain ⟨z, hz⟩ := h_finite (c.get ⟨i, by omega⟩, c.get ⟨i + 1, by omega⟩) hedge_mem
  have hsw_i : sw i = ((z : ℤ) : ℝ) - μstar := by
    dsimp [sw]
    rw [dif_pos hi]
    show ((E.weight (c.get ⟨i, _⟩, c.get ⟨i + 1, _⟩)).toInt : ℝ) - μstar = ((z : ℤ) : ℝ) - μstar
    rw [hz, toInt_ofInt]
  have hsw : shift_w E μstar (c.get ⟨i, by omega⟩, c.get ⟨i + 1, by omega⟩) =
      WithBot.some (((z : ℤ) : ℝ) - μstar) :=
    shift_w_of_ofInt E μstar (c.get ⟨i, by omega⟩, c.get ⟨i + 1, by omega⟩) z hz
  rw [← hcoei1, ← hcoei, hsw]
  rw [show WithBot.some (a i) + WithBot.some (((z : ℤ) : ℝ) - μstar) =
      WithBot.some (a i + (((z : ℤ) : ℝ) - μstar)) from rfl]
  exact congrArg WithBot.some (by linarith [hEq, hsw_i])

/-! #### Conclusion arithmétique (sorry-free) : `μ* ≤ (d_n − d_k)/(n−k)` depuis `e_n(v*) ≥ π(v*)`

    Miroir B de `per_v_ineq` (Dir A) au sens opposé : Dir A prouvait `(d_n−d_k)/(n−k) ≤ μ*`
    (Karp min_k ≤ μ*), ici `μ* ≤ (d_n−d_k)/(n−k)` (μ* ≤ chaque terme ⟹ μ* ≤ l'inf'). Recette
    `dirB_arith` (cast-then-sub `(n−k:ℝ) = ↑n − ↑k`, linarith-friendly). `e_n(v*) ≥ π(v*) ≥ e_k(v*)`
    (pump + `excess_le_pot`) ⟹ `some(n_val − n·μ*) ≥ some(k_val − k·μ*)` ⟹ `μ* ≤ ratio`. -/

lemma per_k_ineq (μstar : ℝ) (n : ℕ) (vstar : V) (n_val : ℤ)
    (hdn : karp_d E s n vstar = Z_max.ofInt n_val)
    (hge : excess E s μstar n vstar ≥ pot E s μstar n vstar) :
    ∀ k, (hk : k < n) → ∀ k_val, karp_d E s k vstar = Z_max.ofInt k_val →
      μstar ≤ ((n_val - k_val : ℝ) / (n - k : ℝ)) := by
  intro k hk k_val hkv
  have hle_k : excess E s μstar k vstar ≤ pot E s μstar n vstar :=
    excess_le_pot E s μstar n k vstar hk
  have hge_k : excess E s μstar k vstar ≤ excess E s μstar n vstar := hle_k.trans hge
  have hex_n : excess E s μstar n vstar = WithBot.some ((n_val : ℝ) - (n : ℝ) * μstar) :=
    excess_of_ofInt E s μstar n vstar n_val hdn
  have hex_k : excess E s μstar k vstar = WithBot.some ((k_val : ℝ) - (k : ℝ) * μstar) :=
    excess_of_ofInt E s μstar k vstar k_val hkv
  rw [hex_n, hex_k] at hge_k
  exact dirB_arith μstar n_val k_val n k hk (WithBot.coe_le_coe.mp hge_k)

/-! #### Queue B (miroir de `per_v_ineq`) : `e_n(v) ≤ e_k(v)` via retrait d'un cycle de mean ≤ μ*

    Dir A prouvait `(d_n−d_k)/(n−k) ≤ μ*` (per_v_ineq) ; ici la n-marche argmax raccourcie en
    k-marche par retrait du cycle simple `c` de mean ≤ μ* donne `e_n = e_k + G_μ(c) ≤ e_k` :
    additivité G_μ (`hadd`) + `hgc : G_μ(c) ≤ 0` ⟹ `n_val − n·μ* ≤ w' − k·μ* ≤ k_val − k·μ*`
    (w' = poids de l' ≤ d_k via `hge`). Recette `per_v_ineq` (cast-then-sub, linarith-friendly). -/

lemma excess_n_le_excess_k (μstar : ℝ) (n : ℕ) (v : V) (n_val : ℤ)
    (l l' c : List V) (k : ℕ) (k_val : ℤ)
    (hdn : karp_d E s n v = Z_max.ofInt n_val)
    (hgc : G_μ_fin E μstar c ≤ 0)
    (hadd : G_μ_fin E μstar l = G_μ_fin E μstar l' + G_μ_fin E μstar c)
    (hwl : walkWeightL E l = ofInt n_val)
    (hww : walkWeightL E l = walkWeightL E l' * walkWeightL E c)
    (hlen : l.length = n + 1) (hl'len : l'.length = k + 1)
    (hkdk : karp_d E s k v = ofInt k_val)
    (hge : karp_d E s k v ≥ walkWeightL E l')
    (hklt : k < n) :
    excess E s μstar n v ≤ excess E s μstar k v := by
  -- (a) walkWeightL E l' est fini (⊥ absorbant depuis hww + hwl) → ofInt w'
  have hl'ne : walkWeightL E l' ≠ (0 : Z_max) := by
    intro h
    apply Z_max.ofInt_ne_bot n_val
    rw [← hwl, hww, h]; exact Z_max.zero_mul _
  obtain ⟨w', hw'⟩ : ∃ w', walkWeightL E l' = ofInt w' :=
    Z_max.exists_ofInt_of_ne_bot (walkWeightL E l') hl'ne
  -- (b) d_k(v) = ofInt k_val ≥ ofInt w' (témoin) → w' ≤ k_val
  have hkw : (w' : ℤ) ≤ k_val := by
    have hh : ofInt w' ≤ ofInt k_val := by
      have := hge; rw [hkdk, hw'] at this; exact this
    exact (Z_max.ofInt_le_iff w' k_val).mp hh
  -- (c) G_μ(l) = n_val − n·μ* , G_μ(l') = w' − k·μ*
  have hlen1 : (l.length - 1 : ℕ) = n := by omega
  have hl'lenk : (l'.length - 1 : ℕ) = k := by omega
  have hGl : G_μ_fin E μstar l = ((n_val : ℝ) - (n : ℝ) * μstar) := by
    rw [G_μ_fin_of_ofInt E μstar l n_val hwl, hlen1]
  have hGl' : G_μ_fin E μstar l' = ((w' : ℝ) - (k : ℝ) * μstar) := by
    rw [G_μ_fin_of_ofInt E μstar l' w' hw', hl'lenk]
  -- (d) G_μ(c) ≤ 0 ⟹ G_μ(l) ≤ G_μ(l') ⟹ n_val − n·μ* ≤ w' − k·μ* ≤ k_val − k·μ*
  have hle : G_μ_fin E μstar l ≤ G_μ_fin E μstar l' := by rw [hadd]; linarith
  have h1 : (n_val : ℝ) - (n : ℝ) * μstar ≤ (w' : ℝ) - (k : ℝ) * μstar := by
    have := hle; rw [hGl, hGl'] at this
    linarith
  have hkwR : (w' : ℝ) ≤ (k_val : ℝ) := by exact_mod_cast hkw
  have h2 : (n_val : ℝ) - (n : ℝ) * μstar ≤ (k_val : ℝ) - (k : ℝ) * μstar := by
    linarith
  -- (e) conclusion : some(n_val − n·μ*) ≤ some(k_val − k·μ*) ⟺ e_n ≤ e_k
  have hex_n : excess E s μstar n v = WithBot.some ((n_val : ℝ) - (n : ℝ) * μstar) :=
    excess_of_ofInt E s μstar n v n_val hdn
  have hex_k : excess E s μstar k v = WithBot.some ((k_val : ℝ) - (k : ℝ) * μstar) :=
    excess_of_ofInt E s μstar k v k_val hkdk
  rw [hex_n, hex_k]
  exact WithBot.coe_le_coe.mpr h2

/-! #### P5 — atteignabilité : `d_k(v) ≠ ⊥` ⟹ `∃ k' < |V|`, `d_{k'}(v) ≠ ⊥` (retrait de cycle itéré)

    Le chemin argmax de longueur `k` (A2) est raccourci par retrait de cycle tant que `|V| ≤ k`
    (pigeonhole : une marche de longueur `k` a `k+1` sommets > `|V|` ⟹ sommet répété `l[i] = l[j]`).
    À chaque itération la longueur décroît strictement et le poids reste fini (⊥ absorbant pour
    `*`), donc par récurrence forte on atteint `k' < |V|`. Un seul retrait ne suffit pas (le
    raccourci peut rester ≥ |V|). Cas dégénéré (`j+1 = l.length`, le sommet répété est l'extrémité
    `v`, `path_shorten_weight_last`) et non-dégénéré (`path_shorten_weight`). Pas de `h_edge`
    requis (la finitude se transmet par absorbant `Z_max.zero_mul`/`mul_zero`). -/

lemma karp_d_ne_bot_lt_card {V : Type*} [Fintype V] [DecidableEq V] (E : EdgeSet V) (s v : V)
    (k : ℕ) (hk : karp_d E s k v ≠ (⊥ : Z_max)) :
    ∃ k' : ℕ, k' < Fintype.card V ∧ karp_d E s k' v ≠ (⊥ : Z_max) := by
  -- récurrence forte avec la condition `karp_d ≠ ⊥` dans le motive (le pas kk exige `d_kk ≠ ⊥`)
  refine Nat.strongRecOn (motive := fun n => karp_d E s n v ≠ (⊥ : Z_max) →
      ∃ k' : ℕ, k' < Fintype.card V ∧ karp_d E s k' v ≠ (⊥ : Z_max)) k (fun kk ih => ?_) hk
  intro hkk
  by_cases hklt : kk < Fintype.card V
  · exact ⟨kk, hklt, hkk⟩
  · -- |V| ≤ kk : marche argmax de longueur kk (A2), pigeonhole (sommet répété), retrait de cycle
    obtain ⟨f, hf0, hflast, hfw⟩ := exists_path_weight_eq_karp_d E s kk v hkk
    set l := List.ofFn f with hldef
    have hlen : l.length = kk + 1 := by rw [hldef, List.length_ofFn]
    have hwl_ne : walkWeightL E l ≠ (⊥ : Z_max) := by
      rw [hldef, ← walkWeight_eq_walkWeightL E kk f, hfw]
      exact hkk
    have hl0p : 0 < l.length := by omega
    have hl0 : l.get ⟨0, hl0p⟩ = s := by
      show (List.ofFn f).get ⟨0, hl0p⟩ = s
      rw [List.get_ofFn]
      exact (congrArg f (Fin.eq_of_val_eq rfl) : f _ = f (0 : Fin (kk + 1))).trans hf0
    have hlnp : kk < l.length := by omega
    have hln : l.get ⟨kk, hlnp⟩ = v := by
      show (List.ofFn f).get ⟨kk, hlnp⟩ = v
      rw [List.get_ofFn]
      exact (congrArg f (Fin.eq_of_val_eq rfl) : f _ = f (Fin.last kk)).trans hflast
    have hcard : Fintype.card V < l.length := by rw [hlen]; omega
    obtain ⟨i, j, hi, hj, hij, heq⟩ := exists_repeated_of_length_gt_card l hcard
    by_cases hj1 : j + 1 < l.length
    · -- NON-dégénéré : k' = l'.length − 1 < k, l' = take(i+1) ++ drop(j+1)  (FB-Queue)
      obtain ⟨k', l', hl'0, hl'k, hl'len0, hl'len', hl's, hl'v, hge, hww⟩ :=
        produce_shortened_walk E s v l kk i j hi hj hij heq hj1 hl0p hl0 hlen hlnp hln
      have hk'ltk : k' < kk := by omega
      have hk'ne : karp_d E s k' v ≠ (⊥ : Z_max) := by
        have hl'f : walkWeightL E l' ≠ (⊥ : Z_max) := by
          intro h; apply hwl_ne; rw [hww, h]; exact Z_max.zero_mul _
        intro hb; rw [hb] at hge
        exact hl'f (le_antisymm hge bot_le)
      exact ih k' hk'ltk hk'ne
    · -- DÉGÉNÉRÉ : j+1 = l.length (le sommet répété est l'extrémité v), k' = i, l' = take(i+1)
      have hj1eq : j + 1 = l.length := by omega
      obtain ⟨l', hl'0, hl'k, hl'len', hl's, hl'v, hge, hww⟩ :=
        produce_shortened_walk_last E s v l kk i j hi hj hij heq hj1eq hl0p hl0 hlen hlnp hln
      have hk'ne : karp_d E s i v ≠ (⊥ : Z_max) := by
        have hl'f : walkWeightL E l' ≠ (⊥ : Z_max) := by
          intro h; apply hwl_ne; rw [hww, h]; exact Z_max.zero_mul _
        intro hb; rw [hb] at hge
        exact hl'f (le_antisymm hge bot_le)
      have hilt : i < kk := by omega
      exact ih i hilt hk'ne

/-! #### B1 local — `maxCycleMeanSimple E ≠ ⊥ ⟹ ∃ c* simple, cycleMean c* = maxCycleMeanSimple E`

    Atteinte du sup sur `Finset (SimpleCycle E)` (Finset fini). Contrapositive `sup_eq_bot_iff` :
    `maxCycleMeanSimple ≠ ⊥ ⟹ ∃ c, cycleMean c ≠ ⊥` ⟹ `Nonempty (SimpleCycle E)` ⟹
    `Finset.exists_mem_eq_sup` donne le témoin `c*` avec `cycleMean c* = sup = maxCycleMeanSimple`. -/

lemma exists_simple_cycle_eq_max (hpos : maxCycleMeanSimple E ≠ (⊥ : WithBot ℝ)) :
    ∃ (c : SimpleCycle E), cycleMean E (↑c) = maxCycleMeanSimple E := by
  have hex_ne : ∃ c : SimpleCycle E, cycleMean E (↑c) ≠ (⊥ : WithBot ℝ) := by
    by_contra hneg
    apply hpos
    show maxCycleMeanSimple E = (⊥ : WithBot ℝ)
    unfold maxCycleMeanSimple
    simp only [Finset.sup_eq_bot_iff, Finset.mem_univ, true_implies]
    intro c
    by_contra hcne
    exact hneg ⟨c, hcne⟩
  obtain ⟨c, _⟩ := hex_ne
  have hnonempty : (Finset.univ : Finset (SimpleCycle E)).Nonempty := ⟨c, Finset.mem_univ c⟩
  obtain ⟨cstar, hcmem, hceq⟩ :=
    Finset.exists_mem_eq_sup (s := Finset.univ) hnonempty (f := fun c => cycleMean E (↑c))
  exact ⟨cstar, hceq.symm⟩

/-! #### Direction B2 — assemblage top-level `maxCycleMeanSimple ≤ maxCycleMeanKarp`

    Cible via C1 : `maxCycleMeanKarp_ge_sSup` (ci-dessous). Décomposition : B1 (témoin `c*`,
    `exists_simple_cycle_eq_max`, sorry-free) → extraction `μ*` (`WithBot.ne_bot_iff_exists`,
    sorry-free) → `hnpos` (V non-vide) → Dir A port `hFact2` (pigeonhole, sorry) → `hπfin`
    (atteignabilité+pigeon, sorry) → `pot_attained` + `pump` (CŒUR, sorry-free) → `tightness`
    (Fact 4, sorry) → `hdn` reachability (sorry, déduit de hπfin+hpump+excess_eq_bot_iff) →
    `per_k_ineq` (sorry-free) → `hle` inf'/sup lifting (sorry, miroir Dir A) → trans. Le CŒUR
    nouveau (pump) est sorry-free + axiom-clean ; les sorries = machinery Dir A + couture WithBot
    (soustraction télscopique, dépliage inf'/sup). -/

theorem maxCycleMeanSimple_le_maxCycleMeanKarp
    (h_edge : ∀ (p : V × V), p ∉ E.edges → E.weight p = (0 : Z_max))
    (h_finite : ∀ (p : V × V), p ∈ E.edges → ∃ (z : ℤ), E.weight p = Z_max.ofInt z)
    (h_irred : Irreducible E) :
    maxCycleMeanSimple E ≤ maxCycleMeanKarp E := by
  by_cases hpos : maxCycleMeanSimple E = (⊥ : WithBot ℝ)
  · rw [hpos]; exact bot_le
  · -- B1 : témoin cycle simple c* avec cycleMean c* = maxCycleMeanSimple
    obtain ⟨cstar, hceq⟩ := exists_simple_cycle_eq_max E hpos
    set c := cstar.val with hcdef
    have hc : isCycle E c := cstar.2.1
    have h2 : 2 ≤ c.length := hc.1
    have hcm : cycleMean E c = maxCycleMeanSimple E := hceq
    have hcm_ne : cycleMean E c ≠ (⊥ : WithBot ℝ) := hcm ▸ hpos
    obtain ⟨μstar, hμ⟩ := WithBot.ne_bot_iff_exists.mp hcm_ne
    have hcm_μ : cycleMean E c = some μstar := hμ.symm
    -- n = |V| > 0 (B1 témoin ⟹ V non-vide)
    have hnpos : 0 < Fintype.card V := by
      exact Fintype.card_pos_iff.mpr ⟨c.get ⟨0, by omega⟩⟩
    haveI : Nonempty V := Fintype.card_pos_iff.mp hnpos
    set s := Classical.arbitrary V with hs
    set n := Fintype.card V with hn
    -- Dir A port : e_n(v) ≤ π(v) pour tout v (pigeonhole n-marche + cycleMean ≤ μ*, cf. A5)
    have hFact2 : ∀ w : V, excess E s μstar n w ≤ pot E s μstar n w := by
      intro w
      by_cases hdn_bot : karp_d E s n w = (⊥ : Z_max)
      · -- d_n(w) = ⊥ : e_n(w) = ⊥ ≤ π(w)
        rw [excess_of_negInf E s μstar n w hdn_bot]
        exact bot_le
      · -- d_n(w) = ofInt n_val : marche argmax de longueur n (A2), pigeonhole, retrait de cycle
        obtain ⟨n_val, hdn⟩ := Z_max.exists_ofInt_of_ne_bot (karp_d E s n w) hdn_bot
        obtain ⟨f, hf0, hflast, hfw⟩ := exists_path_weight_eq_karp_d E s n w hdn_bot
        set l := List.ofFn f with hldef
        have hlen : l.length = n + 1 := by rw [hldef, List.length_ofFn]
        have hwl : walkWeightL E l = ofInt n_val := by
          rw [hldef, ← walkWeight_eq_walkWeightL E n f, hfw, hdn]
        have hwl_ne : walkWeightL E l ≠ (⊥ : Z_max) := by rw [hwl]; exact Z_max.ofInt_ne_bot n_val
        have hwalk : IsWalk E l := walkWeightL_finite_imp_isWalk E h_edge l hwl_ne
        -- extrémités : l[0] = s, l[n] = w
        have hl0p : 0 < l.length := by omega
        have hl0 : l.get ⟨0, hl0p⟩ = s := by
          show (List.ofFn f).get ⟨0, hl0p⟩ = s
          rw [List.get_ofFn]
          exact (congrArg f (Fin.eq_of_val_eq rfl) : f _ = f (0 : Fin (n + 1))).trans hf0
        have hlnp : n < l.length := by omega
        have hln : l.get ⟨n, hlnp⟩ = w := by
          show (List.ofFn f).get ⟨n, hlnp⟩ = w
          rw [List.get_ofFn]
          exact (congrArg f (Fin.eq_of_val_eq rfl) : f _ = f (Fin.last n)).trans hflast
        -- pigeonhole : premier-repeat (i, j) ⟹ cycle SIMPLE extrait
        have hcard : Fintype.card V < l.length := by rw [hlen, hn]; omega
        obtain ⟨i, j, hi, hj, hij, heq, hjnodup⟩ := exists_first_repeat l hcard
        have hcyc : isCycle E ((l.drop i).take (j - i + 1)) :=
          cycle_from_repeated E l i j hi hj hij heq hwalk
        have hsc : isSimpleCycle E ((l.drop i).take (j - i + 1)) :=
          simple_cycle_of_first_repeat E l hwalk i j hi hj hij heq hjnodup
        -- μ* = maxCycleMeanSimple ; mean c' ≤ μ* ⟹ G_μ(c') ≤ 0 (pont cycleMean)
        have hμstar_simple : (↑μstar : WithBot ℝ) = maxCycleMeanSimple E := hμ.trans hcm
        have hcm' : cycleMean E ((l.drop i).take (j - i + 1)) ≤ (↑μstar : WithBot ℝ) :=
          (cycleMean_le_max E hsc).trans hμstar_simple.symm.le
        have hgc : G_μ_fin E μstar ((l.drop i).take (j - i + 1)) ≤ 0 := by
          rw [← G_μ_fin_cycle_nonpos E ((l.drop i).take (j - i + 1)) hcyc μstar]
          exact hcm'
        -- dégénéré (j+1 = l.length) vs non-dégénéré (j+1 < l.length)
        by_cases hj1 : j + 1 < l.length
        · -- NON-dégénéré : k' = l'.length − 1, l' = take(i+1) ++ drop(j+1)  (FB-Queue)
          obtain ⟨k, l', hl'0, hl'k, hl'len0, hl'len, hl's, hl'v, hge, hww⟩ :=
            produce_shortened_walk E s w l n i j hi hj hij heq hj1 hl0p hl0 hlen hlnp hln
          have hklt : k < n := by omega
          have hadd : G_μ_fin E μstar l =
              G_μ_fin E μstar l' + G_μ_fin E μstar ((l.drop i).take (j - i + 1)) := by
            refine G_μ_fin_add_general E μstar l l' ((l.drop i).take (j - i + 1)) hww hwl_ne ?_
            have hclen : ((l.drop i).take (j - i + 1)).length = j - i + 1 := by
              rw [List.length_take, List.length_drop,
                  min_eq_left (by omega : (j - i + 1) ≤ l.length - i)]
            rw [hl'len, hclen]; omega
          cases hkdk : karp_d E s k w with
          | negInf =>
            exfalso
            rw [hkdk] at hge
            have hl'bot : walkWeightL E l' = (⊥ : Z_max) := le_antisymm hge bot_le
            exact Z_max.ofInt_ne_bot n_val (by rw [← hwl, hww, hl'bot]; exact Z_max.zero_mul _)
          | ofInt k_val =>
            exact (excess_n_le_excess_k E s μstar n w n_val l l' ((l.drop i).take (j - i + 1))
              k k_val hdn hgc hadd hwl hww hlen hl'len hkdk hge hklt).trans
              (excess_le_pot E s μstar n k w hklt)
        · -- DÉGÉNÉRÉ : j+1 = l.length, k = i, l' = take(i+1)  (FB-Queue)
          have hj1eq : j + 1 = l.length := by omega
          have hklt : i < n := by omega
          obtain ⟨l', hl'0, hl'k, hl'len, hl's, hl'v, hge, hww⟩ :=
            produce_shortened_walk_last E s w l n i j hi hj hij heq hj1eq hl0p hl0 hlen hlnp hln
          have hadd : G_μ_fin E μstar l =
              G_μ_fin E μstar l' + G_μ_fin E μstar ((l.drop i).take (j - i + 1)) := by
            refine G_μ_fin_add_general E μstar l l' ((l.drop i).take (j - i + 1)) hww hwl_ne ?_
            have hclen : ((l.drop i).take (j - i + 1)).length = j - i + 1 := by
              rw [List.length_take, List.length_drop,
                  min_eq_left (by omega : (j - i + 1) ≤ l.length - i)]
            rw [hl'len, hclen]; omega
          cases hkdk : karp_d E s i w with
          | negInf =>
            exfalso
            rw [hkdk] at hge
            have hl'bot : walkWeightL E l' = (⊥ : Z_max) := le_antisymm hge bot_le
            exact Z_max.ofInt_ne_bot n_val (by rw [← hwl, hww, hl'bot]; exact Z_max.zero_mul _)
          | ofInt k_val =>
            exact (excess_n_le_excess_k E s μstar n w n_val l l' ((l.drop i).take (j - i + 1))
              i k_val hdn hgc hadd hwl hww hlen hl'len hkdk hge hklt).trans
              (excess_le_pot E s μstar n i w hklt)
    -- Atteignabilité : π(c[i]) fini pour les sommets du cycle (reachability + pigeonhole)
    have hπfin : ∀ i, (hi : i < c.length) →
        pot E s μstar n (c.get ⟨i, by omega⟩) ≠ (⊥ : WithBot ℝ) := by
      intro i hi
      -- h_irred : s atteint c[i] ⟹ d_k(c[i]) ≠ ⊥ pour un k ; raccourcir à k' < |V| = n
      obtain ⟨k, hkne⟩ := h_irred s (c.get ⟨i, by omega⟩)
      obtain ⟨k', hk'lt, hk'ne⟩ := karp_d_ne_bot_lt_card E s (c.get ⟨i, by omega⟩) k hkne
      have hk'ltn : k' < n := by rw [hn]; exact hk'lt
      exact (pot_ne_bot_iff E s μstar n (c.get ⟨i, by omega⟩)).mpr ⟨k', hk'ltn, hk'ne⟩
    -- CŒUR (sorry-free) : atteinte π(c[0]) = e_{k0}(c[0]), pompage ⟹ ∃ v*, e_n(v*) ≥ π(v*)
    obtain ⟨k0, hk0, hk0eq⟩ := pot_attained E s μstar n (c.get ⟨0, by omega⟩) hnpos
    have htight : ∀ i, (hi : i < c.length - 1) →
        pot E s μstar n (c.get ⟨i + 1, by omega⟩) =
        pot E s μstar n (c.get ⟨i, by omega⟩) +
          shift_w E μstar (c.get ⟨i, by omega⟩, c.get ⟨i + 1, by omega⟩) :=
      tightness E s c hc h2 μstar n hnpos h_finite hcm_μ hπfin hFact2
    obtain ⟨vstar, hvstar, hpump⟩ := pump E s c hc h2 μstar n k0 hk0 htight hk0eq
    -- v* = c.get ((n−k0) mod (c.length−1)) est un sommet du cycle ⟹ π(v*) ≠ ⊥ (hπfin à cet indice)
    have hπvstar : pot E s μstar n vstar ≠ (⊥ : WithBot ℝ) := by
      have hvstar_idx : pot E s μstar n
          (c.get ⟨(n - k0) % (c.length - 1), mod_lt_of c h2 (n - k0)⟩) ≠ (⊥ : WithBot ℝ) :=
        hπfin ((n - k0) % (c.length - 1)) (mod_lt_of c h2 (n - k0))
      exact hvstar.symm ▸ hvstar_idx
    -- hpump : excess n v* ≥ π(v*) ≠ ⊥ ⟹ d_n(v*) fini (excess_eq_bot_iff + decode F3)
    have hdn : ∃ n_val, karp_d E s n vstar = Z_max.ofInt n_val := by
      -- hpump : excess n v* ≥ π(v*) ≠ ⊥ ⟹ excess n v* ≠ ⊥
      have hexcess_ne : excess E s μstar n vstar ≠ (⊥ : WithBot ℝ) := by
        intro hex_bot
        have hpb : pot E s μstar n vstar ≤ (⊥ : WithBot ℝ) := by
          rw [← hex_bot]
          exact hpump
        exact hπvstar (le_bot_iff.mp hpb)
      -- excess n v* ≠ ⊥ ⟹ karp_d n v* ≠ ⊥ (excess_eq_bot_iff) ⟹ décode Z_max (helper F3)
      have hkarp_ne : karp_d E s n vstar ≠ (⊥ : Z_max) := by
        intro hb
        apply hexcess_ne
        exact (excess_eq_bot_iff E s μstar n vstar).mpr hb
      exact Z_max.exists_ofInt_of_ne_bot (karp_d E s n vstar) hkarp_ne
    obtain ⟨n_val, hdn⟩ := hdn
    -- Conclusion arith (sorry-free) : μ* ≤ (d_n − d_k)/(n−k) ∀ k < n à d_k(v*) fini
    have hperk : ∀ k, (hk : k < n) → ∀ k_val,
        karp_d E s k vstar = Z_max.ofInt k_val →
          μstar ≤ ((n_val - k_val : ℝ) / (n - k : ℝ)) :=
      per_k_ineq E s μstar n vstar n_val hdn hpump
    -- Lifting WithBot + inf'/sup (miroir Dir A L1750) : some μ* ≤ maxCycleMeanKarp E
    have hle : (↑μstar : WithBot ℝ) ≤ maxCycleMeanKarp E := by
      unfold maxCycleMeanKarp
      split
      · -- isTrue : 0 < card V — dépliage sup_v, témoin v*
        dsimp only
        rw [← hs, ← hn]
        refine le_trans ?_ (Finset.le_sup (Finset.mem_univ vstar))
        -- cas d_n(v*) : ofInt n_val (hdn) ⟹ branche finie ; ks non-vide via π(v*) ≠ ⊥
        rw [hdn]
        dsimp only
        have hks_ne : ((Finset.Iio n).filter (fun k => karp_d E s k vstar ≠ (⊥ : Z_max))).Nonempty := by
          obtain ⟨k, hklt, hknbot⟩ := (pot_ne_bot_iff E s μstar n vstar).mp hπvstar
          exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Iio.mpr hklt, hknbot⟩⟩
        rw [dif_pos hks_ne]
        rw [Finset.le_inf'_iff]
        intro k hkks
        have hkIio : k ∈ Finset.Iio n := (Finset.mem_filter.mp hkks).1
        have hknbot : karp_d E s k vstar ≠ (⊥ : Z_max) := (Finset.mem_filter.mp hkks).2
        have hklt : k < n := Finset.mem_Iio.mp hkIio
        obtain ⟨k_val, hkv⟩ := Z_max.exists_ofInt_of_ne_bot (karp_d E s k vstar) hknbot
        rw [hkv]
        exact WithBot.coe_le_coe.mpr (hperk k hklt k_val hkv)
      · -- isFalse : ¬ 0 < card V — contradictoire (hnpos)
        rename_i hnot
        exact (hnot hnpos).elim
    -- maxCycleMeanSimple E = ↑μ* (hcm.symm.trans hμ.symm) ≤ maxCycleMeanKarp E
    have hsneq : maxCycleMeanSimple E = (↑μstar : WithBot ℝ) := hcm.symm.trans hμ.symm
    rw [hsneq]; exact hle

end DirectionB

/-- **Direction B** du théorème de Karp : `sSup{cycleMean | isCycle} ≤ maxCycleMeanKarp E`.
    Via C1, équivaut à `maxCycleMeanSimple ≤ maxCycleMeanKarp` (témoin concret `c*`,
    **D2/BddAbove ÉVITÉE**). Preuve par **récurrence + propagation** du potentiel décalé
    `π(v) := max_{k<n} (toRealBot(d_k(v)) − k·μ*)` le long des arêtes du cycle critique `c*`
    (section Direction B, portée de `DirectionB2_scratch.lean` 2026-08-05, sorry-free) :
      (B1) témoin `c*` simple de mean `μ*` (`exists_simple_cycle_eq_max`) ;
      (B2) `hFact2` : `e_n(v) ≤ π(v)` ∀v (pigeonhole n-marche, retrait de cycle simple de mean ≤ μ*) ;
      (B3) `tightness` : `π(c[i+1]) = π(c[i]) + shift_w` sur `c*` (télscopique + `G_μ_fin(c*)=0`) ;
      (B4) `pump` : `∃ v*, e_n(v*) ≥ π(v*)` (propagation le long des arêtes, induction sur L ;
           **`r ≠ 0` ABSORBÉ** par le témoin flottant `v* = c.get((n−k0) mod m)`, aucune divisibilité) ;
      (B5) conclure `μ* ≤ maxCycleMeanKarp` (`per_k_ineq` + `Finset.le_inf'_iff` + `Finset.le_sup`).
    Hypothèses : `h_edge` (IsWalk) + `h_finite` (poids finis ⟹ shift_w fini, `G_μ_fin(c*)=0`) +
    `h_irred` (atteignabilité ⟹ `hπfin`). Sorry-free, `#print axioms` =
    `[propext, Classical.choice, Quot.sound]`. Cf. `cache/analyse_directionB2_derisque_2026-08-05.md`. -/
theorem maxCycleMeanKarp_ge_sSup {V : Type*} [Fintype V] [DecidableEq V] (E : EdgeSet V)
    (h_edge : ∀ (p : V × V), p ∉ E.edges → E.weight p = (0 : Z_max))
    (h_finite : ∀ (p : V × V), p ∈ E.edges → ∃ (z : ℤ), E.weight p = Z_max.ofInt z)
    (h_irred : Irreducible E) :
    sSup (insert (⊥ : WithBot ℝ)
      { x : WithBot ℝ | ∃ c : List V, isCycle E c ∧ x = cycleMean E c }) ≤ maxCycleMeanKarp E :=
  (C1_sSup_eq E h_finite).le.trans (maxCycleMeanSimple_le_maxCycleMeanKarp E h_edge h_finite h_irred)

/-- Correctness of Karp's algorithm: `maxCycleMeanKarp` computes the maximum cycle mean of `E`.
    Formal statement of Karp's 1978 theorem adapted to max-plus algebra.

    RHS = `sSup` des `cycleMean E c` sur les **cycles** (`isCycle E c`), avec `⊥` par défaut
    (graphe acyclique → `sSup {⊥} = ⊥`). Le filtre `isCycle E c` est **requis** dès que
    `E.weight = ⊥` hors-arêtes (sinon un chemin ouvert `[a,b,c]` a un `cycleMean` fini qui gonfle
    le RHS au-dessus du max cycle mean). **Correctif de l'énoncé (découverte #4, 2026-08-01)** :
    l'énoncé porte désormais formellement `h_edge` (poids `= (0 : Z_max)` = `⊥`/`negInf`
    hors-arêtes) et `h_finite` (∃ `z : ℤ`, poids `= Z_max.ofInt z` sur les arêtes), en plus de
    `h_irred`. Sans `h_edge`, un poids fini hors-arêtes fait croître `karp_d` (LHS) via le graphe
    *complet* et l'égalité est fausse (LHS > RHS ; contre-ex. V={a,b}, `E.edges=∅`, poids finis
    hors-arêtes → LHS=1, RHS=⊥). `h_finite` garantit qu'un cycle `isCycle` optimal a
    `cycleMean ≠ ⊥` (facilite la Direction B / lasso-pumping). Toutes deux sont satisfaites par
    `tegEdgeSet` (`ExtensionInfinie.lean:226`) — correctif **non-régressif** : le consommateur
    aval `maxCycleMean_eq_karp` (#4, `ExtensionInfinie.lean:473`) hérite déjà `h_irred` et
    dérivera `h_edge`/`h_finite` de `tegEdgeSet`. La Direction A (`maxCycleMeanKarp_le_simple`)
    n'utilise que `h_edge` (pas `h_irred`, pas `h_finite`) ; l'égalité-cible les exige toutes
    trois. Cf. `lean4_proof_difficulties_analysis.md` §13.13 (A/B/C fixés ; l'énoncé était cru
    VRAI après Fix B — justement : VRAI mais trivial, cible = graphe complet, pas le TEG).

    **Hypothèse `h_irred : Irreducible E` (décision (i) / dimension (c))** : la formule
    single-source (`Classical.arbitrary V` + `n = Fintype.card V`) n'est correcte que sous
    forte connexité — sans elle, `D_n(v)=⊥` pour les sommets hors du SCC de la source → LHS faux
    (vérité contingentée au tirage `Classical.arbitrary`). `Irreducible E` = `#5 h_irred` / cadre
    BCOQ (eigenvalue = max cycle mean sous irréductibilité) ; **#4 hérite** de cette hypothèse.
    Cas couverts sans elle : #3 (acyclique → `D_n = ⊥` = RHS `sSup{⊥}`, calcul direct sans cet
    énoncé) et #5 (sous `Irreducible` côté matrice). L'énoncé **général** porte donc `Irreducible E`.

    **⚠️ Subtilité `Irreducible` (à traiter dans la preuve)** : `Irreducible E := ∀ s v, ∃ k,
    karp_d E s k v ≠ ⊥` admet `k = 0` pour `s = v` (`d_0(s) = 1`). Donc pour `|V| = 1` sans
    self-boucle, `Irreducible E` tient trivialement sans cycle — cas dégénéré à carter (la preuve
    doit soit exclure `|V| ≥ 2`, soit traiter `|V| = 1` séparément). Pour `|V| ≥ 2`, `Irreducible`
    ⟹ forte connexité ⟹ ∃ cycle (helper `Irreducible_imp_exists_cycle`, ~20 lignes, Semaine 4 J4).

    **Stratégie de preuve (Karp 1978)** — décomposition en deux directions
    (`maxCycleMeanKarp_correct = le_antisymm`) ; Direction A sorry-free (A5+C1), Direction B
    sorry-free (potentiel décalé + propagation, portée de `DirectionB2_scratch.lean` 2026-08-05 —
    cf. `maxCycleMeanKarp_ge_sSup` ci-dessous) :
      • **Direction A** (`maxCycleMeanKarp E ≤ sSup{cycleMean}`) : pour tout `v` et `k < n` à
        `d_k(v)` fini, `(d_n(v) - d_k(v))/(n-k) ≤ μ*`. Via `path_shorten` : tout chemin de
        longueur `n` finissant en `v`, pigeonhole sur `|V|` sommets donne un sommet répété
        `i < j`, extraire le cycle `P[i..j]` (mean ≤ μ*), le retirer ; itérer jusqu'à longueur
        `k`. Donc `d_k(v) ≥ d_n(v) − (n−k)·μ*` → l'inégalité. Le `min_k` (inf') est ≤ chaque
        terme, le `sup_v` préserve. Helpers : `List.exists_repeated` (pigeonhole Fintype),
        `cycle_from_repeated_vertex`, `path_shorten_by_cycle_removal`.
      • **Direction B** (`sSup{cycleMean} ≤ maxCycleMeanKarp E`) : via C1, équivaut à
        `maxCycleMeanSimple ≤ maxCycleMeanKarp` (D2/BddAbove ÉVITÉE). **Récurrence + propagation**
        du potentiel décalé `π(v) = max_{k<n} (d_k(v) − k·μ*)` le long des arêtes du cycle
        critique `c*` : `hFact2` (e_n ≤ π, pigeonhole) + `tightness` (π(c[i+1]) = π(c[i]) + shift_w,
        télscopique + G_μ(c*)=0) + `pump` (∃ v*, e_n(v*) ≥ π(v*), induction sur L) + conclure
        `per_k_ineq`-style (`Finset.le_inf'_iff` + `Finset.le_sup`). **`r ≠ 0` absorbé** par le
        témoin flottant `v* = c.get((n−k0) mod m)`, **aucune divisibilité**. Arithmétique
        `per_v_ineq`-style (cast-then-sub `(n−k:ℝ)`, linarith-friendly). Cf.
        `cache/analyse_directionB2_derisque_2026-08-05.md`.
    Consommateur aval : `cycleWeight_TEG_eq_Karp` → #4 → #1/#5 → #3 (Semaine 4). -/
theorem maxCycleMeanKarp_correct {V : Type*} [Fintype V] [DecidableEq V] (E : EdgeSet V)
    (h_edge : ∀ (p : V × V), p ∉ E.edges → E.weight p = (0 : Z_max))
    (h_finite : ∀ (p : V × V), p ∈ E.edges → ∃ (z : ℤ), E.weight p = Z_max.ofInt z)
    (h_irred : Irreducible E) :
    maxCycleMeanKarp E = sSup (insert (⊥ : WithBot ℝ)
      { x : WithBot ℝ | ∃ c : List V, isCycle E c ∧ x = cycleMean E c }) :=
  le_antisymm (maxCycleMeanKarp_le_sSup E h_edge h_finite)
              (maxCycleMeanKarp_ge_sSup E h_edge h_finite h_irred)

end KarpAlgorithm
