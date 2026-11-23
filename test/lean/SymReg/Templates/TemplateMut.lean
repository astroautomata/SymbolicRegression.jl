import SymReg.Templates.TemplateOps

/-!
Template mutation and crossover hooks, parameter initialisation and `copy_into!`,
`src/TemplateExpression.jl:514-541,651-701,966-1108`.
-/

namespace SymReg.Templates
open DynExpr DynExpr.Expressions

/-- `with_contents_for_mutation`, `src/TemplateExpression.jl:1012-1027`. -/
def withInner {M : Type} (ex : TExpr M) (new : Expression JF M) (ctx : String) : TExpr M :=
  { ex with inners := (ex.s.keys.zip ex.inners).map fun p => if p.1 = ctx then new else p.2 }

/-- `get_contents_for_mutation`, `src/TemplateExpression.jl:970-976`; `rand(rng, keys)` is the
arbitrary position `i`. -/
def pickInner {M : Type} (ex : TExpr M) (i : Nat) : Option (Expression JF M × String) :=
  match ex.inners[i]?, ex.s.keys[i]? with
  | some e, some k => some (e, k)
  | _, _ => none

/-- `get_nfeatures_for_mutation`, `src/TemplateExpression.jl:1030-1032`. -/
def nfeaturesFor {M : Type} (ex : TExpr M) (ctx : String) : Jl Int := ex.s.nf ctx

theorem zip_map_id {α β : Type} [DecidableEq α] (k : α) (new : β) : ∀ (ks : List α) (xs : List β),
    (∀ a ∈ ks, a ≠ k) → ks.length = xs.length →
    ((ks.zip xs).map fun p => if p.1 = k then new else p.2) = xs
  | [], [], _, _ => rfl
  | [], _ :: _, _, hl => by simp at hl
  | _ :: _, [], _, hl => by simp at hl
  | a :: ks, x :: xs, h, hl => by
    simp only [List.zip_cons_cons, List.map_cons]
    rw [if_neg (h a (by simp)), zip_map_id k new ks xs (fun a' ha' => h a' (by simp [ha']))
      (by simpa using hl)]

theorem zip_map_set {α β : Type} [DecidableEq α] (k : α) (new : β) :
    ∀ (ks : List α) (xs : List β) (i : Nat), ks.Nodup → ks.length = xs.length → ks[i]? = some k →
      ((ks.zip xs).map fun p => if p.1 = k then new else p.2) = xs.set i new
  | [], _, _, _, _, hk => by simp at hk
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | a :: ks, x :: xs, 0, hnd, hl, hk => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    simp only [List.zip_cons_cons, List.map_cons, ↓reduceIte, List.set_cons_zero]
    rw [zip_map_id a new ks xs (fun a' ha' h => (List.nodup_cons.mp hnd).1 (h ▸ ha'))
      (by simpa using hl)]
  | a :: ks, x :: xs, i + 1, hnd, hl, hk => by
    simp only [List.getElem?_cons_succ] at hk
    have hne : a ≠ k := fun h => (List.nodup_cons.mp hnd).1 (h ▸ List.mem_of_getElem? hk)
    simp only [List.zip_cons_cons, List.map_cons, hne, ↓reduceIte, List.set_cons_succ]
    rw [zip_map_set k new ks xs i (List.nodup_cons.mp hnd).2 (by simpa using hl) hk]

theorem set_self {β : Type} : ∀ (xs : List β) (i : Nat) (e : β), xs[i]? = some e → xs.set i e = xs
  | [], _, _, h => by simp at h
  | x :: xs, 0, e, h => by simp at h; simp [h]
  | x :: xs, i + 1, e, h => by
    simp only [List.getElem?_cons_succ] at h
    simp [set_self xs i e h]

theorem pickInner_some {M : Type} {ex : TExpr M} {i : Nat} {e : Expression JF M} {k : String}
    (h : pickInner ex i = some (e, k)) : ex.inners[i]? = some e ∧ ex.s.keys[i]? = some k := by
  unfold pickInner at h
  split at h
  · cases h; exact ⟨by assumption, by assumption⟩
  · cases h

/-- The mutation context round-trips: putting back the sampled inner expression under its key
restores the template, and any replacement changes exactly that key's inner expression. -/
def mutationContext : Prop :=
  ∀ (M : Type) (ex : TExpr M) (i : Nat) (e new : Expression JF M) (k : String),
    ex.s.keys.Nodup → ex.s.keys.length = ex.inners.length → pickInner ex i = some (e, k) →
      withInner ex e k = ex ∧ withInner ex new k = { ex with inners := ex.inners.set i new }

theorem mutationContext_holds : mutationContext := by
  intro M ex i e new k hnd hl hp
  obtain ⟨he, hk⟩ := pickInner_some hp
  have hset : ∀ x, withInner ex x k = { ex with inners := ex.inners.set i x } := fun x => by
    simp only [withInner, zip_map_set k x ex.s.keys ex.inners i hnd hl hk]
  refine ⟨?_, hset new⟩
  rw [hset, set_self _ _ _ he]

theorem lookup_zip {β : Type} : ∀ (ks : List String) (ns : List β) (i : Nat) (k : String),
    ks.Nodup → ks.length = ns.length → ks[i]? = some k → (ks.zip ns).lookup k = ns[i]?
  | [], _, _, _, _, _, hk => by simp at hk
  | _ :: _, [], _, _, _, hl, _ => by simp at hl
  | a :: ks, n :: ns, 0, k, _, _, hk => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    simp [List.lookup]
  | a :: ks, n :: ns, i + 1, k, hnd, hl, hk => by
    simp only [List.getElem?_cons_succ] at hk
    have hne : k ≠ a := fun h => (List.nodup_cons.mp hnd).1 (h ▸ List.mem_of_getElem? hk)
    simp only [List.zip_cons_cons, List.lookup, List.getElem?_cons_succ]
    rw [show (k == a) = false from by simp [hne]]
    exact lookup_zip ks ns i k (List.nodup_cons.mp hnd).2 (by simpa using hl) hk

theorem any_zip_set {α β : Type} (f : α × β → Bool) (a : α) :
    ∀ (xs : List α) (ys : List β) (i : Nat), (xs.zip ys).any f = false →
      (∀ y, ys[i]? = some y → f (a, y) = false) → ((xs.set i a).zip ys).any f = false
  | [], _, _, _, _ => by simp
  | _ :: _, [], i, _, _ => by cases i <;> simp
  | x :: xs, y :: ys, 0, h, ha => by
    simp only [List.zip_cons_cons, List.any_cons, Bool.or_eq_false_iff] at h
    simp only [List.set_cons_zero, List.zip_cons_cons, List.any_cons, Bool.or_eq_false_iff]
    exact ⟨ha y rfl, h.2⟩
  | x :: xs, y :: ys, i + 1, h, ha => by
    simp only [List.zip_cons_cons, List.any_cons, Bool.or_eq_false_iff] at h
    simp only [List.set_cons_succ, List.zip_cons_cons, List.any_cons, Bool.or_eq_false_iff]
    exact ⟨h.1, any_zip_set f a xs ys i h.2 (fun y' hy => ha y' (by simpa using hy))⟩

/-- A mutation that keeps the sampled inner expression within `get_nfeatures_for_mutation`
features keeps the template free of invalid variables. -/
def mutationValid : Prop :=
  ∀ (M : Type) (ex : TExpr M) (i : Nat) (e new : Expression JF M) (k : String) (m : Int),
    ex.s.keys.Nodup → ex.s.keys.length = ex.inners.length →
    ex.s.keys.length = ex.s.numFeatures.length →
    hasInvalid ex = false → pickInner ex i = some (e, k) → nfeaturesFor ex k = .ok m →
    containsGreater m new.tree = false → hasInvalid (withInner ex new k) = false

theorem mutationValid_holds : mutationValid := by
  intro M ex i e new k m hnd hl hnf hv hp hm hnew
  obtain ⟨_, hk⟩ := pickInner_some hp
  rw [(mutationContext_holds M ex i e new k hnd hl hp).2]
  have hlk := lookup_zip ex.s.keys ex.s.numFeatures i k hnd hnf hk
  simp only [nfeaturesFor, TStructure.nf, field, hlk] at hm
  unfold hasInvalid at hv ⊢
  apply any_zip_set _ _ _ _ _ hv
  intro y hy
  rw [hy] at hm
  cases hm
  exact hnew

def mutationReplacementValid : Prop :=
  ∀ (M : Type) (ex : TExpr M) (i : Nat) (e new : Expression JF M) (k : String) (m : Int),
    ex.s.keys.Nodup → ex.s.keys.length = ex.inners.length →
    ex.s.keys.length = ex.s.numFeatures.length →
    hasInvalid ex = false → pickInner ex i = some (e, k) → nfeaturesFor ex k = .ok m →
    containsGreater m new.tree = false →
    withInner ex new k = { ex with inners := ex.inners.set i new } ∧
    hasInvalid (withInner ex new k) = false

theorem mutationReplacementValid_holds : mutationReplacementValid := by
  intro M ex i e new k m hnd hl hnf hv hp hm hnew
  exact ⟨(mutationContext_holds M ex i e new k hnd hl hp).2,
    mutationValid_holds M ex i e new k m hnd hl hnf hv hp hm hnew⟩

/-- `crossover_trees(::AbstractExpression, ...)` (`src/MutationFunctions.jl`) when both
sampled nodes are the roots: the inner trees are exchanged, each child keeping its metadata. -/
def rootSwap {M : Type} (a b : Expression JF M) : Expression JF M × Expression JF M :=
  (⟨b.tree, a.metadata⟩, ⟨a.tree, b.metadata⟩)

/-- `crossover_trees(::TemplateExpression, ...)`, `src/TemplateExpression.jl:978-1009`: each
parent samples its own key (positions `i` and `j`), the sampled inners are crossed and each
child replaces its sampled key. -/
def crossTemplate {M : Type} (cross : Expression JF M → Expression JF M → Expression JF M × Expression JF M)
    (ex1 ex2 : TExpr M) (i j : Nat) : Option (TExpr M × TExpr M) :=
  match pickInner ex1 i, pickInner ex2 j with
  | some (a, k1), some (b, k2) =>
    let c := cross a b
    some (withInner ex1 c.1 k1, withInner ex2 c.2 k2)
  | _, _ => none

/-- Crossover of two templates without invalid variables should give children without
invalid variables. -/
def crossoverValid : Prop :=
  ∀ (M : Type) (ex1 ex2 : TExpr M) (i j : Nat) (c1 c2 : TExpr M),
    hasInvalid ex1 = false → hasInvalid ex2 = false →
    crossTemplate rootSwap ex1 ex2 i j = some (c1, c2) → hasInvalid c1 = false ∧ hasInvalid c2 = false

/-- `f(x1) + g(x1, x2)` with `f = x1`, `g = x2`. -/
def exFG2 : TExpr Unit := ⟨⟨["f", "g"], [], [1, 2], []⟩, [⟨.feature 1, ()⟩, ⟨.feature 2, ()⟩], []⟩

theorem crossoverValid_refuted : ¬ crossoverValid := by
  intro h
  have hv : hasInvalid exFG2 = false := by
    simp [hasInvalid, exFG2, containsGreater]
  have := (h Unit exFG2 exFG2 0 1 _ _ hv hv rfl).1
  simp [withInner, hasInvalid, exFG2, rootSwap, containsGreater] at this

/-- Crossing the same key of two templates with one structure keeps both children valid. -/
def crossoverSameKey : Prop :=
  ∀ (M : Type) (ex1 ex2 : TExpr M) (i : Nat) (c1 c2 : TExpr M),
    ex1.s = ex2.s → ex1.s.keys.Nodup → ex1.s.keys.length = ex1.inners.length →
    ex2.s.keys.length = ex2.inners.length → ex1.s.keys.length = ex1.s.numFeatures.length →
    (∀ m ∈ ex1.s.numFeatures, 0 ≤ m) → hasInvalid ex1 = false → hasInvalid ex2 = false →
    crossTemplate rootSwap ex1 ex2 i i = some (c1, c2) → hasInvalid c1 = false ∧ hasInvalid c2 = false

theorem nf_of_valid {M : Type} (ex : TExpr M) (i : Nat) (e : Expression JF M) (k : String)
    (hnd : ex.s.keys.Nodup) (hnf : ex.s.keys.length = ex.s.numFeatures.length)
    (hpos : ∀ m ∈ ex.s.numFeatures, 0 ≤ m) (hv : hasInvalid ex = false)
    (hp : pickInner ex i = some (e, k)) :
    ∃ m, nfeaturesFor ex k = .ok m ∧ (maxFeature e.tree : Int) ≤ m := by
  obtain ⟨he, hk⟩ := pickInner_some hp
  have hlk := lookup_zip ex.s.keys ex.s.numFeatures i k hnd hnf hk
  have hlt : i < ex.s.numFeatures.length := by
    have := (List.getElem?_eq_some_iff.mp hk).1; omega
  refine ⟨ex.s.numFeatures[i], by
    simp [nfeaturesFor, TStructure.nf, field, hlk, List.getElem?_eq_getElem hlt], ?_⟩
  have hi : i < ex.inners.length := (List.getElem?_eq_some_iff.mp he).1
  have hmem : (e, ex.s.numFeatures[i]) ∈ ex.inners.zip ex.s.numFeatures := by
    rw [List.mem_iff_getElem?]
    exact ⟨i, by simp [List.getElem?_zip_eq_some, he]⟩
  have hno : ¬ ∃ p ∈ ex.inners.zip ex.s.numFeatures, (maxFeature p.1.tree : Int) > p.2 := fun hex => by
    have := (invalidVars_holds M ex hpos).mpr hex
    rw [hv] at this; cases this
  exact Int.not_lt.mp (fun hgt => hno ⟨_, hmem, hgt⟩)



theorem crossoverSameKey_holds : crossoverSameKey := by
  intro M ex1 ex2 i c1 c2 hs hnd hl1 hl2 hnf hpos hv1 hv2 hc
  unfold crossTemplate at hc
  split at hc
  · rename_i a k1 b k2 h1 h2
    cases hc
    have hk : k1 = k2 := by
      have := (pickInner_some h1).2; have := (pickInner_some h2).2; rw [<- hs] at *; simp_all
    subst hk
    obtain ⟨m1, hm1, ha⟩ := nf_of_valid ex1 i a k1 hnd hnf hpos hv1 h1
    obtain ⟨m2, hm2, hb⟩ := nf_of_valid ex2 i b k1 (hs ▸ hnd) (hs ▸ hnf) (hs ▸ hpos) hv2 h2
    have hm : m1 = m2 := by
      simp only [nfeaturesFor] at hm1 hm2; rw [hs] at hm1; rw [hm1] at hm2; cases hm2; rfl
    subst hm
    have hmpos : 0 ≤ m1 := by
      obtain ⟨_, hk⟩ := pickInner_some h1
      have hlk := lookup_zip ex1.s.keys ex1.s.numFeatures i k1 hnd hnf hk
      simp only [nfeaturesFor, TStructure.nf, field, hlk] at hm1
      cases he : ex1.s.numFeatures[i]? with
      | none => rw [he] at hm1; cases hm1
      | some q =>
        rw [he] at hm1
        cases hm1
        exact hpos _ (List.mem_of_getElem? he)
    have hl := containsGreater_iff (T := JF) m1 hmpos
    exact ⟨mutationValid_holds M ex1 i a _ k1 m1 hnd hl1 hnf hv1 h1 hm1
        (by change containsGreater m1 b.tree = false; rw [hl]; simp; omega),
      mutationValid_holds M ex2 i b _ k1 m1 (hs ▸ hnd) hl2 (hs ▸ hnf) hv2 h2 hm2
        (by change containsGreater m1 a.tree = false; rw [hl]; simp; omega)⟩
  · cases hc

end SymReg.Templates
