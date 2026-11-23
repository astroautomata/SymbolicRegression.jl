import SymReg.Loss.Core

namespace SymReg.Loss
open DynExpr SymReg.HeapLemmas

private def meanOf (p : LossPrecision) (values : List JF) : JF :=
  p.round (pairwiseSum p values / floatCount p values.length)

def unweighted_mean : Prop :=
  ∀ (p : LossPrecision) (f : JF → JF → JF) (g : JF → JF → JF → Jl JF)
    (x y : List JF), x.length = y.length → x ≠ [] →
    lossArray x y (.custom (fun target prediction => .ok (f target prediction)) g) true p =
      .ok (meanOf p (List.zipWith f y x))

theorem unweighted_mean_refuted : ¬ unweighted_mean := by
  intro h
  have hh := h .float64 (fun target _ => target) (fun _ _ _ => .ok (.fin 0))
    [.fin 2] [.fin 7] rfl (by simp)
  have hl : lossArray [.fin 2] [.fin 7]
      (.custom (fun x _ => .ok x) (fun _ _ _ => .ok (.fin 0))) = .ok (.fin 2) := by
    decide +kernel
  have hr : meanOf .float64 [.fin 7] = .fin 7 := by decide +kernel
  change _ = (Except.ok (meanOf .float64 [.fin 7]) : Jl JF) at hh
  rw [hl, hr] at hh
  cases hh

def supervised_weighted_sum : Prop :=
  ∀ (p : LossPrecision) (f : JF → JF → JF) (x y w : List JF),
    x.length = y.length → x.length = w.length → x ≠ [] →
    let values := List.zipWith (fun v wi => p.round (wi * v)) (List.zipWith f x y) w
    weightedLoss x y w (.supervised (fun pred target => .ok (f pred target))) true p =
      .ok (p.round (pairwiseSum p values / pairwiseSum p w))

def custom_weighted_sum : Prop :=
  ∀ (p : LossPrecision) (f : JF → JF → Jl JF) (g : JF → JF → JF → JF)
    (x y w : List JF), x.length = y.length → x.length = w.length → x ≠ [] →
    let values := List.zipWith (fun (target, pred) wi => g target pred wi) (y.zip x) w
    weightedLoss x y w (.custom f (fun target pred wi => .ok (g target pred wi))) true p =
      .ok (p.round (pairwiseSum p values / pairwiseSum p w))

theorem custom_weighted_sum_refuted : ¬ custom_weighted_sum := by
  intro h
  have hh := h .float64 (fun _ _ => .ok (.fin 0)) (fun target _ w => w * target)
    [.fin 2] [.fin 7] [.fin 3] rfl rfl (by simp)
  have hl : weightedLoss [.fin 2] [.fin 7] [.fin 3]
      (.custom (fun _ _ => .ok (.fin 0)) (fun x _ w => .ok (w * x))) = .ok (.fin 2) := by
    decide +kernel
  have hr : LossPrecision.float64.round
      (pairwiseSum .float64 [JF.fin 3 * JF.fin 7] / pairwiseSum .float64 [.fin 3]) =
      .fin 7 := by decide +kernel
  change _ = (Except.ok (LossPrecision.float64.round
    (pairwiseSum .float64 [JF.fin 3 * JF.fin 7] / pairwiseSum .float64 [.fin 3])) : Jl JF) at hh
  rw [hl, hr] at hh
  cases hh

def compatible_weighted : Prop :=
  ∀ (p : LossPrecision) (f : JF → JF → Jl JF) (x y w : List JF),
    x.length = y.length → x.length = w.length →
    weightedLoss x y w (.custom f (fun pred target wi =>
      (f pred target).map (fun v => p.round (wi * v)))) true p =
    weightedLoss x y w (.supervised f) true p

theorem compatible_weighted_holds : compatible_weighted := by
  intro p f x y w hy hw
  have hpoint (i : Nat) :
      (do
        let xi ← at1 x (i + 1)
        let yi ← at1 y (i + 1)
        let wi ← at1 w (i + 1)
        (f xi yi).map (fun v => p.round (wi * v))) =
      (do
        let wi ← at1 w (i + 1)
        let xi ← at1 x (i + 1)
        let yi ← at1 y (i + 1)
        weightedElement (.supervised f) xi yi wi p) := by
    unfold at1
    simp only [Nat.add_eq_zero_iff, Nat.succ_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    by_cases hi : i < x.length
    · have yi : i < y.length := hy ▸ hi
      have wi : i < w.length := hw ▸ hi
      simp [List.getElem?_eq_getElem, hi, yi, wi, weightedElement, bind, Except.bind, pure, Except.pure]
    · have yi : ¬ i < y.length := hy ▸ hi
      have wi : ¬ i < w.length := hw ▸ hi
      simp [List.getElem?_eq_none, hi, yi, wi, bind, Except.bind]
  have hf := funext hpoint
  have hwy : y.length = w.length := hy.symm.trans hw
  simp only [weightedLoss, matchingAxes, hy, hwy, decide_true, Option.map_some,
    Option.getD_some, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hf]

example : ([JF.fin 1] : List JF).length = ([JF.fin 2] : List JF).length ∧
    ([JF.fin 1] : List JF).length = ([JF.fin 3] : List JF).length := ⟨rfl, rfl⟩

def element_type_errors : Prop :=
  ∀ (S L : Type) (elementType : Nat → Nat) (render : Nat → String)
    (x y w : Nat) (s : S)
    (unweighted : Nat → Nat → EStateM JlError S L)
    (weighted : Nat → Nat → Nat → EStateM JlError S L),
    let tx := elementType x
    let ty := elementType y
    let tw := elementType w
    (tx ≠ ty → arrayLossDispatch elementType render x y unweighted s =
      .error (.errorException
        ("Element type of `x` is " ++ render tx ++
          " is different from element type of `y` which is " ++ render ty ++ ".")) s) ∧
    (tx ≠ ty ∨ tx ≠ tw → weightedArrayLossDispatch elementType render x y w weighted s =
      .error (.errorException
        ("Element type of `x` is " ++ render tx ++ ", element type of `y` is " ++
          render ty ++ ", and element type of `w` is " ++ render tw ++
          ". All element types must be the same.")) s)

theorem element_type_errors_holds : element_type_errors := by
  intro S L elementType render x y w s unweighted weighted
  dsimp only
  refine ⟨?_, ?_⟩
  · intro h
    simp [arrayLossDispatch, lossTypeDispatch, h] <;> rfl
  · rintro (h | h) <;> simp [weightedArrayLossDispatch, lossTypeDispatch, h] <;> rfl

example :
    arrayLossDispatch (m := Jl) id (fun ty => if ty = 32 then "Float32" else "Float64")
      32 64 (fun _ _ => .ok ()) =
    .error (.errorException "Element type of `x` is Float32 is different from element type of `y` which is Float64.") := by decide

private def isArgumentError : Jl JF → Prop
  | .error (.argumentError _) => True
  | _ => False

def empty_mean : Prop :=
  ∀ l : Elementwise, isArgumentError (lossArray [] [] l) ∧
    isArgumentError (weightedLoss [] [] [] l)

theorem empty_mean_holds : empty_mean := by
  intro l
  cases l <;> exact ⟨trivial, trivial⟩

end SymReg.Loss
