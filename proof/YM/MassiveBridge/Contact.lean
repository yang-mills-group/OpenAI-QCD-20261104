import YM.MassiveBridge.Cups
import YM.MassiveBridge.Panes
/-!
# Actual graded commutation testing

Use exchange lemma with the specific adjacent swaps. Arc C27 in the same conventions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge.Contact
open Set Function Filter Analysis MeasureTheory Distribution Mink Mink.Poincare Complex
open Boundary hiding Fields Surface Waves Letter Sentence
open scoped Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius InnerProductSpace
variable {Q:Sequence} {P:Calibration Q} {X:Massive.Fields} {S:X.Kernel}
variable {Y:Waves X} {W:Surface X} {n : ℕ}
private theorem coordinate_tsupport (f : Fin n → Test4) (i : Fin n) :
    tsupport (Joint.materialize n f) ⊆ (fun x : Points n => x i) ⁻¹' tsupport (f i) := by
  refine closure_minimal ?_ ((isClosed_tsupport _).preimage (by fun_prop))
  intro x hx
  apply subset_tsupport
  intro h
  apply hx
  exact (Joint.material_at f x).trans (Finset.prod_eq_zero (Finset.mem_univ i) h)

private theorem materialize_switch (P : NearPair n) (f : Fin n → Test4) :
    Probe.along P.switch.toContinuousLinearEquiv (Joint.materialize n f) = Joint.materialize n (f ∘ P.s) := by
  ext1 x
  change Joint.materialize n f (P.switch x) = _
  simp only [Joint.material_at, NearPair.switch_at, Function.comp_apply]
  exact ((Equiv.prod_comp P.s (fun i => f i (x (P.s i)))) |>.symm.trans (by simp [NearPair.s]))

private theorem expect_get (W : Surface X) (b : Sentence X) (v : Fin n → Letter X)
    (h : b.length = n) (hv : ∀ i, b.get i = v (Fin.cast h i)) :
    W.expect b = W.W n (fun i => (v i).1) (Joint.materialize n (fun i => (v i).2)) := by
  subst n
  have he : b.get = v := funext hv
  rw [Surface.expect, he]

variable {α : Type*}

/-- Place two letters between the spectator lists. -/
private def slots (a b : List α) (x y : α) (i : Fin (a.length + (b.length+2))) : α :=
    if h : i.val < a.length then a[i.val]
    else if _ : i.val = a.length then x
    else if _ : i.val = a.length+1 then y
    else b[i.val-(a.length+2)]'(by omega)

private def pair (a b : List α) : NearPair (a.length + (b.length+2)) :=
  ⟨⟨a.length, by omega⟩, ⟨a.length+1, by omega⟩, rfl⟩

private theorem get_slots (a b : List α) (x y : α) (i : Fin (a ++ x::y::b).length) :
    (a ++ x::y::b).get i = slots a b x y (Fin.cast (by simp) i) := by
  simp only [List.get_eq_getElem, slots, Fin.val_cast]
  split_ifs with h1 h2 h3
  · exact List.getElem_append_left h1
  · rw [List.getElem_append_right (by omega)]
    generalize_proofs _
    simp [h2]
  · rw [List.getElem_append_right (by omega)]
    generalize_proofs _
    simp [h3]
  rw [List.getElem_append_right (by omega)]
  have h : i.val - a.length = i.val - (a.length+2) + 1 + 1 := by omega
  generalize_proofs _
  simp [h]

private theorem slots_switch (a b : List α) (x y : α) (i : Fin (a.length + (b.length+2))) :
    slots a b x y ((pair a b).s i) = slots a b y x i := by
  rcases eq_or_ne i (pair a b).i with rfl|hi
  · simp [NearPair.s, slots, pair]
  rcases eq_or_ne i (pair a b).j with rfl|hj
  · simp [NearPair.s, slots, pair]
  rw [NearPair.s, Equiv.swap_apply_of_ne_of_ne hi hj]
  have h : i.val ≠ a.length := fun h => hi (Fin.ext h)
  have k : i.val ≠ a.length+1 := fun h => hj (Fin.ext h)
  simp [slots, h, k]


-- Realizations with any adjacent marked values. Work around dependent length indexing by using the split explicitly.
abbrev χ (l r : ℕ): NearPair (l+(r+2)) := ⟨⟨l,by omega⟩,⟨l+1,by omega⟩,rfl⟩
lemma realize_swap (H : Fields.Euclidean S) (l r : ℕ) (x : Points (l+(r+2))) (h : x∈ conf _) (v : Fin (l+(r+2)) → X.W) (p q : Bool)
    (hp:X.homogeneous p (v (χ l r).i))(hq:X.homogeneous q (v (χ l r).j)):
    S _ x v = (if p && q then (-1:ℂ) else 1)*S _ ((χ l r).switch x) (v ∘ (χ l r).s) := by
   let j := χ l r
   let g (k:Fin (l+(r+2))) := (x k,v k)
   let A:=List.ofFn (fun i : Fin l=> g (Fin.castAdd (r+2) i))
   let c:= g ∘ (Fin.natAdd l)
   let R:= List.ofFn (Fin.tail (Fin.tail (fun i:Fin (r+2)=>c i)))
   have he (w:Fin (l+(r+2)) → Plant X) : List.ofFn w= (List.ofFn (fun i : Fin l=> w (Fin.castAdd (r+2) i))) ++ w j.i :: w j.j :: List.ofFn (Fin.tail (Fin.tail (w ∘ Fin.natAdd l : Fin (r+2) → Plant X))) := by
     -- split
     nth_rw 1 [show w= Fin.append (w ∘ Fin.castAdd (r+2)) (w ∘ Fin.natAdd l) from ?_] -- all occurrences
     swap; exact funext (fun i=> Fin.addCases (fun _=> by simp) (fun _=> by simp) i)
     rw [List.ofFn_fin_append,List.ofFn_succ (f:=fun i:Fin (r+2)=>_),List.ofFn_succ (f:=fun i:Fin (r+1)=>_)] -- may rewrite wrong
     rfl
   have init : realize v x=A++g j.i :: g j.j :: R:= he _
   have hE : (fun i=> (((χ l r).switch x) i, (v ∘ (χ l r).s) i))=g ∘ j.s:=rfl
   have second : realize (F:=X) (v ∘ j.s) (j.switch x)=A++ g j.j :: g j.i :: R := by
       unfold realize; rw [hE,he]
       have hx (k): k≠ j.i→ k≠j.j→ j.s k=k:=by intro i j; exact Equiv.swap_apply_of_ne_of_ne i j
       rw [show (g ∘ ⇑j.s) j.i=g j.j from congrArg g (Equiv.swap_apply_left ..),show (g ∘ ⇑j.s) j.j=g j.i from congrArg g (Equiv.swap_apply_right ..)]
       have h₁ (i:Fin l) : j.s (Fin.castAdd (r+2) i) = Fin.castAdd (r+2) i := by apply hx <;> (intro h; have hh:=congrArg Fin.val h; simp only [j,χ,Fin.val_castAdd] at hh; omega)
       have h₂ (i:Fin r):j.s (Fin.natAdd l i.succ.succ)=Fin.natAdd l i.succ.succ:=by apply hx <;> (intro h; have hh:=congrArg Fin.val h; simp only [j,χ,Fin.val_natAdd,Fin.val_succ] at hh; omega)
       congr 1
       · exact congrArg List.ofFn (funext fun i=>congr_arg g (h₁ i))
       exact congrArg (List.cons _) (congrArg (List.cons _) (congrArg List.ofFn (funext fun i=>congr_arg g (h₂ i))))
   rw [← readAt,← readAt, init,second]; exact H.swap _ _ _ _ (by rw [←init]; simpa using h) p q hp hq

lemma pair_commute (E:X.System P) (H:Fields.Euclidean S) (K:WSpins X)(he:Y.Region S) (hw : Y.NonTangentialFree W) (hB : Y.Breathes)
    (l r:ℕ) (f:Fin (l+(r+2))→Test4)(v:Fin (l+(r+2)) → X.W) (p q : Bool) (hp:X.homogeneous p (v (χ l r).i))(hq:X.homogeneous q (v (χ l r).j))(hf:Boundary.Fields.causal (f (χ l r).i) (f (χ l r).j)):
    W.W _ v (Joint.materialize _ f) = (if p && q then (-1:ℂ) else 1) * W.W _ (v ∘ (χ l r).s) (Joint.materialize _ (f ∘ (χ l r).s)):=by
  let j:=χ l r
  let z:= if p&&q then (-1:ℂ) else 1
  let a : (i:Fin (l+(r+2)))→ X.W := v ∘ j.s
  let V:= update a j.i (z • a j.i)
  obtain ⟨X,hX⟩:=Surface.Aurora.supplies (D:=pad) (Surface.tents Y E H K W he hw hB) he hB hw
  have hs : tsupport (Joint.materialize _ f) ⊆ j.gap:=by
    intro x hx
    have hh := lateral _ |>.mp (hf (x j.i) (coordinate_tsupport f j.i hx) (x j.j) (coordinate_tsupport f j.j hx))
    change x j.j-x j.i∈spacelike; rw [lateral,←neg_sub (x j.i)]; simpa only [clock_neg,rest_neg,abs_neg,norm_neg] using hh
  rw [AlongEdge.exchange E H K he hw hB X hX j v V (fun x h=>?_ ) (Joint.materialize _ f) hs,materialize_switch] -- coordinate lemma
  · unfold V; rw [MultilinearMap.map_update_smul, Function.update_eq_self]; rfl
  unfold V; conv_rhs=>rw [realize_swap H l r x h v p q hp hq]
  simp only [MultilinearMap.map_update_smul, Function.update_eq_self, smul_eq_mul]; rfl

theorem graded (E:X.System P) (H:Fields.Euclidean S) (K:WSpins X)(he:Y.Region S) (hw : Y.NonTangentialFree W) (hb : Y.Breathes)
    (a b:Sentence X) (x y:X.W)(p q:Bool)(hx:X.homogeneous p x)(hy:X.homogeneous q y) (f g: Test4)(hf: Boundary.Fields.causal f g): W.expect (a ++ (x,f)::(y,g)::b) = (if p&&q then (-1:ℂ) else 1) * W.expect (a ++ (y,g)::(x,f)::b):=by
  rw [expect_get W _ _ _ (get_slots a b (x,f) (y,g)), expect_get W _ _ _ (get_slots a b (y,g) (x,f))]
  have eq : pair a b=χ a.length b.length:=rfl
  have h' := pair_commute E H K he hw hb a.length b.length (fun i=> (slots a b (x,f) (y,g) i).2) (fun i=> (slots a b (x,f) (y,g) i).1) p q (by simpa [χ,slots] using hx) (by simpa [χ,slots] using hy) (by simpa [χ,slots] using hf)
  simpa only [← eq,Function.comp_def,slots_switch] using h'
end YM.Massive.Bridge.Contact
