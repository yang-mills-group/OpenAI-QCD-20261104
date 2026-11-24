import YM.QCD.Sparks.Colours

/-! # Additive integral and elementary tile estimate for any closed walk in cover. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sparks
open Function Filter Lattice Wilson Lat Kit Finset Eyrie Quarry Rudder Stationary
open scoped Topology Matrix BigOperators Classical ContDiff
section IntPath
variable {R X : Type} [AddCommGroup R] [One R] [AddCommGroup X]
def imp (i:Step)(Z: Edge (Four R)→X)(x:Four R):= if i.neg then -(Z (i.used x)) else Z (i.used x)
lemma spendPath (Z: Links R X)(x:Four R)(a b:Walk): bill Z x (a++b)=bill Z x a+bill Z (stop x a) b:=by
  induction a generalizing x <;> simp_all [bill,Lattice.stop,add_assoc]
lemma add_bill (Z:Links R X)(x:Four R)(i:Step)(w:Walk): bill Z x (i::w)=imp i Z x+bill Z (x+i.vec) w:=rfl
lemma reverse_step (Z:Links R X)(x:Four R)(i:Step): imp i.rev Z (x+i.vec)= -imp i Z x:=by rcases i with ⟨i,_|_⟩ <;> simp [imp,Step.vec,Step.rev,Step.used, sub_eq_add_neg]
lemma cancelled (Z:Links R X)(x:Four R)(a:Walk): bill Z (stop x a) (Lattice.reverse a)= -bill Z x a:=by
  induction a generalizing x with
  | nil=> simp [bill,Lattice.reverse]
  | cons a p ih=> rw [show Lattice.reverse (a::p)=Lattice.reverse p++[a.rev] from by simp [Lattice.reverse],add_bill,Lattice.stop,spendPath, ih,reverse_stop,add_bill,bill,add_zero,reverse_step]; abel
lemma drawer (Z:Links R X) (x:Four R)(a b: Step): bill Z x [a,b]= imp a Z x+imp b Z (x+a.vec):=by rw [add_bill,add_bill,bill,add_zero]
def ash (Z:Links R X)(x: Four R)(a b:Step):= bill Z x [a,b]-bill Z x [b,a]
lemma gantry (Z:Links R X)(x:Four R)(a b: Axis): ash Z x (posDir a) (posDir b)=bill Z x (Lattice.square a b):=by
  rw [Lattice.square,show [posDir a,posDir b,negDir a,negDir b]=([posDir a,posDir b]++Lattice.reverse [posDir b,posDir a]) from rfl,spendPath]
  rw [show stop x [posDir a,posDir b]=stop x [posDir b,posDir a] from add_right_comm ..,cancelled,ash]; abel
lemma lift_fell (Z:Links R X)(x:Four R)(a b:Step): ash Z (x+a.vec) a.rev b= -ash Z x a b:=by
  simp only [ash,drawer,reverse_step]
  rw [Step.vec_rev a (R:=R), add_neg_cancel_right, add_right_comm x, reverse_step]; abel
lemma ash_rev (Z: Links R X)(x: Four R)(a b:Step) : ash Z x a b= -ash Z x b a:=by unfold ash; abel
end IntPath

-- payload independent of colors.
abbrev Flux:= Links ℤ ℝ
structure Plaid where
  p : Face ℤ
  sign : ℝ
  cash : |sign|=1

def Plaid.beat (P:Plaid) (X:Flux):= P.sign*bill X P.p.1 (Lattice.square P.p.2.val.1 P.p.2.val.2)
def Plaid.min (P:Plaid):Plaid := { P with sign:=-P.sign,cash:=by rw [abs_neg,P.cash] }
@[simp] lemma Plaid.beat_min (P:Plaid)(X): P.min.beat X= -P.beat X:=by unfold Plaid.min Plaid.beat; ring
def Check (a b:Step):Prop:= ∀ x:Cover,∃ p:Plaid, Laurent.size p.p.1≤ Laurent.size x+ ((a.neg.toNat+b.neg.toNat):ℕ) ∧ ∀ Z, ash Z x a b= p.beat Z
lemma check_toggle (a b:Step)(h:Check a b) : Check b a:=by
  unfold Check; intro x; obtain ⟨p,h,hp⟩:=h x; refine ⟨p.min,?_ ,fun i=> ?_⟩
  · change Laurent.size p.p.1≤ _; omega
  rw [ash_rev,hp,p.beat_min]
lemma in_line (a b:Axis)(h:a≠b): Check (posDir a) (posDir b):=by
  have H a b (h:a<b) : Check (posDir a) (posDir b):= by intro x; exact ⟨⟨(x,⟨(a,b),h⟩),1,abs_one⟩,le_add_of_nonneg_right (Nat.zero_le _),fun Z=>by rw [gantry]; unfold Plaid.beat; simp only [one_mul]⟩ -- h Binder
  rcases lt_or_gt_of_ne h with h|h; · exact H _ _ h
  exact check_toggle _ _ (H _ _ h)
lemma check_left (a:Axis)(b:Step)(h:Check (posDir a) b): Check (negDir a) b:=by
  intro x; let y:= x-step a
  obtain ⟨p,hx,hP⟩:=h y
  refine ⟨p.min,?_ ,fun i=>?_⟩
  · have he : Laurent.size y ≤ Laurent.size x+1:=by
      have hh:= Laurent.size_add x ((negDir a).vec (R:=ℤ))
      rw [price_vec] at hh; simpa [negDir,Step.vec,y,sub_eq_add_neg] using! hh
    change Laurent.size p.p.1 ≤ Laurent.size x+(1+_); change Laurent.size p.p.1≤ Laurent.size y+(0+_) at hx; omega
  have he:=lift_fell i y (posDir a) b; rw [hP,show y+(posDir a).vec=x from by simp [y]] at he; rw [Plaid.beat_min]; exact he
lemma check_all (a b:Step)(h:a.dir≠b.dir): Check a b:= by
  rcases a with ⟨a,_|_⟩ <;> rcases b with ⟨b,_|_⟩
  · exact in_line a b h
  · exact check_toggle _ _ (check_left b _ (in_line _ _ h.symm)) -- inspect
  · exact check_left a _ (in_line a b h)
  exact check_left a _ (check_toggle _ _ (check_left b _ (in_line _ _ h.symm)))
lemma strait (a b:Step)(h:a.dir=b.dir)(Z:Flux)(x):bill Z x [a,b]=bill Z x [b,a]:= by
  rcases a with ⟨a,A⟩; rcases b with ⟨b,B⟩; change a=b at h; subst b
  cases A <;> cases B <;> try rfl
  all_goals
    rw [drawer,drawer]
    simp only [imp,Step.used,Bool.false_eq_true,↓reduceIte,Step.vec]; simp [sub_eq_add_neg]
end YM.QCD.Sparks
