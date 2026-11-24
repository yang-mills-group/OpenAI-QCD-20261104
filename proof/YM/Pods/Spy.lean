import YM.Patria.Brute
import YM.Patria.Reflect
import YM.QCD.Tide.Milky
import YM.Massive.Finite.Chess
/-! # Oriented tile reflections on the fermions (PicC, t=0, includes their AP)
   Mirrors through link seams as required for chessboard *on the same regulated spin theory*.
   Use cycles in the actual cut groupoid; comparing two such paths in geometry
   can expose only an overall grade sign. Essential in bounding with the same family
   of operands, with any reflections encountered.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Romance
open Function Filter Set QCD QCD.Lat QCD.Tide QCD.Revolve QCD.RP QCD.Grass Lattice Wilson Matrix
open Chess Cells
open scoped Topology ComplexOrder BigOperators Matrix.Norms.L2Operator Classical
variable {F:ℕ}{n:Side}
abbrev Band (n:Side):= Cells.Cut n
variable (l:List (Band n))
def linear : List (Band n)→Signed
 | []=>1
 | C::l=> C.flip * linear l
def stride : List (Band n)→Site n
 | []=>0
 | C::l=> affine C.flip C.slide (stride l)
abbrev maps := shiftE (linear l) (stride l)
lemma maps_cons (C:Band n) : maps (C::l)= (maps l).trans (shiftE C.flip C.slide) :=by
   ext1 i; change affine (C.flip * linear l) (stride (C::l)) i= affine C.flip C.slide (affine (linear l) (stride l) i); simp only [stride,affine,Signed.act_mul, Signed.act_add]; abel

section signs
variable {s t:Site n→ℂ} {X Y:Signed}{u v:Site n}
lemma via_glare (h:Glare X 0 0 u s) (ht:Glare Y 0 0 v t) : Glare (Y*X) 0 0 (affine Y v u) (fun i=>s i*t (affine X u i)):=by
   refine ⟨fun x=>?_ ,fun i x=>?_⟩; · rcases h.sign x with h|h <;> rcases ht.sign (affine X u x) with he|he <;> rw [h,he] <;> simp
   let a:=posDir i; let y:=affine X u x; have ha:= glared ht (a.rotate X) y
   change glint 0 x a*(s (x+a.vec)* _)= (s x*t y)*_
   rw [← mul_assoc,glared h a x,show x+step i=x+a.vec from rfl,Revolve.affine_add,mul_assoc]; change s x*(glint (0:Site n) y (a.rotate X)*t (y+(a.rotate X).vec))= (s x*t y)*glint 0 _ _; rw [ha,Step.rotate_mul,show affine (Y*X) (affine Y v u) x=affine Y v y from ?_,mul_assoc]; unfold affine y; rw [affine,Signed.act_add,Signed.act_mul,← add_assoc]; -- likely

def sealP : List (Band n)→Site n→ℂ
 | []=>1
 | C::l=> fun i=>sealP l i*inc C (maps l i)
variable (he:∀ C∈l,C.kind= .link)
include he
lemma seal_glare : Glare (linear l) 0 0 (stride l) (sealP l):=by
   induction l with
   | nil=> refine ⟨fun i=> Or.inl rfl,fun i x=>?_⟩; simp [linear,stride,sealP,affine,glint]; rfl
   | cons C l ih=> exact via_glare (ih fun c hc=> he c (by simp [hc])) (glances C (he C (by simp)))
omit he in
lemma tracks (x y:Site n):∃ w:Walk,stop x w=y:=by
   let w:= route 0 (Lattice.lift (y-x)) 1; refine ⟨w,?_⟩; rw [QCD.Kit.wrap_stop]; unfold w; rw [route_end,wrap_lift]; abel
omit he in
lemma shimmer_ok (x:Site n) (w:Walk) : shimmer 0 x w ≠0:=by
   induction w generalizing x with
   | nil=> exact one_ne_zero
   | cons a w h=> have h0:= glint_sq x (0:Site n) a; have hh: glint 0 x a ≠0:= fun he=> by simp [he] at h0
                  exact mul_ne_zero hh (h _)
lemma frozen (h: linear l=1)(ht:stride l=0) : ∃ z:ℂ,(z=1∨z= -1)∧ sealP l=Function.const _ z:=by
    have hh:=seal_glare l he; rw [h,ht] at hh; refine ⟨sealP l 0,hh.sign 0,funext fun i=>?_⟩; obtain ⟨w,hw⟩:= tracks (0:Site n) i; have hV:= flare_path hh w 0; rw [hw] at hV; change _= _*shimmer _ _ _ at hV; simp only [Step.rotate_one,affine,Signed.act_one,zero_add] at hV; rw [show (List.map (fun i=>i) w)=w from List.map_id w] at hV; apply mul_left_cancel₀ (shimmer_ok (0:Site n) w); exact hV.trans (mul_comm ..)
end signs


-- Spin rotation side (G5 already charged inside tilt).
abbrev arrow (i:Axis): Spike:= - gamma i
noncomputable def rod : List Axis→Spike
 | []=>1
 | a::l=> rod l * arrow a
variable (t:List Axis)
theorem rod_app (w:List Axis):rod (t++w)=rod w * rod t:=by induction t with | nil=> simp [rod] | cons a t ih=> change rod (t++w)*arrow a= _; rw [ih]; exact mul_assoc ..
private lemma cross {G:Type*}[Ring G] {a b x y:G} (hp:SignedEq a b)(he:SignedEq x y): SignedEq (a*x) (b*y) :=by
   rcases hp with h|h <;> rcases he with ht|ht <;> rw [h,ht] <;> simp [SignedEq]
lemma two_rods (i:Axis): arrow i * arrow i=1:=by simp [arrow]
theorem trade (u v:List Axis)(h:u.Perm v): SignedEq (rod u) (rod v) :=by
   induction h with
   | nil=>exact .refl _
   | cons a _ ih=> exact cross ih (.refl _)
   | trans _ _ h i=> exact h.trans i
   | swap a b l =>
       change SignedEq ((rod l*arrow a)*arrow b) ((rod l*arrow b)*arrow a)
       rw [mul_assoc,mul_assoc]; apply cross (.refl _); by_cases h:a=b; · subst a; exact .refl _
       exact Or.inr (by unfold arrow; rw [neg_mul_neg,neg_mul_neg,clifford h]) -- orientation
lemma even_rods (m:ℕ)(h:∀ i:Axis, Even (t.count i))(ht:t.length=m): Even m ∧ SignedEq (rod t) 1:=by
   induction m using Nat.strong_induction_on generalizing t with
   | h m ih=>
     cases t with
     | nil=> exact ht ▸ ⟨(by decide),Or.inl rfl⟩
     | cons a l=>
        have he:=h a; rw [List.count_cons_self,Nat.even_iff] at he
        obtain ⟨u,v,rfl⟩:=List.mem_iff_append.mp (List.count_pos_iff.mp (show 0<l.count a from (by omega)))
        have hP:(a::(u++a::v)).Perm (a::a::(u++v)):= List.Perm.cons _ (List.perm_middle (a:=a)) -- check order
        have hz :∀ i:Axis, Even ((u++v).count i):=by
             intro i; specialize h i; rw [hP.count_eq] at h; by_cases hi:i=a; · subst i; simp only [List.count_cons_self,Nat.even_iff] at h ⊢; omega -- goal `Even`
             rwa [List.count_cons_of_ne (Ne.symm hi),List.count_cons_of_ne (Ne.symm hi)] at h
        have H: m=(u++v).length+2:=ht.symm.trans hP.length_eq; obtain ⟨hl,hx⟩:= ih _ (by omega : (u++v).length < m) _ hz rfl
        refine ⟨H.symm ▸ hl.add (by decide),SignedEq.trans (trade _ _ hP) ?_⟩; rwa [rod, rod,mul_assoc,two_rods,mul_one]
abbrev axes : List Axis:= l.map (fun i=>i.pos)
lemma identity_perm (i:Axis): (linear l).perm i=i:=by induction l with
    | nil=> rfl
    | cons x l ih=> rw [linear, Signed.mul_perm_apply,ih]; rfl
lemma paper (i:Axis): (linear l).flip i=false ↔ Even ((axes l).count i):=by
    induction l with
    | nil=> simp [linear,axes]
    | cons C l h=> rw [linear, Signed.mul_flip,identity_perm]; by_cases hp:i=C.pos
                   · have hv : C.flip.flip i=true:=by simp [Cells.Cut.flip,Signed.mirror,hp]
                     simp only [show axes (C::l) = i::axes l from hp.symm ▸ rfl, List.count_cons_self,hv]
                     cases hZ:(linear l).flip i <;> simp only [hZ,Bool.true_xor,Bool.not_false,Bool.not_true,Nat.even_iff] at h ⊢ <;> simp at * <;> omega -- last may undo
                   have hh:C.flip.flip i=false:=by simp [Cells.Cut.flip,Signed.mirror,Ne.symm hp]
                   simp only [hh,Bool.false_xor,show axes (C::l)=C.pos :: axes l from rfl,List.count_cons_of_ne (Ne.symm hp)]; exact h
lemma alcohol (h:linear l=1): Even l.length ∧ SignedEq (rod (axes l)) 1:= even_rods (axes l) _ (fun i=>(paper l i).1 (by rw [h]; rfl)) (by simp [axes])

abbrev spinM : Sheet n:= rides (maps l) (fun i=>sealP l i • wave (rod (axes l)))

lemma spinM_nil : spinM ([]:List (Band n))=1:=by unfold spinM; simp only [axes,List.map_nil,sealP, Pi.one_apply,one_smul,rod,wave_one]; rw [show maps ([]:List (Band n))=Equiv.refl _ from ?_,ridden]; ext1 i; change affine 1 0 i=i; simp [affine]
lemma spinM_cons (C: Band n): spinM (C::l)= spinM l*(- Tide.lens C):=by
   unfold spinM; rw [maps_cons]; unfold Tide.lens hues; rw [← neg_one_smul ℂ (rides _ _),ride_smul,ride_mul]
   congr 1; funext x; simp only [Pi.smul_apply,neg_one_smul,List.map_cons,axes, rod, sealP,gamma_star]; simp only [arrow, Matrix.mul_neg,Matrix.smul_mul,Matrix.mul_smul,wave_mul, Revolve.wave_neg, mul_smul, smul_neg]; rw [smul_comm (sealP _ _)]

variable (C: Lat.Cut n F) (x:Insertion n F) -- mass Wey Θ
abbrev reels (C: Lat.Cut n F) : List (Band n) →Insertion n F→Insertion n F
 | [],x=>x
 | a::l,x=>picture a C (reels C l x)
lemma adapter_neg (x:Fields n F) : adapter (-1) (-1) x= grade x:=by
   have he: (adapter (A:=Modes n F) (-1) (-1))= QCD.Grass.grade:=by -- actual type
      apply ext_atoms; intro i; cases i with
      | inl i=> rw [grade_atom]; change adapter _ _ (psi _)=-psi _; rw [adapt_psi]; simp [Matrix.one_apply, Finset.sum_neg_distrib]
      | inr i=> rw [grade_atom]; change adapter _ _ (bar _)=-bar _; rw [adapt_bar]; simp [Matrix.one_apply, Finset.sum_neg_distrib]
   rw [he]

variable (R : Band n)(hc:C.t=0)
include hc
lemma paints (V:Grid n): picture R C x V= tilt (copies F (Tide.lens R)) (x (R.pullC su V)):=by
    rw [lensF]; have h: RP.mount R C=Tide.simple R:=by unfold RP.mount Tide.simple; rw [hc]; rfl
    unfold picture; rw [h]; rfl
lemma one_grading (V:Grid n) : picture R C x V= adapter (copies F (- Tide.lens R)) (Twist (copies F (- Tide.lens R))) (turn (x (R.pullC su V))):=by
    rw [paints C x R hc, RP.copies_neg,tilts, Twist, ← Matrix.star_eq_conjTranspose,star_neg,← copies_star,Tide.lens_star] -- arg binder
lemma orbits (V:Grid n): reels C l x V= adapter (copies F (spinM l)) (Twist (copies F (spinM l))) (((⇑(turn (A:=Modes n F)))^[l.length]) (x (pull (linear l) (stride l) V))):=by
    induction l generalizing V with
    | nil=> rw [spinM_nil,copies_one]; simp [Twist,linear,stride,reels]
    | cons a l ih=> rw [reels, one_grading C (reels C l x) a hc,ih, Grass.turns,twist_turn,adapt_together,← copies_mul,← spinM_cons,← twist_mul, ← copies_mul,← spinM_cons]; unfold Cut.pullC; rw [pull_pull,List.length_cons,iterate_succ_apply']; rfl -- convert iterate step.Application
                    exact C
omit hc
lemma twistW (x:Fields n F)(k:ℕ)(hk:Even k): ((⇑(turn (A:= Modes n F)))^[k]) x=x:= by
   obtain ⟨k,rfl⟩:= hk; suffices h:∀ (l:ℕ),(⇑(turn (A:=Modes n F)))^[l+l]=id by rw [h]; rfl
   intro l; induction l with
   | zero=> simp
   | succ l ih=> rw [show l+1+(l+1)=2+(l+l) by omega,iterate_add,ih]; ext1 x; change turn (turn x)= _; rw [turned]; rfl -- iterate arg order
lemma closed_spin (he:∀ C∈l,C.kind=.link)(h:linear l=1)(ht:stride l=0) : spinM l=1∨ spinM l= -1:=by
    obtain ⟨z,hz,hW⟩:= frozen l he h ht; have hx:= (alcohol l h).2
    have h0:maps l=Equiv.refl _:=by unfold maps; rw [h,ht]; ext1 i; change affine 1 0 i=i; simp [affine]
    unfold spinM; rw [h0,hW]; have hm : rides (Equiv.refl (Site n)) (fun _=> -(1:Bundle)) = (-1:Sheet n):=by
         have he: (fun _ : Site n=> -(1:Bundle))=(-1:ℂ) • (fun _=> (1:Bundle)):=funext fun i=> (neg_one_smul ℂ _).symm
         rw [he,← ride_smul,ridden,neg_one_smul]
    rcases hz with h'|h' <;> rcases hx with hx|hx <;> rw [h',hx] <;> simp only [Function.const_apply, Revolve.wave_neg,wave_one,one_smul,neg_one_smul,neg_neg,ridden,true_or, hm,or_true]
include hc
lemma picture_closed (hu: Chess.Parity x)(he:∀ C∈l,C.kind=.link)(h:linear l=1)(ht:stride l=0) : Chess.SignedEq (reels C l x) x:=by
    have hk:Even l.length:=(alcohol l h).1
    have hv:= closed_spin l he h ht; obtain ⟨b,hb⟩:= hu; rcases hv with hv| hv
    · apply Or.inl; ext1 i; rw [orbits l C x hc,h,ht,pull_id,twistW _ _ hk,hv, copies_one]; simp [Twist]
    have h(V:Grid n): reels C l x V=grade (x V):=by rw [orbits l C x hc,h,ht,pull_id,twistW _ _ hk,hv, RP.copies_neg, copies_one]; simp [Twist, adapter_neg]
    cases b; · exact Or.inl (ContinuousMap.ext fun i=> (h i).trans (hb i))
    exact Or.inr (ContinuousMap.ext fun i=> (h i).trans (hb i))
end YM.Massive.Romance
#print axioms YM.Massive.Romance.picture_closed
