import YM.Elms.Arbor
import YM.QCD.Grass.SD
/-! # Regulator corresponds to oriented Wilson hopping, and row/col forced operators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp Kronecker
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open LinearMap
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
variable {n:Side}(U:Grid n)
def extra (R:Regulator n 6) : Matrix (Modes n 6) (Modes n 6) ℂ:= Matrix.blockDiagonal (fun i=> (R.m i:ℂ) • (1:Sheet n))
lemma agency (R:Regulator n 6): R.D U= extra R+copies 6 (bareD R.t U 0):=by
   unfold Regulator.D extra copies bareD; rw [← Matrix.blockDiagonal_add]; congr; ext i j; simp
lemma formOg (R:Regulator n 6): Grass.form (R.D U) =Grass.form (extra R)+∑ x:Site n, RP.bank (0+4) 6 x + ∑ x:Site n, ∑ a:Axis, spans 6 a (thread R.t U a x) x (x+step a):=by
    let C: Lat.Cut n 6:=⟨R.β,R.t,0⟩; rw [agency,form_add,show copies _ _=C.ferm U from rfl,RP.bare_basis]
    change _+(_+_)=_; rw [←add_assoc]; rfl
-- location Hessians.C variant.FL
variable (R:Regulator n 6)
abbrev mL (M: Spike):ΔM:= copies 6 (wave M)
variable (o:Cover)(w:Walk)
local notation "sT"=>stripe n o w U
local notation "K"=> landsE n o w
local notation "t₁" x a=>thread (0:Site n) U a x
abbrev Scope (n:Side):= Matrix (Modes n 6) (Modes n 6) ℂ
def torn (a:Axis)(n:Side)(U:Grid n):Scope n:=copies 6 (1-singleHop 0 U a)
lemma hmasses (hT:R.t=0): R.D U= extra R+∑ i:Axis,torn i n U:=by
   rw [agency,hT,bareD,Complex.ofReal_zero,zero_smul,zero_add]
   congr 1; ext i j
   simp_rw [torn]; simp only [copies,Matrix.blockDiagonal_apply,Matrix.sum_apply]; split_ifs <;> simp
lemma card_on(x:Site n)(a: Dike): ∀ i:Modes n 6, extra R (place x a) i=if place x a=i then (R.m a.2:ℂ) else 0:=by
   intro ⟨b,c⟩; unfold extra place; simp [Matrix.blockDiagonal_apply, Matrix.one_apply, ←ite_and,and_comm]; -- split
lemma card_tr (x:Site n)(a:Dike)(i:Modes n 6): extra R i (place x a)=extra R (place x a) i:=by
   obtain ⟨⟨y,v⟩,u⟩:=i; change extra R (place y (v,u)) (place x a)=extra R (place x a) (place y (v,u)); rw [card_on,card_on]; by_cases h:place (F:=6) x a=place y (v,u) 
   · rw [if_pos h.symm,if_pos h]; rw [show a.2=u from congr_arg Prod.snd h]
   rw [if_neg (Ne.symm h),if_neg h]
lemma visorB (a:Axis)(x y: Site n)(i j:Dike): copies 6 (singleHop 0 U a) (place x i) (place y j)=
     (if x+step a=y then RP.down 6 a (thread 0 U a x) i j else 0)+(if x-step a=y then RP.up 6 a (thread 0 U a (x-step a)) i j else 0):=by
   rw [singleHop,copies_add]; simp_rw [Matrix.add_apply]; unfold shift onSpin RP.down RP.up; rw [ride_ad,ride_mul,ride_mul,RP.placed,RP.placed]; simp only [touch_star,Equiv.refl_trans, Lat.forward, Equiv.refl_apply, show ∀ x, ((Equiv.addRight (step a : Site n)).symm x)=_ from fun x=> Lat.back a x]; rfl
lemma thornB (a:Axis): torn a n U= 1 - copies 6 (singleHop 0 U a):=by unfold torn; simp only [sub_eq_add_neg,copies_neg,copies_add,copies_one]
noncomputable def shove (i:Dike)(a:Axis)(x:Site n):Lat.Fields n 6:=∑ j:Modes n 6, torn a n U (place x i) j • psi j
noncomputable def coveD(i:Dike)(a:Axis)(x:Site n):Lat.Fields n 6:=∑ j:Modes n 6, torn a n U j (place x i) • bar j
private lemma P_at (A B : ΔM) (e: Dike)(V: Dike→ Lat.Fields n 6) :
     ∑ j:Dike,(A*B) e j • V j= ∑ j:Dike, A e j • ∑ i:Dike,B j i • V i:=by simp only [Matrix.mul_apply,sum_smul,mul_smul,Finset.smul_sum]; rw [Finset.sum_comm]
lemma shoved(i:Dike)(a:Axis)(x:Site n): shove U i a x=psi (place x i)-((∑ j:Dike, RP.down 6 a (thread 0 U a x) i j • psi (place (x+step a) j)) + ∑ j:Dike, RP.up 6 a (thread 0 U a (x-step a)) i j • psi (place (x-step a) j)):=by
    unfold shove; rw [thornB]; simp_rw [Matrix.sub_apply,Matrix.one_apply, sub_smul, ite_smul]; simp only [Finset.sum_sub_distrib,one_smul,zero_smul,sum_ite_eq,mem_univ,if_true]; rw [RP.placed_sum]; simp_rw [visorB,add_smul]; simp only [ite_smul,zero_smul,sum_add_distrib]; apply congr_arg₂ _ rfl; refine congr_arg₂ (·+·) ?_ ?_
    · rw [sum_comm]; simp
    rw [sum_comm]; simp
lemma coved(i:Dike)(a:Axis)(x:Site n): coveD U i a x=bar (place x i)-((∑ j:Dike, RP.down 6 a (thread 0 U a (x-step a)) j i • bar (place (x-step a) j)) + ∑ j:Dike, RP.up 6 a (thread 0 U a x) j i • bar (place (x+step a) j)):=by
    unfold coveD; rw [thornB]; simp_rw [Matrix.sub_apply,Matrix.one_apply, sub_smul, ite_smul]; simp only [Finset.sum_sub_distrib,one_smul,zero_smul,sum_ite_eq',mem_univ,if_true]; rw [RP.placed_sum]; simp_rw [visorB,add_smul]; simp only [ite_smul,zero_smul,sum_add_distrib]; apply congr_arg₂ _ rfl; refine congr_arg₂ (·+·) ?_ ?_
    · rw [sum_comm]; simp [←eq_sub_iff_add_eq]
    rw [sum_comm]; simp [sub_eq_iff_eq_add]
lemma clutch_wave (u:su.El)(M:Spike): Commute (clutch u) (mL M):=by show _*_=_*_; unfold clutch blux mL; rw [←copies_mul,←copies_mul,(interlace ..).eq]
lemma stripe_wave (M:Spike):Commute sT (mL M):= (clutch_wave _ M).smul_left _
lemma stripe_top (a:Axis): sT * RP.down 6 a (thread 0 U a K)=mL (Lat.lo a)* stripe n o (w++[posDir a]) U:=by rw [stripe_head]; unfold RP.down; rw [Lat.copies_mul]; change sT*(mL _ * blux _)= mL _ * (sT * blux _); rw [←Matrix.mul_assoc,(stripe_wave U o w _).eq,Matrix.mul_assoc]
lemma stripe_bot (a:Axis): sT*RP.up 6 a (thread 0 U a (K-step a))=mL (hi a)* stripe n o (w++[negDir a]) U:=by rw [stripe_tail]; unfold RP.up; rw [Lat.copies_mul,← blux_star]; change sT*(mL _ * blux _)= mL _ *(sT* blux _); rw [←Matrix.mul_assoc,(stripe_wave U o w _).eq,Matrix.mul_assoc]
lemma moveB(a:Axis)(i:Dike):
     ∑ j:Dike, sT i j • shove U j a K=
     beams false n o w U i- ((∑ j:Dike,mL (Lat.lo a) i j • beams false n o (w++[posDir a]) U j) +∑ j:Dike,mL (hi a) i j • beams false n o (w++[negDir a]) U j):=by
    simp only [shoved,smul_sub,smul_add, Finset.sum_add_distrib,Finset.sum_sub_distrib]; unfold beams; simp only [peggle,Bool.false_eq_true,if_false,lineT]; apply congr_arg₂ _ rfl; refine congr_arg₂ (·+·) ?_ ?_
    next => rw [← P_at sT,← P_at (mL _),land_head,stripe_top]
    next => rw [← P_at sT,← P_at (mL _),land_tail,stripe_bot]
lemma starstripe (M:Spike):Commute (star sT) (mL M):=by
    have h:= congr_arg star (stripe_wave U o w (star M)).eq; unfold mL at *; rw [star_mul,star_mul,←copies_star,wave_star,star_star] at h; exact h.symm
lemma threadS (u:ΔM)(p:Dike→Lat.Fields n 6)(a:Dike): ∑ j:Dike, u j a • p j=∑ j:Dike, u.transpose a j • p j:=rfl -- dot convenience
lemma stripes_fore(a:Axis): (star sT).transpose * (RP.up 6 a (thread 0 U a K)).transpose=(mL (hi a)).transpose * (star (stripe n o (w++[posDir a]) U)).transpose:=by
   have he(m:Mat)(y:Spike): Commute (blux m) (mL y):=by show _*_=_*_; unfold blux mL; rw [←copies_mul,←copies_mul,(interlace ..).eq]
   rw [← Matrix.transpose_mul,← Matrix.transpose_mul]; apply congr_arg
   let u:= thread 0 U a K; let y:= hi a
   rw [RP.up,Lat.copies_mul,stripe_head, star_mul]; change (mL y * blux (star u)) * star sT = (star (blux u) * star sT)* mL y
   rw [← blux_star u, Matrix.mul_assoc (blux _), (starstripe U o w _).eq, ← Matrix.mul_assoc (blux _), (he _ _).eq]
lemma stripes_aft(a:Axis): (star sT).transpose * (RP.down 6 a (thread 0 U a (K-step a))).transpose=(mL (Lat.lo a)).transpose * (star (stripe n o (w++[negDir a]) U)).transpose:=by
   rw [← Matrix.transpose_mul,← Matrix.transpose_mul]; apply congr_arg; let Z:=thread 0 U a (K-step a)
   rw [RP.down,Lat.copies_mul,stripe_tail, star_mul,star_star]; change (mL (Lat.lo a)*blux Z)*star sT=(blux Z*star sT)*mL (Lat.lo a); rw [Matrix.mul_assoc (blux Z),(starstripe U o w _).eq, ← Matrix.mul_assoc (blux _)]; unfold blux mL; rw [←copies_mul,← copies_mul] -- may tries on ext star.E
   rw [(interlace ..).eq]
lemma moveH (a:Axis)(i:Dike):
    ∑ j:Dike,(star sT).transpose i j • coveD U j a K=
    beams true n o w U i- ((∑ j:Dike,(mL (Lat.lo a)).transpose i j • beams true n o (w++[negDir a]) U j)+∑ j:Dike,(mL (hi a)).transpose i j • beams true n o (w++[posDir a]) U j):=by
    simp only [coved,smul_sub,smul_add,sum_add_distrib,sum_sub_distrib]; unfold beams; simp only [peggle,if_true,lineT]; apply congr_arg₂ _ rfl; refine congr_arg₂ (·+·) ?_ ?_
    next => simp_rw [threadS (RP.down 6 a (thread 0 U a (K-step a)))]; rw [← P_at (star sT).transpose,← P_at (mL _).transpose,land_tail,stripes_aft]
    next => simp_rw [threadS (RP.up 6 a (thread 0 U a K))]; rw [← P_at (star sT).transpose,← P_at (mL _).transpose,land_head,stripes_fore]
open Pulses
noncomputable def revM {X:Type}(q:Bool)(A:Matrix X X ℂ):Matrix X X ℂ:=if q then A.transpose else A
def adWalk(q:Bool)(w:Walk)(a:Axis):Walk:= if q then w++[negDir a] else w++[posDir a]
noncomputable def unwind (n:Side)(q:Bool)(o:Cover)(w:Walk)(U:Grid n)(i:Dike)(a:Axis):Lat.Fields n 6:=
   beams q n o w U i-((∑ j:Dike, revM q (mL (Lat.lo a)) i j • beams q n o (adWalk q w a) U j)+∑ j:Dike, revM q (mL (hi a)) i j • beams q n o (adWalk (!q) w a) U j)
lemma movesSpin(q:Bool)(i:Dike)(a:Axis):
   ∑ j:Dike, peggle q sT i j • ∑ z:Modes n 6, revM q (torn a n U) (place K j) z • lineT q z =unwind n q o w U i a:=by cases q; exact moveB U o w a i; exact moveH U o w a i
lemma independent_stripe (q:Bool)(i j:Dike)(h:i.2 ≠ j.2): peggle q sT i j=0:=by cases q <;> simp only [peggle,Bool.false_eq_true,if_false,if_true,stripe, star_smul,stripe_star,Matrix.transpose_apply,Matrix.smul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,clutch,blux,Lat.copies,Matrix.blockDiagonal_apply,if_neg h,star_zero,smul_zero]
noncomputable def windR (R:Regulator n 6)(q:Bool)(o:Cover)(w:Walk)(U:Grid n)(i:Dike): Lat.Fields n 6:=(R.m i.2:ℂ) • beams q n o w U i+∑ a:Axis,unwind n q o w U i a
lemma star_bill (hR:R.t=0)(q:Bool)(i:Dike): ∑ j:Dike, peggle q sT i j • ∑ z:Modes n 6,revM q (R.D U) (place K j) z • lineT q z= windR R q o w U i:=by
   have hp(j z): revM q (R.D U) (place K j) z= extra R (place K j) z + ∑ a:Axis,revM q (torn a n U) (place K j) z:=by cases q <;> simp only [revM,Bool.false_eq_true,if_false,if_true,Matrix.transpose_apply,hmasses U R hR, Matrix.add_apply,Matrix.sum_apply]; rw [card_tr]
   unfold windR; simp only [hp,add_smul,sum_smul,sum_add_distrib,smul_add]; refine congr_arg₂ (·+·) ?_ ?_
   next => unfold beams; simp only [card_on,ite_smul,zero_smul,sum_ite_eq,mem_univ,if_true, Finset.smul_sum]; refine Finset.sum_congr rfl (fun j _=>?_); by_cases h:i.2=j.2; ·rw [h, smul_comm]
           simp [independent_stripe U o w q i j h]
   next => simp_rw [Finset.smul_sum]
           simp_rw [← movesSpin, Finset.smul_sum]; conv_rhs=>rw [Finset.sum_comm]
           exact Finset.sum_congr rfl fun j _=>Finset.sum_comm
end Arbor
end SparK
end YM.Massive.Elm
