import YM.Mural.Pears
/-! # Color--stripe expansion and neighborhood transports. AP signs retained. Bill entry with at most one footprint in point cube. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Comet
open QCD QCD.Grass QCD.Finch QCD.Lat Lattice Wilson RG
open Function Finset MeasureTheory Filter Fork Laurent Flume Kit Pine
open scoped ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
variable {c f:Side}{j k m:ℕ}
-- separate boundary phases at flat, with path universal on small supports
noncomputable def needle (t x:Site f) (e:Step):ℂ:= Lat.seam t (e.used x).1 e.dir
noncomputable def film (t x:Site f): Walk→ℂ
 | []=>1
 | a::l=> needle t x a * film t (x+a.vec) l
noncomputable def turn (t: Site f)(U:Grid f)(w: Walk) (x:Site f): QCD.Mat:= film t x w • colour (travel U x w)
local notation "V"=>turn
lemma nPrice (t x:Site f)(w:Walk): ‖film t x w‖=1:=by
   induction w generalizing x with
   | nil=>simp [film]
   | cons a w ih=> rw [film,norm_mul,ih,mul_one]; unfold needle; rcases Lat.seam_cases t (a.used x).1 a.dir with h|h <;> simp [h]
lemma zedTurn (t x:Site f)(w:Walk): turn t 1 w x= film t x w • 1:=by
    rw [turn, show travel (1:Grid f) x w=1 from ?_, show colour 1=1 from su.mat_one]
    induction w generalizing x with
    | nil=>rfl
    | cons a w ih=> rw [travel,ih,mul_one]; cases a with | mk d b=>cases b <;> simp [Step.read]
lemma urn_h (t: Site f)(w:Walk)(U:Grid f):∃ (e:Equiv.Perm (Site f)), (∀ x,e x=stop x w)∧ routeM t U w=rides e (fun x=> Lat.touch (turn t U w x)):=by
   induction w with
   | nil=>
     refine ⟨Equiv.refl _,fun _=>rfl,?_⟩; change 1=rides _ _; have hh x:turn t U [] x=1:=by unfold turn; simp only [film,one_smul,travel]; exact su.mat_one
     simp_rw [hh,touch_one]; rw [ridden]
   | cons a w ih=>
      obtain ⟨e,h,hM⟩:=ih; change ∃ e, _∧ leg t U a* routeM t U w=_; rw [hM]
      rcases a with ⟨d,b⟩; cases b
      · simp only [leg,Bool.false_eq_true,if_false, shift, ride_mul,touch_mul]
        refine ⟨(forward d).trans e,fun x=>h _,?_⟩; congr 1; funext i; apply congr_arg; rw [hop,turn,turn,film,travel]; change (seam t i d • colour (U (i,d)))*(film t (i+step d) w • _)=(seam t i d*film t (i+step d) w) • colour (_ * _)
        rw [colour_mul,Matrix.mul_smul,Matrix.smul_mul,smul_smul,mul_comm (Lat.seam ..)]; rfl
      simp only [leg, if_true, opp,ride_mul,touch_mul]
      refine ⟨(forward d).symm.trans e,fun x=>?_,?_⟩
      · rw [Equiv.trans_apply,h,back,sub_eq_add_neg]; rfl
      congr 1; funext i; apply congr_arg; rw [back,turn,turn,travel,film]; change star (Lat.thread t U d (i-step d)) * (film t (i-step d) w • colour (travel U (i-step d) w))= (seam t (i-step d) d*film t (i+-step d) w) • colour ((U (i-step d,d))⁻¹*travel U (i+-step d) w); rw [sub_eq_add_neg,thread,star_smul,seam_real,colour_mul,colour_inv,Matrix.mul_smul,Matrix.smul_mul,smul_smul,mul_comm (Lat.seam ..)]
-- extract operator at base t=0
open YM.Next.Free
variable (P:Flight j k)(d:f.val=c.val*P.L.val)(t:Site f)
local notation "S"=> sliceL P d
variable (x:Site c)(y:Site f)
local notation "Iy"=> P.patch.Points
noncomputable def edgeB (i:Iy)(a:Lattice.Order) (U:Grid f): QCD.Mat:= let z:= (route 0 i.val a); if stop ((sliceL P d).embed x) z=y then turn t U z ((sliceL P d).embed x) else 0
noncomputable def byteV (i:Lattice.Order)(U:Grid f): QCD.Mat:= ∑ b:Iy, (P.patch.weight b:ℂ) • edgeB P d t x y b i U
noncomputable def texel (U:Grid f): QCD.Mat:= (massL P.L:ℂ) • ((votes:ℂ)⁻¹ • ∑ i, byteV P d t x y i U)
lemma surfQ (U:Grid f)(w:Walk) (i j: Lat.Fiber): (routeM t U w) (((S).embed x),i) (y,j) = touch (if stop ((S).embed x) w=y then turn t U w ((S).embed x) else 0) i j :=by
    obtain ⟨e,h,hv⟩:=urn_h t w U; rw [hv,rr]; split; next he=> rw [if_pos (show stop _ w=y from (h ..).symm.trans he)]
    next he=> rw [if_neg (show stop _ w ≠ y from fun h'=> he ((h ..).trans h'))]; simp [Lat.touch]
lemma touchSum {I:Type}(s:Finset I)(f:I→Mat) : Lat.touch (∑ i∈s,f i)=∑ i∈s,Lat.touch (f i):=by
   induction s using Finset.induction_on with
   | empty=>simp [Lat.touch]
   | insert i s hi ih=> rw [sum_insert hi,sum_insert hi,← touch_add,ih]
lemma touch_fee (z:ℂ)(x:Mat): touch (z • x)=z • Lat.touch x:=by ext i j; simp [Lat.touch]; ring
lemma crest (U:Grid f)(i j: Lat.Fiber): tied P d t U (x,i) (y,j)= Lat.touch (texel P d t x y U) i j:=by
    simp only [Flume.tied,texel,byteV,lineF,touch_fee, Matrix.smul_apply,touchSum, Matrix.sum_apply, Kit.shows]; apply congr_arg; apply congr_arg; apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _; apply congr_arg; exact surfQ ..
lemma stencil (U:Grid f)(N:ℕ)(i j:Lat.Fiber)(a b:Flavor N):
    Jets.ater (F:=N) P d U ((x,i),a) ((y,j),b)=if a=b then Lat.touch (texel P d 0 x y U) i j else 0:=by
    -- through Choir
    unfold Jets.ater; rw [Sway.choir_in]; change tied P d 0 U _ _ * ((1:Matrix (Flavor N) (Flavor N) ℂ) a b) = _; split; next he=> rw [he, Matrix.one_apply_eq,mul_one,crest]
    next he=> rw [Matrix.one_apply_ne he,mul_zero]
lemma activeP {i j:Pinor}{a b:Hue}(X:Mat): Lat.touch X (i,a) (j,b)=if i=j then X a b else 0:=by simp [Lat.touch,Matrix.one_apply]
@[fun_prop] lemma ticksC (w:Iy)(o:Lattice.Order) : Continuous (edgeB P d t x y w o):=by unfold edgeB turn; dsimp only; split <;> fun_prop
@[fun_prop] lemma contT : Continuous (texel P d t x y):=by unfold texel byteV; fun_prop
end YM.QCD.Comet
#print axioms YM.QCD.Comet.urn_h
#print axioms YM.QCD.Comet.stencil
