import YM.Lapin.Zass
import YM.Lapin.Kroft
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Patria.Gall.Cahoots
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical Kronecker InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open Tawny Tawny.Cast Tawny.Cast.Rays
variable {C:ℝ}{c:Side}{n l d m r k p q w i N:ℕ}{U:BudgetPoint}
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC Patria Patria.Depth Patria.Rolls PCAC.Oren QCD.Grass.Ward Plans.Stamp.Stair
variable {S:Scheme}{R:Side}(A:Massive.Run S N R 6)(hA:A.Actual)(hi:i≤ N)
local notation "M"=> S.side R i
variable (a b:Flavor 6) (s t:Axis)(j j':Fiber)(g:su.Color)(u:Averaging)(T:TaperHol)
local notation "φ"=> A.density i
local notation "G"=> sprigs (i:=i) A a
local notation "X"=> report A (G s) u i 0
local notation "Z"=> foil φ X
local notation "O"=> (0:Multi 10)
local notation "H"=> leadR t
open QCD.Entr.Goals Patria.Gall.Seals
open Lat Grass
private lemma heft (o: Site c)(D:Site c→Site c→ℂ): reed b b j j' D (mote a o 1).val= if a=b ∧ j=j' then D o o else 0:=by
       change (∑ i:Site c,∑ i':Site c, D i i' * (uncoat (coat (localF o 1 a a))) ((i,j),b) ((i',j'),b))=_; rw[coat_known,sum_eq_single o]
       · rw[sum_eq_single o]; rw[localF,zleft,if_pos rfl,flavorW,Matrix.kronecker_apply,on_spin_one]; simp only[Matrix.one_apply]; unfold spot; split_ifs <;> simp_all
         intro i _ h; rw[focusR a a o _ _ _ h,mul_zero]; simp
       · intro i _ h; exact sum_eq_zero fun j _=>by rw[focusL a a o _ _ _ h,mul_zero]
       simp
private lemma oks (F:Cover)(he: F=step t ∨ F = -step t)(hc: 10≤c.val) (f:Site c)(hp: f=wrap c F): Np T.T f * Nw T.T (UV.first s) f=(F s:ℂ):=by
       have ht:Lattice.lift f=F:=by apply lift_eq_iff.mpr; refine ⟨hp,fun i=>?_⟩; rcases he with he|he <;> rw[he]; all_goals by_cases h:i=t <;> simp [step_apply,h] <;> omega
       have hm:T.T.χ ((c.val:ℝ)⁻¹ • vector F)=1:=by
               apply T.T.near; intro i; have he : ‖(F i:ℝ)‖≤1:=by rcases he with he|he <;> rw[he]; all_goals by_cases h:i=t <;> simp [step_apply,h]
               change |((c.val:ℝ)⁻¹)*(F i:ℝ)| ≤ _; rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (by positivity))]; apply le_trans (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (by positivity))); have hx : (10:ℝ) ≤ (c.val:ℝ):=by exact_mod_cast hc
               rw [mul_one]; field_simp; linarith -- edit
       let W:=Np T.T f; have hv: W*W=1:=by
           unfold W Np; rw [ht,hm, Complex.ofReal_one,one_mul]; -- ap simple square using product
           unfold Cylinder.ap; rw [← prod_mul_distrib]; exact prod_eq_one fun i _=>by rw[← mul_zpow, neg_one_mul,neg_neg,one_zpow]
       rw [N_one,ht,←mul_assoc,hv,one_mul]
include hA hi
variable (x:RawVec 10)
local notation "Y"=> report A (G 0) u i 0
variable (hT:Tally T 0 (x.val 0) (A.density i) (report A (sprigs (i:=i) A a 0) u i 0))(hc: 10 ≤ (S.side R i).val)
include hT hc
private lemma zomp : chipK O H b (x.val 0)= if a=b ∧ (t=0) then 1 else 0:=by
       let p: Site M:= step 0; let g(v:Site M):=(mote a v 1).val; let z:= x.val 0; have hh: foil φ Y 1=(sprig a 0 (0:Site M) 1).val:=by rw[arrivesHere]; change Ring.inverse _*(actor A i 1 * _)=_; rw[map_zero,show actor A i 1= φ 1 from congr_fun (act A hA hi) 1]; exact (Ring.inverse_mul_cancel_left (φ 1) _ hT.unit.self_of_nhds) -- order
       ext j j'; let D:= ballast O H T.T (c:=M); let Q:= reed b b j j' D; rw [show chipK O H b (x.val 0) j j'=Q (foil φ Y 1) from (strokeL T j j' b _ _ _ hT O H (by rw [gradeV,gradeL]; norm_num)).symm]; have he: foil φ Y 1=(2:ℂ)⁻¹ • (g p-g (-p)) :=by rw [hh]; change (2:ℂ)⁻¹ • (g (0+p)-g (0-p))=_; rw [zero_add,zero_sub]
       rw [he,map_smul,map_sub,show Q (g p)=_ from heft a b j j' p D,show Q (g (-p))=_ from heft a b j j' (-p) D]; unfold D ballast; split
       next h=> rw [(veil 0 T p).2,(veil 0 T (-p)).2,(veil t T p).1,(veil t T (-p)).1]; rw [oks t 0 T (step 0) (Or.inl rfl) hc _ (wrap_step M 0).symm,oks t 0 T (-(step 0)) (Or.inr rfl) hc _ (by rw [map_neg,wrap_step])] -- hp orientation
                obtain ⟨hH,h1⟩:=h; split
                next h2=>norm_num [hH,h1,h2.2, step_apply,Matrix.one_apply]
                next hh=>simp [*, show t≠0 from fun h=>hh ⟨hH,h⟩,step_apply]
       next h=>
            rw [sub_zero,smul_zero]; split; next h' => simp [Matrix.one_apply,show j ≠ j' from fun hL=> h ⟨h'.1,hL⟩]; -- else
            next _=>rfl
open Cast.TableT
lemma naked : axM 0 x=Pi.single a 1 ∧ axM 1 x=0:=by
        obtain ⟨⟨v,c⟩,rfl⟩:= certified.2 x; let x:= plaza (v,c); have hp (p:Flavor 6)(t:Axis): wave (qv p O (leadR t) x)= if a=p ∧ t=0 then 1 else 0:=by rw [←coinedP]; exact zomp A hA hi a p t u T x hT hc
        have hu(p'):v p' 1=0:=by
             let J:= gamma (0:Axis)*gamma 1; have he:qv p' O (leadR 1) x=v p' 1 • J:= (life_v p' v c).2.1; have h:=hp p' 1; rw [he,waveP,if_neg (fun hx=> (by have he:(1:Axis)=0:=hx.2; exact (by decide : (1:Axis) ≠0) he))] at h
             have hh : wave J ≠0:=by obtain ⟨i,j,h⟩:= wind_h; exact fun ht=> h (by change wave J i j=0; rw[ht]; rfl)
             exact (smul_eq_zero.mp h).resolve_right hh
        constructor
        · funext b; change (bodyS _).1 b 0=_; rw [bodyι]; have h:=hp b 0; have he:qv b O (leadR 0) x=v b 0 • (1:Spike)+v b 1 • (1:Spike):= (life_v b v c).1; rw [he,hu b,zero_smul,add_zero,waveP,wave_one] at h
          have ht : ((v b 0 • (1:Bundle)) : Bundle) 0 0=v b 0:=by simp
          have hr:=congr_fun (congr_fun h 0) 0; rw [ht] at hr; by_cases hp:b=a; · rw[if_pos ⟨hp.symm,rfl⟩] at hr; simpa only [hp,Pi.single_eq_same, Matrix.one_apply_eq] using hr
          rw [if_neg (by simp[Ne.symm hp])] at hr; rw [Pi.single_eq_of_ne hp]; exact hr
        funext b; change (bodyS _).1 b 1=0; rw [bodyι]; exact hu b
end YM.Massive.Patria.Gall.Cahoots
#print axioms YM.Massive.Patria.Gall.Cahoots.naked
