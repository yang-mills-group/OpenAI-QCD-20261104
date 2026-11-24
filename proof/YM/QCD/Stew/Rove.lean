import YM.QCD.Stew.Silver
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Spin
/-! # Moments charged at footprint. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ}
open Revolve Flume Quarry
open AnalyticBridge.VerifiedReset
lemma colour_room (x:EvenA c N){S:Support c}{i j:Site c}(h:Gated S x) (b:Flavor N)(hp:i∉S∨j∉S): cell (feeF b x) i j=0:=by
   ext p q; let I : Modes c N:= ((i,p),b); let J:Modes c N:=((j,q),b); change bit I J*coef (tag I J) x.val=0
   rw [Cove.ember x.val h, mul_zero]; intro he; apply hp.elim
   · intro h; exact h ((mem_filter.mp (he (show Sum.inr I∈ tag I J by simp [tag]))).2)
   intro h; exact h ((mem_filter.mp (he (show Sum.inl J∈ tag I J by simp [tag]))).2)
-- lift-conventions
abbrev heel (o y: Site c):=lift (y-o)
def shine (o y:Site c):ℂ := shimmer 0 o (route 0 (heel o y) 1)
@[simp] lemma shine_self (o: Site c): shine o o=1:=by
   unfold shine heel; rw [sub_self,show lift (0:Site c)=0 from ?_,route_same]; rfl
   ext; simp [lift]
lemma shore (o i: Site c)(p:Walk)(he: stop (0:Cover) p= heel o i): shine o i= shimmer 0 o p:=by rw [shine, occ_rays,occ_rays,he, route_end]
lemma heels (v:Strut c)(o i:Site c)(h:10* separation i o < c.val): heel (act v o) (act v i)= v.1.act (heel o i):=by
  apply lift_eq_iff.mpr; refine ⟨?_,fun j=> ?_⟩
  · rw [← wrap_signed,heel,wrap_lift,v.1.act_sub]; change affine v.1 v.2 i-affine v.1 v.2 o=_; unfold affine; abel
  obtain ⟨j,rfl⟩:=v.1.perm.surjective j; have hp := component_le (i-o) j; unfold separation at h; unfold heel; rw [Signed.act_at]; split<;> omega
lemma shoes (hp: Warrant v g k)(o i)(hx: 10* separation i o < c.val):shine (act v o) (act v i)*g o= g i*shine o i:=by
   let W:=route 0 (heel o i) 1; have he:= flare_path hp.1 W o; have hh : shine (act v o) (act v i)=shimmer 0 (affine v.1 v.2 o) (W.map (·.rotate v.1)):=by
       apply Eq.trans (shore (act v o) (act v i) (W.map (·.rotate v.1)) ?_) rfl; rw [heels v o i hx]; have hm:= moved_stop v.1 (0:Cover) W; rw [show stop (0:Cover) W=_ from route_end .., v.1.act_zero] at hm; exact hm.symm
   rw [hh,mul_comm,← he, show stop o W=i from ?_,mul_comm]; rotate_left
   · rw [wrap_stop,show stop (0:Cover) W=heel o i from route_end ..,wrap_lift]; abel
   rfl
lemma glisten (t x:Site c)(w:Walk): shimmer t x w=1∨shimmer t x w=-1:=by
   induction w generalizing x with
   | nil=> left; rfl
   | cons a w ih=> obtain hx|hx:= seam_cases t (a.used x).1 (a.used x).2 <;> rcases ih (x+a.vec) with h|h <;> simp only [shimmer,glint,h,hx] <;> simp
lemma shines (o x:Site c): shine o x=1∨ shine o x=-1 := glisten ..
lemma realK {x:Grid c→EvenA c N}(b:Flavor N)(h1:Fit (x 1))(h:shadeG x)(he:Regal c N (x 1)=x 1)(i j:Site c): blot b (x 1) i j=g5*star (blot b (x 1) j i)*g5:=by
   let A:=feeF b (x 1); let Γ:=chirality c; have hG: A=star Γ*star A*Γ:= by have hp:=Stew.burst (x 1) b h1; rw [he] at hp; exact hp
   have hk : cell A i j=wave (g5*star (blot b (x 1) j i)*g5):=by
      rw [hG]; rw [show Γ=star (rides (Equiv.refl (Site c)) (fun _=>J0)) from chi_star.symm,star_star,cell_ride_right,cell_ride_left,Equiv.refl_apply,Equiv.refl_apply, show cell (star A) i j=star (cell A j i) from cell_flip ..]; rw [show cell A j i=wave _ from known x h h1 b j i,wave_star, cT]; simp only [J0,wave_mul]
   exact congr_arg gold hk|>.trans (leafy _)
lemma billsL (s: Equiv.Perm (Site c))(X: Site c→Bundle)(D:Sheet c)(i j:Site c): cell (star (rides s X)*D * rides s X) (s i) (s j)=star (X i) *cell D i j*X j:=by
    rw [ride_ad]; nth_rw 1 [show rides s X=star (rides s.symm (fun i=>star (X (s.symm i)))) from ((star_star _).symm.trans (congr_arg _ (ride_ad ..)))]
    rw [cell_ride_right,cell_ride_left]; simp
lemma rollsL {x: Grid c→EvenA c N}(hp:Warrant v g k)(h:Fit (x 1))(hf:shadeG x)(i j:Site c)(b:Flavor N):
    blot b (Diode N v k g (x 1)) (act v i) (act v j)=(g i*g j) • (k*blot b (x 1) i j*star k):=by
   unfold blot; rw [show feeF b (Diode N v k g (x 1))=_ from rite _ _ _ h]; change gold (cell (star (rides (act v) (lightP v k g))*feeF b (x 1)*rides (act v) (lightP v k g)) _ _)=_; rw [billsL,known x hf h b i j]; unfold lightP; simp only [star_smul,Matrix.smul_mul, Matrix.mul_smul,wave_star,star_star,wave_mul, smul_smul]
   obtain hx|hx:= hp.1.sign i <;> obtain hj|hj:=hp.1.sign j <;> simp only [hx,hj,star_one,star_neg,neg_mul_neg,one_mul,neg_mul, mul_one, neg_smul,one_smul,← wave_neg,leafy]
lemma booth (hp: Warrant v g k)(o x y:Site c)(h:10* separation x o < c.val)(hz:10*separation y o< c.val):shine (act v o) (act v x)*shine (act v o) (act v y)*(g x*g y) = shine o x * shine o y:=by
  have hh:=shoes hp o x h; have hv:=shoes hp o y hz; rcases hp.1.sign x with hk|hk <;> rcases hp.1.sign y with hp'|hp' <;> rcases hp.1.sign o with hi|hi <;> rw [hi,hk] at hh <;> rw [hi,hp'] at hv <;> simp_all <;> rw [←hh,←hv] <;> ring
end YM.QCD.Stew
