import YM.Poised.River
import YM.Poised.Canoe
import YM.Planned.PRIMARY_INTEGRAL_295.Streets
/-! # Full AP lifted kernel. Cover royalties, periodic rows.Countable movement including arbitrary seam moves. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson Tree RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type}{d k j n:ℕ}{c l:Side}
namespace Steed
open Pipes QCD.Kit QCD.Flume QCD.Cove QCD.Creek QCD.Loom QCD.Flume QCD.Fork QCD.Port QCD.Brick Lining Lining.Ferry
open Pressure Garden Run Laurent Carrier Next.Free
variable (R:Ratio c l)
lemma locPose (n:Side)(x:Cover)(w:Walk): seamPath (wrap n x) w * ap n x = ap n (Lattice.stop x w):=by
   induction w generalizing x with
   | nil=> simp [stop,seamPath]
   | cons a w ih=>
      let Φ := wrap n x
      rw [seamPath,stop,← ih]; rw [map_add,show wrap n (a.vec:Cover)=(a.vec:Site n) from ?_]; swap
      · unfold Step.vec; split <;> simp
      obtain ⟨a,_|_⟩:=a -- ctor Bool awkward
      · simp only [Bool.false_eq_true,if_false, Step.vec]; rw [seam_tick];ring
      simp only [↓reduceIte,Step.vec,← sub_eq_add_neg]; rw [mul_comm (seam _ _ _) _, mul_assoc]; apply congr_arg; have hx:=seam_tick (c:=n) (x-step a) a; rw [sub_add_cancel,map_sub,wrap_step] at hx; rw [hx, mul_comm (ap n _), ← mul_assoc, seam_sq, one_mul]
lemma rollAP (n:Side)(x y:Cover) : ap n x * occ (wrap n x) y = ap n (x+y):=by
   let p:= occ (wrap n x) y; rw [mul_comm,occ,locPose]; nth_rw 1 [← add_zero x]; rw [cover_along]; rw [show Lattice.stop 0 (route (0:Cover) y 1) = y from route_end ..]
lemma sameAP (u:Cover): ap l (R.count.val • u)=ap c u:=by
   unfold ap; apply prod_congr rfl; intro i _; apply congr_arg; simp only [Pi.smul_apply,nsmul_eq_mul, R.exact_size, Nat.cast_mul]; rw [mul_comm ↑↑R.count (u i), Int.mul_ediv_mul_of_pos_left]; exact_mod_cast R.count.property
lemma ownerAP (x:Cover): let z:= cellar R.count x
   ap c z * occ (R.embed (wrap c z)) (lift (wrap R.count x)) = ap l x:=by
   intro z; rw [←sameAP R z,R.embed_wrap,rollAP]; apply congr_arg; rw [add_comm]; exact (balance R.count x).symm
-- read every mask
variable (P:Flight j k) (h:l.val=c.val*P.L.val)
abbrev Rm (x: Bundle)(u v:Pipes.Shell) : ℂ:= match u,v with
   | Sum.inl u,Sum.inl v=> if u.2=v.2 then x u.1 v.1 else 0
   | Sum.inr u,Sum.inr v=> if v.2=u.2 then (Lat.wave g5 * star x*Lat.wave g5) v.1 u.1 else 0
   | _,_=> 0
lemma spin_patch(u v:Pipes.Shell): ∃ L:Bundle→L[ℝ]ℂ,∀ x,L x=Rm x u v:=by
   refine ⟨LinearMap.toContinuousLinearMap { toFun:=fun x=>Rm x u v,map_add':= ?_,map_smul':=?_ },fun _=>rfl⟩
   · intro x y; cases u <;> cases v <;> simp only [Rm] <;> simp [Matrix.mul_add,Matrix.add_mul] <;> split_ifs <;> simp
   intro r x; cases u <;> cases v <;> simp only [Rm] <;> simp <;> split_ifs <;> simp
lemma spin_eye (u v:Pipes.Shell) (x:Site l)(y:Site c): flareV (proton P h) (stretch (Site l) (x,u)) (stretch (Site c) (y,v))=Rm (cell (proton P h) x y) u v:=by
   cases u <;> cases v <;> simp only [Rm,stretch,Equiv.coe_fn_mk,Sum.elim_inl,Sum.elim_inr]
   · rfl
   · rfl
   · rfl
   next u v=>
     rw [←cell_flip, ← Garden.halo]; rfl
-- fluct Z.alloc
abbrev gears (x z:Cover): Bundle:= sheath P (wrap P.L x) z
def arch (u v:Pipes.Shell) (x z:Cover) :ℂ:= Rm (gears P x z) u v
lemma boot (x y:Site c) (r:Site P.L) (hk:4≤k): HasSum (fun u=>caption P h (sheath P r u) x y r u) (cell (proton P h) ((sliceL P h).assemble (x,r)) y):=by
    refine Pi.hasSum.mpr (fun i => Pi.hasSum.mpr (fun j=>?_))
    obtain ⟨σ,C,hσ,hC,H⟩:=reserves_font P.legal hk
    let ζ:=occ ((sliceL P h).embed x) (lift r)
    have he:= (splash_budget x y (((H P r [] (by simp) i j).unweighted hσ.le).2.1)).of_norm.hasSum.mul_left ζ
    convert! he using 1
    · funext u; by_cases h:x+wrap c u=y <;> simp only [caption,h, Matrix.smul_apply,Matrix.zero_apply, ↓reduceIte,Garden.sheath,Matrix.of_apply,splashL, mul_zero]; unfold ζ; ring
    change proton P h ((sliceL P h).assemble (x,r),i) (y,j)=_
    rw [show proton P h=printed P h [] from eligible P h P.legal hk [] (by simp)]; exact prints ..
lemma reinsH (x:Cover)(y:Site c)(u v:Pipes.Shell)(hk:4≤k):let p:= wrap c (cellar P.L x); let q:= flareV (proton P h) ((stretch _) (wrap l x,u)) ((stretch _) (y,v)); HasSum (fun z: Cover=> if p+wrap c z=y then ap l x*ap c (cellar P.L x+z)*arch P u v x z else 0) q:=by
   intro s q; have hg:=Streets.around (sliceL P h) x; let p:=cellar P.L x; let r:= wrap P.L x; let F(k:Cover):=caption P h (gears P x k) s y r k
   obtain ⟨L,hL⟩:=spin_patch u v; have hz:=L.hasSum (boot P h s y r hk); unfold q; rw [spin_eye,hg,←hL]; change HasSum _ (L (cell (proton P h) ((sliceL P h).assemble (s,r)) y)); change HasSum (fun i=>L (F i)) _ at hz
   have he (z:Cover): L (F z)= if s+wrap c z=y then ap l x * ap c (p+z)*arch P u v x z else 0:= by
      unfold F caption; split; swap; · exact map_zero _
      let I:= occ ((sliceL P h).embed s) (lift r); let D:= occ s z; change L ((I*D) • _)= _
      have hu:ap c p*I=ap l x:=ownerAP (sliceL P h) x; have hd : ap c p * D=ap c (p+z):= rollAP c p z
      have hm: ap l x*ap c (p+z)=I*D:=by rw [←hu,←hd,mul_mul_mul_comm,ap_sq,one_mul]
      rw [hm]; unfold arch; rw [←hL]
      -- coefficients AP real
      have hI : star I=I:= (realSeam ..).1; have hD':star D=D:= (realSeam ..).1; let a:= (I*D).re
      rw [show I*D=(a:ℂ) from Complex.conj_eq_iff_re.mp (by change star (I*D)=I*D; rw [star_mul,hD',hI,mul_comm]) |>.symm]; exact map_smul L a _
   simp_rw [he] at hz; exact hz
lemma cons (u v:Pipes.Shell): Rm 1 u v= if u=v then 1 else 0:=by
   cases u <;> cases v <;> simp [Rm,wave_mul,g5_sq,wave_one,Matrix.one_apply,Prod.ext_iff,eq_comm]; all_goals split_ifs <;> tauto
end Steed
end YM.Massive.Poised
