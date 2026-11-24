import YM.QCD.Plum.Rind
import YM.QCD.RP.Yard
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Plum
open Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox Jets
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder Classical
variable {n c f : Side}{F:ℕ}{β:ℝ} {R:Cells.Cut c} {K:KernelChoices}
open Tide Flume YM.Next.Free Kites Acre Rails Rain Loom Fleet
variable {X:Pixel c F}{J:Patch}{w z:ℝ} {A:Set (Site c)}
variable (hp:Healing J X)(he:Continuous X)(hv:Cvol X=1)(h: Even c.val)(hN:4≤c.val)
noncomputable abbrev WithinP (w:ℝ)(x: Stud c F):Prop:=∀ i, ‖x i‖ ≤ w
lemma WithinP.tower {x:Stud c F}(hp: WithinP w x): WithinP (c:=c) w (tallH R x):=fun i=> (roll_fields _ _).trans ((thin _).trans ((roll_fields _ _).trans (hp _)))
lemma WithinP.nonneg {x:Stud c F}(hp:WithinP w x): 0 ≤ w:= (norm_nonneg _).trans (hp 1)
lemma WithinP.square {x:Stud c F}(hp:WithinP w x): WithinP (c:=c) (w^2) (tallH R x*x):=fun i=> (norm_mul_le ..).trans ((mul_le_mul (tower hp i) (hp i) (norm_nonneg _) hp.nonneg).trans_eq (pow_two w).symm)
lemma fresh1 (X:Pixel c F):Tide.fresh X 1= Cvol X:=by unfold Tide.fresh Cvol; apply integral_congr_ae; filter_upwards with i; rw [Pi.one_apply,mul_one]; rfl
lemma tall1 : tallH R (1: Stud c F)=1:=funext fun i=>by rw [huesT,Pi.one_apply,tilt_one,Pi.one_apply]
local notation "d"=> longM J
include hp he hv h hN
lemma branchy (p : Site c) (a : Axis) (i : Axis → ℕ) (hi : 2*(i a+2*d) ≤ c.val) (x:Stud c F) (H:Fence (RP.square p i) x) (hA:WithinP w x): ∃ q y, Fence (RP.square q (Function.update i a (2*(i a+d)))) y ∧ WithinP (F:=F) (w^2) y ∧ ‖Tide.fresh X x‖^2 ≤ ‖Tide.fresh X y‖:=by
    obtain ⟨m,hm⟩:= h; let r:= i a; let R : Cells.Cut c:= ⟨⟨m,by omega⟩,by dsimp; omega, .link,a,p a-(d:Per c)⟩; let j:= update i a (2*(r+d)); let q:=Function.update p a (p a- (↑(r+2*d):Per c)); have hr:2*(r+2*d)≤c.val:=hi
    have ha: RP.square p i⊆eaves R d:=by
         intro x hx; have ht: (x a-p a).val<r:=hx a; have hx:R.distance x=(x a-p a).val+d:=by unfold Cells.Cut.distance; change (x a-(p a- (d:Per c))).val=_; rw [show x a- (p a-(d:Per c))=(↑((x a-p a).val+d):Per c) from (by rw [Nat.cast_add,ZMod.natCast_zmod_val]; abel),ZMod.val_natCast_of_lt (by omega)]
         change d≤_∧_ < m; rw [hx]; omega
    have hY : RP.square p i ⊆ RP.square q j:=by
         intro x hx s; by_cases e:s=a
         · subst s; have ht: (x a-p a).val<r:=hx a; simp only [q,j,update_self]; rw [show x a-(p a- (↑(r+2*d):Per c))=(↑((x a-p a).val+(r+2*d)):Per c) from (by simp only [Nat.cast_add, ZMod.natCast_zmod_val]; abel), ZMod.val_natCast_of_lt (by omega)]; omega
         unfold j q; rw [update_of_ne e,update_of_ne e]; exact hx s
    have hg : Set.MapsTo R.reflect (RP.square p i) (RP.square q j):=by
         intro x hx s; by_cases e:s=a
         · subst s; let b:=(x a-p a).val; have he:b<r:= hx a; have hx:R.reflect x a=2*(p a-(d:Per c))-1-x a:=by simpa only [R,Cells.Kind.shift,Nat.cast_one] using (R.reflect_here x)
           simp only [q,j,update_self,hx]; rw [show 2* (p a-(d:Per c))-1-x a - (p a- (↑(r+2*d):Per c))=(↑(r-(b+1)):Per c) from (by rw [Nat.cast_sub (by omega),Nat.cast_add, Nat.cast_add,show (b:Per c)=x a-p a from ZMod.natCast_zmod_val _]; push_cast; ring), ZMod.val_natCast_of_lt (by omega)]; omega
         unfold j q; rw [R.reflect_there x (show s ≠ R.pos from e),update_of_ne e,update_of_ne e]; exact hx s
    refine ⟨q,tallH R x*x,(H.tall hg).mult (H.high hY), hA.square,?_⟩; have hb := sheen hp he Fence.one (H.high ha) (show R.kind=.link from rfl) (by change 2 ≤ m; omega); simpa only [tall1,one_mul,fresh1,hv,norm_one] using hb
lemma grows (t :ℕ)(p:Site c)(a:Axis)(i:Axis→ℕ)(hi: 2^t*(i a+2*d) ≤ c.val)(x: Stud c F)(H:Fence (RP.square p i) x)(hx:WithinP w x):∃ q y,Fence (RP.square q (Function.update i a (2^t*(i a+2*d)-2*d))) y ∧ WithinP (F:=F) (w^(2^t:ℕ)) y∧ ‖Tide.fresh X x‖^(2^t:ℕ) ≤ ‖Tide.fresh X y‖:=by
    induction t with
    | zero=> exact ⟨p,x,by simpa only [pow_zero,one_mul,Nat.add_sub_cancel,Function.update_eq_self] using H,by simpa using hx,by simp⟩
    | succ t ih=>
       rw [pow_succ',mul_assoc] at hi; obtain ⟨q,y,Y,hy,hh⟩:= ih (by omega); let r:=i a; let j:= update i a (2^t*(i a+2*d)-2*d); have het: 2*d ≤2^t*(i a+2*d):= (show 2*d ≤ i a+2*d by omega).trans (le_mul_of_one_le_left (by omega) (show 1 ≤(2:ℕ)^t from one_le_pow₀ (by omega)));
       have hk:j a+2*d=2^t*(i a+2*d):=by unfold j; rw [update_self]; omega
       obtain ⟨s,z,Z,hZ,hQ⟩:= branchy hp he hv h hN q a j (by rw [hk]; exact hi) y Y hy -- he shadow
       refine ⟨s,z,?_,by simpa only [pow_succ (2:ℕ) t, pow_mul] using hZ,?_⟩
       · rw [show 2^(t+1) * (i a+2*d)-2*d=2*(j a+d) from (by rw [pow_succ',mul_assoc,← hk]; omega), show Function.update i a (2*(j a+d))=Function.update j a (2*(j a+d)) from (update_idem ..).symm]; exact Z
       rw [pow_succ,pow_mul]; exact (pow_le_pow_left₀ (by positivity) hh _).trans hQ
end YM.QCD.Plum
