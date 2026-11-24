import YM.QCD.Reef.Crown
import YM.QCD.RP.Yard
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Plum
open Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox Jets
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder Classical
variable {n c f : Side}{F:ℕ}{β:ℝ} {R:Cells.Cut c} {K:KernelChoices}
open Tide Flume YM.Next.Free Kites Acre Rails Rain Loom Fleet
variable {X:Pixel c F}{J:Patch}{w z:ℝ} {A:Set (Site c)}
local notation "V"=> Stud c F
lemma goodN {y:Stud c F} (h:Stays y)(hp:Continuous X): Integrable (fun i=>ber _ (Cove.light _ (X i)*y i)) (prior su c):=(( (stays ((Cove.lightC _).comp hp)).mult h).flows ((ber _).continuous_of_finiteDimensional)).intg _
lemma spell (hp:Continuous X){x y:Stud c F} (hx:Stays x)(hy:Stays y): Tide.fresh X (x+y)=Tide.fresh X x+ Tide.fresh X y:=by
     unfold Tide.fresh; simp only [Pi.add_apply,mul_add,map_add, integral_add (goodN hx hp) (goodN hy hp)]
lemma spend (x: Stud c F)(t:ℂ): Tide.fresh X (t • x)=t • Tide.fresh X x:=by unfold Tide.fresh; rw [← integral_smul]; apply integral_congr_ae; filter_upwards with i; rw [Pi.smul_apply,mul_smul_comm,map_smul]
structure Fence (S:Set (Site c))(x:Stud c F):Prop where
    hp: Tide.Stays x
    he: Uses S x
    hz: Neutral x
lemma Fence.add {x y: Stud c F}(hp:Fence A x)(hq:Fence A y): Fence A (x+y):=⟨(hp.hp.both hq.hp).flows continuous_add,⟨fun U W e=>congr_arg₂ (·+·) (hp.he.1 _ _ e) (hq.he.1 _ _ e),fun U=> by obtain ⟨p,h⟩:=hp.he.2 U; obtain ⟨q,hq⟩:=hq.he.2 U; exact ⟨p+q,by rw [Pi.add_apply,h,hq,map_add]⟩⟩,fun k U=> by simp_rw [Pi.add_apply,map_add,hp.hz _ _, hq.hz _ _]⟩ -- defmap rfl
lemma Fence.mass {x:Stud c F}(hp:Fence A x)(c':ℂ): Fence A (c' • x):=⟨hp.hp.flows (continuous_id.const_smul c'),⟨fun U W h=> congr_arg (c' • ·) (hp.he.1 U W h),fun U=>by obtain ⟨p,h⟩:= hp.he.2 U; exact ⟨c' • p,by rw [Pi.smul_apply,h,map_smul]⟩⟩,fun U k=>by simp_rw [Pi.smul_apply,map_smul,hp.hz _ _]⟩
lemma Fence.mult {x y: Stud c F}(hp:Fence A x)(hq:Fence A y): Fence A (x*y):=⟨hp.hp.mult hq.hp,⟨fun U W h=>congr_arg₂ (·*·) (hp.he.1 _ _ h) (hq.he.1 _ _ h),fun U=>by obtain ⟨p,h⟩:= hp.he.2 U; obtain ⟨q,hq⟩:= hq.he.2 U; exact ⟨p*q,by rw [Pi.mul_apply,h,hq,map_mul]⟩⟩,fun U k=> by simp_rw [Pi.mul_apply,map_mul,hp.hz _ _,hq.hz _ _]⟩
lemma Fence.high {x:Stud c F}{B:Set (Site c)}(hp:Fence A x)(hq:A⊆B): Fence B x:= ⟨hp.hp,staysS x hp.he hq,hp.hz⟩
lemma Fence.tall {x:Stud c F}{B:Set (Site c)}(hp:Fence A x)(hq:Set.MapsTo R.reflect A B): Fence B (tallH R x):=⟨tallCost x hp.hp, tallSite x A B hp.he hq,coated _ _ (floods _ (coated _ _ hp.hz))⟩
lemma Fence.one : Fence A (1:Stud c F):=⟨stays continuous_const, ⟨fun _ _ _=> rfl,fun U=>⟨1,(map_one _).symm⟩⟩,fun k U=>map_one _⟩
private lemma conjugate (a b z w : ℂ) (A : 0 ≤ a) (B : 0 ≤ b)
    (H : ∀ c : ℂ, 0 ≤ a+c*z+star c*w+c*star c*b) : star z=w := by
  have ha := Complex.nonneg_iff.mp A; have hb := Complex.nonneg_iff.mp B; have hr := Complex.nonneg_iff.mp (H 1); have hi := Complex.nonneg_iff.mp (H Complex.I); rw [Complex.nonneg_iff] at A B; simp [Complex.mul_im, ← A.2, ← B.2] at hr hi; apply Complex.ext <;> simp <;> linarith
lemma sheen {x y: Stud c F} (hp:Healing J X)(he:Continuous X) (hx:Fence (eaves R (longM J)) x) (hy:Fence (eaves R (longM J)) y)(hr:R.kind=.link)(hz:2≤ R.half.val) : let L (u v:Stud c F):= Tide.fresh X (tallH R u*v); ‖L x y‖^2 ≤ ‖L x x‖ * ‖L y y‖:=by -- implicit x
    intro L; have hv(u:V)(h:Fence (eaves R (longM J)) u):0 ≤ L u u:= hp.rails R hr hz _ h.hp h.hz h.he
    let v:=tallH R x; let w':= tallH R y
    have ha: Stays v:= tallCost x hx.hp; have hb: Stays w':= tallCost y hy.hp
    have hm (c:ℂ)(x:V)(h:Stays x) : Stays (c • x) := h.flows (continuous_id.const_smul c)
    have H (s:ℂ) : 0 ≤ L x x+s*L x y+star s*L y x+s*star s*L y y:=by
         apply (hv _ (hx.add (hy.mass s))).trans_eq; change Tide.fresh X _=_
         rw [show tallH R (x+s • y)=v+ star s • w' from funext fun i=> by simp [huesT,v,w'], add_mul,mul_add,mul_add]
         have h1:Stays (star s • w'):=hm _ _ hb; have h2:Stays (s • y):=hm _ _ hy.hp
         have hf{u v:V}(hu:Tide.Stays u)(hv:Tide.Stays v): Tide.Stays (u+v):=(hu.both hv).flows continuous_add
         rw [spell he (hf (ha.mult hx.hp) (ha.mult h2)) (hf (h1.mult hx.hp) (h1.mult h2)), spell he (ha.mult hx.hp) (ha.mult h2), spell he (h1.mult hx.hp) (h1.mult h2)]; simp only [mul_smul_comm,smul_mul_assoc,spend,smul_eq_mul]; unfold L v w'; ring
    have hQ:=hv x hx; have hy':=hv y hy; apply Cells.schwarz hQ hy'; intro t; have h:= H (star t); rw [star_star] at h; rw [mul_comm (star t) t, ← conjugate (L x x) (L y y) (L x y) (L y x) hQ hy' H] at h; exact h
end YM.QCD.Plum
