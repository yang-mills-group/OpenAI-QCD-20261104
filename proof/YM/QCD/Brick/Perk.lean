import YM.QCD.Brick.Seal
/-! # Reusable power factor recursions on Peg -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Brick
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Garden Fork Leaf Tee Flume YM.Next.Free Laurent
variable {c f : Side} {F:Kit.Rail f c}{N m:ℕ}{o:Site f}{w:Keys c N→ℕ}{p r q t v C:ℝ}{D:Type*}[Fintype D]{b:Bool}
lemma regio (x:Alg D): x∈ region (univ:Finset D):=by
   rw [← write x]; apply Subalgebra.sum_mem; intro s _; apply Subalgebra.smul_mem
   obtain ⟨π,-,-,he⟩:= expression s; rw [he]; exact Subalgebra.list_prod_mem _ (by simp only [List.mem_ofFn]; rintro _ ⟨i,rfl⟩; exact Creek.marked _ _ (mem_univ _)) -- name
section hers
local notation "A"=> EvenA f N
lemma vacant1 (X: EvenA f N)(hx:coef ∅ X.val=0)(i:Finset (Keys f N))(he:i.card<2): coef i X.val=0:=by
   by_cases hi:i.card=0
   · rw [card_eq_zero.mp hi,hx]
   exact measured _ (by omega) _
lemma vacant2 (X: EvenA f N)(hx:coef ∅ X.val=0)(i:Finset (Keys f N))(he:i.card<4): coef i (X-Stew.stage 2 X).val=0:=by
   by_cases hi:i.card%2=1; · exact measured i hi _
   rcases (show i.card=0∨i.card=2 by omega) with h|h
   · change coef i (X.val-panel 2 X.val)=0; rw [map_sub,angel,if_neg (by omega),Finset.card_eq_zero.mp h,hx,sub_zero]
   change coef i (X.val-panel 2 X.val)=0; rw [map_sub,angel,if_pos h,sub_self]
lemma omnibus (x:Keys f N) : ∃ v: Accent N,pitchQ (locationP x) v=x:=by rcases x with i|i; exact ⟨.inl (i.1.2,i.2),rfl⟩; exact ⟨.inr (i.1.2,i.2),rfl⟩
def fern (L:Side):ℝ:= (L.val:ℝ)⁻¹
lemma capeQ (L : Side): cape L 0 ^2=fern L^3:=by unfold cape Kit.slope fern; rw [mul_pow,inv_pow,Real.sq_sqrt (by positivity : 0 ≤ (L.val:ℝ))]; ring
lemma fern_pos (L:Side):0 < fern L:=by unfold fern; positivity
lemma fern_one (L:Side): fern L ≤1:= inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr L.property)
variable {L':Side}(hA:∀ i:Accent N,Lien w (fern L') p (C*t*cape L' 0) (staff o F i)) (hp:0<p)(ht:0<t)(he:0≤C) (h :640*C*cape L' 0≤1)
include hA hp ht h he
-- lag bound row as grew-one.E incidence shape2.
lemma taxi (X :Alg (Keys f N))(hr:∀ i: Finset (Keys f N), i.card < m → coef i X=0): visc w p (apple F N X)≤(640*C*cape L' 0)^m * visc (Stew.lens o) t X:=by
   let v:= C*t*cape L' 0; have hv:0≤v:=by unfold v; positivity [cape_pos L' 0]
   let W:ℝ:=320*v; have hw:0≤W:=by unfold W; positivity
   apply sprinkles hp hw (apple F N) univ _ _ (regio X) hr (show 2*W=_ by unfold W v; ring) (by positivity [cape_pos L' 0]) h ht.le
   intro i _; obtain ⟨z,hz⟩:=omnibus i; let x:= locationP i; let j:= heel o x; let D:= separation x o; have hh : size j≤4*D:= trail_size ..
   obtain ⟨hs,h₁⟩:= (hA z).poses j _ hh; rw [shim, hz] at hs h₁; have he (U):‖shine o U‖=1:=by rcases shines o U with h|h <;> simp [h]
   constructor
   · rw [dryL,load_scale,he,one_mul] at h₁; exact h₁.trans (le_mul_of_one_le_left hv (by norm_num))
   rw [vc_scale, he,one_mul] at hs; apply hs.trans; change v*(2+(↑(4*D):ℝ)*(fern _))^2 ≤ (1+(D:ℝ))^2*W
   have hf:= fern_one L'; push_cast; refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity [fern_pos L']) (b:=(4:ℝ)*(1+D)) ?_ _) hv).trans ?_
   · linarith only [mul_le_mul_of_nonneg_left hf (show 0 ≤ (4:ℝ)*D by positivity)]
   unfold W; nlinarith only [mul_nonneg hv (sq_nonneg (1+(D:ℝ)))]
def ott (C:ℝ):ℝ:= (640*C)^4*2
lemma broad (i: EvenA f N)(hr:coef ∅ i.val=0): visc w p (apple F N i.val) ≤ (640*C)^2 * fern L'^3 * Sen o t i:=by
   apply (taxi hA hp ht he h _ (vacant1 _ hr)).trans_eq; rw [mul_pow (640*C), capeQ]; rfl
abbrev nickel (L:Side)(i:Bool):= fern L ^ (if i then 5 else 4)
def coreP (C:ℝ):=16*340*C^2
lemma rebate (X: EvenA f N)(hC: coef ∅ X.val=0)(hv:Fit X)(hQ:lights o b (grasp X.val)): visc w p (apple F N X.val) ≤ (coreP C+ ott C)* nickel L' b* Sen o t X:=by
   let v:= C*t*cape L' 0; have hx :0≤ v:= by unfold v; positivity [cape_pos L' 0]
   let q:= nickel L' b; let r:= fern L'; have hr:0<r:=fern_pos L'
   let Z:= Stew.stage 2 X; let P':=(X-Z).val; have hz: X.val=Z.val+P':=by change _=Z.val+(X.val-Z.val); abel
   let B:= Sen o t X; have hB:0≤B:=norm_nonneg _; let R:=grasp X.val; have hd: Z.val=form R:=rank_two X hv
   have hu := sumBl o X.val ht.le
   have ht₁ : visc w p (apple F N Z.val) ≤ coreP C*q * B:=by
      let T:= ∑ i,∑ j, ‖R i j‖* ↑(pieD (Stew.lens o) (tag i j))
      rw [hd]; refine (river o R hQ hA hp hr.le (fern_one L') hx).trans (le_trans ?_ (mul_le_mul_of_nonneg_left hu (show 0 ≤ coreP C*q by unfold coreP q nickel; positivity [fern_pos L'])))
      change _ ≤ coreP C*q*(T* t^2); unfold coreP q tips nickel; cases b <;> simp only [Bool.false_eq_true,if_true,↓reduceIte] <;> simp_rw [mul_pow,capeQ]; all_goals unfold T R; exact le_of_eq (by ring) -- watch simp
   have hp₀: visc w p (apple F N P') ≤ ott C*q*B:=by
      apply (taxi hA hp ht he h P' (vacant2 _ hC)).trans; have hx: Stew.plank o t P' ≤ 2*B := (vertex X.val Z.val).trans (by rw [two_mul]; exact add_le_add le_rfl (Stew.absolute o 2 X ht.le))
      refine (mul_le_mul_of_nonneg_left hx (show 0 ≤ (640 * C * cape L' 0)^4 by positivity [cape_pos L' 0])).trans ?_
      have hg : cape L' 0 ^4 ≤ q:= by rw [show 4=2*2 from rfl,pow_mul,capeQ,← pow_mul]; apply pow_le_pow_of_le_one (fern_pos L').le (fern_one L') (by split <;> norm_num)
      rw [mul_pow (640*C)]; exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (pow_nonneg (by linarith) _)) (by linarith : 0≤2*B)).trans_eq (by unfold ott; ring)
   calc
     _ = visc w p (apple F N (Z.val+P')):=by apply congr_arg; exact congr_arg _ hz
     _ ≤ (coreP C+ ott C)*q* B:= by rw [map_add]; exact (vested ..).trans ((add_le_add ht₁ hp₀).trans_eq (by ring))
end hers
end YM.QCD.Brick
