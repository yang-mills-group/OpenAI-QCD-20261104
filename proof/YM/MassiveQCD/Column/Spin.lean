import YM.QCD.Dust.Rose

/-! # Split (spin)
 Keeping rank-two phase symmetries only where needed. Two budgets, with a single
 interface `Rebate`. Fee for ALL higher powers and for mass primaries is ramped by
 L² from full unmarked sharp. With vanishing rank-two part on constant spin jets
 (use torus lifts), ramp only by L. Use the same more exact through-order chart
 interpretation of `Fugue` (so can use the NORMALIZED heur kernel, not doing
 differentiability at flagged supports). See `Transmission` for use.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Brick
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Garden Fork Leaf Tee Flume YM.Next.Free Laurent
variable {c f : Side} {F:Kit.Rail f c}{N m:ℕ}{o:Site f}{w:Keys c N→ℕ}{p r q t v C:ℝ}{D:Type*}[Fintype D]{b:Bool}
section strength
variable {L':Side}(hA:∀ i:Accent N,Lien w (fern L') p (C*t*cape L' 0) (staff o F i)) (hp:0<p)(ht:0<t)(he:0≤C) (h :640*C*cape L' 0≤1)
include hA h ht hp he
lemma rebate_weak (X: EvenA f N)(hC: coef ∅ X.val=0)(hv:(Stew.stage 2 X).val=form (grasp X.val))(hQ:lights o b (grasp X.val)): visc w p (apple F N X.val) ≤ (coreP C+ ott C)* nickel L' b* Sen o t X:=by
   let v:= C*t*cape L' 0; have hx :0≤ v:= by unfold v; positivity [cape_pos L' 0]
   let q:= nickel L' b; let r:= fern L'; have hr:0<r:=fern_pos L'
   let Z:= Stew.stage 2 X; let P':=(X-Z).val; have hz: X.val=Z.val+P':=by change _=Z.val+(X.val-Z.val); abel
   let B:= Sen o t X; have hB:0≤B:=norm_nonneg _; let R:=grasp X.val; have hd: Z.val=form R:=hv
   have hu := sumBl o X.val ht.le
   have ht₁ : visc w p (apple F N Z.val) ≤ coreP C*q * B:=by
      let T:= ∑ i,∑ j, ‖R i j‖* ↑(pieD (Stew.lens o) (tag i j))
      rw [hd]; refine (river o R hQ hA hp hr.le (fern_one L') hx).trans (le_trans ?_ (mul_le_mul_of_nonneg_left hu (show 0 ≤ coreP C*q by unfold coreP q nickel; positivity [fern_pos L'])))
      change _ ≤ coreP C*q*(T* t^2); unfold coreP q tips nickel; cases b <;> simp only [Bool.false_eq_true,↓reduceIte] <;> simp_rw [mul_pow,capeQ]; all_goals unfold T R; exact le_of_eq (by ring) -- watch simp
   have hp₀: visc w p (apple F N P') ≤ ott C*q*B:=by
      apply (taxi hA hp ht he h P' (vacant2 _ hC)).trans; have hx: Stew.plank o t P' ≤ 2*B := (vertex X.val Z.val).trans (by rw [two_mul]; exact add_le_add le_rfl (Stew.absolute o 2 X ht.le))
      refine (mul_le_mul_of_nonneg_left hx (show 0 ≤ (640 * C * cape L' 0)^4 by positivity [cape_pos L' 0])).trans ?_
      have hg : cape L' 0 ^4 ≤ q:= by rw [show 4=2*2 from rfl,pow_mul,capeQ,← pow_mul]; apply pow_le_pow_of_le_one (fern_pos L').le (fern_one L') (by split <;> norm_num)
      rw [mul_pow (640*C)]; exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (pow_nonneg (by linarith) _)) (by linarith : 0≤2*B)).trans_eq (by unfold ott; ring)
   calc
     _ = visc w p (apple F N (Z.val+P')):=by apply congr_arg; exact congr_arg _ hz
     _ ≤ (coreP C+ ott C)*q* B:= by rw [map_add]; exact (vested ..).trans ((add_le_add ht₁ hp₀).trans_eq (by ring))
end strength
end YM.QCD.Brick
namespace YM.QCD.Dust
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Brick
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Garden Fork Leaf Tee Flume YM.Next.Free Laurent Reggae
open PhysicalNext.JointLoad MultiNext.SignedSource
variable {c f L:Side} {j k N n:ℕ} {C h1 h2 u v w A t:ℝ} {X:Support f}{o:Site f}{R:BudgetPoint}{a:Site c}
variable {M:Grid f→EvenA f N}
variable {S:Kit.Rail f c}(K: Hera.Rights su k) (hp: Woven o X R t M C)
variable (hQ:∀ i:Accent N,Lien (Stew.lens a) (fern L) u (v*t*cape L 0) (staff o S i))(h:0<u) (ht:0<t) (hV:0 ≤ v) (hv:640*v*cape L 0≤1) {b:Flavor N}
variable (g: Crate c N →L[ℝ]ℝ)(he:∀ x,‖g x‖ ≤ Stew.plank a u x)
private lemma virtue_wk (v:ℝ): 0 ≤ coreP v+ott v∧ (640*v)^2≤Jive v∧ coreP v+ott v ≤ Jive v:=by
    unfold Jive coreP ott; refine ⟨by positivity,?_,?_⟩ <;> nlinarith [sq_nonneg v,pow_nonneg (by have hh:=sq_nonneg v; exact hh) 2]

/-- Role parameter `rate` for a column. -/
abbrev rampFee (gain:Bool)(L:Side):ℝ:= if gain then L.val else (L.val:ℝ)^2
lemma rampFee_gate (L:Side)(gain:Bool):1 ≤ (L.val:ℝ) ∧ (L.val:ℝ) ≤ rampFee gain L:=by
    have h :1≤ (L.val:ℝ):= Nat.one_le_cast.mpr L.property
    cases gain
    · exact ⟨h,le_self_pow₀ h two_ne_zero⟩
    exact ⟨h,le_rfl⟩

/-- Vanishing rank-two read with weaker symmetries. We carry the read in the full basis of generators. -/
def VanishAt (o:Site f) (V:EvenA f N) : Prop :=
   (Stew.stage 2 V).val=form (grasp V.val) ∧ lights o false (grasp V.val)

/-- Rate holds on vector basis selected from Woven. -/
structure Rebate (o:Site f)(M:Grid f→EvenA f N)(gain:Bool) :Prop where
   all :∀ X,mud (M X)=0
   rank:gain → VanishAt o (M 1)
   gauge:shadeG M
include hQ h ht hV hv he hp
set_option maxHeartbeats 320000 in
lemma Rebate.pay {gain:Bool}(H:Rebate o M gain)(hh:1 ≤ k):
    let F:= (g.comp (bill S N) ∘ M); let Q:=Jive v * (C * rampFee gain L)
    0 ≤ Q ∧ Ease.Charm R X F ∧ R.supBounds o X F (Q*fern L^3) ∧ ‖F 1‖ ≤ Q*fern L^5 ∧
       ∀ (i: Directions su f)(T:ℝ), Lyre.Sized T i R o → Mom.screen X i∈Mom.Maps o X 1 → ‖fderiv ℝ (F ∘ increment 1) 0 i‖ ≤ (T*K.fee)*Q*fern L^4 :=by
    intro F Q
    let y:= (g.comp (bill S N)); let a':= fern L; have ht':0<a':=fern_pos L
    have hp0:=hp.travel
    obtain ⟨h₀,hp₁,hp₂⟩:= virtue_wk v
    have hL:0≤ Jive v:= h₀.trans hp₂
    have ha: Ease.Charm R X M:= ⟨hp.room,hp.use⟩
    have hF:=ha.scales y
    have hr := rampFee_gate L gain
    have hcap : 1 ≤ rampFee gain L:=hr.1.trans hr.2
    have hQ':0≤Q:=by unfold Q; positivity
    let Z:= Jive v*C
    have hz:0≤Z:=by unfold Z; positivity
    have hq :Z ≤ Q:= by unfold Z Q; gcongr; exact le_mul_of_one_le_right hp0 hcap
    have hW : R.supBounds o X F (Z*a'^3):=by
        refine ⟨by positivity,?_⟩
        intro U hU l hh hx; rw [left_linear (L:=y) l (hp.use U hU) hh] -- L binder?
        exact (he _).trans ((broad hQ h ht hV hv _ (leftovers hp H.all U hU l hh)).trans ((mul_le_mul (mul_le_mul_of_nonneg_right hp₁ (pow_nonneg ht'.le 3)) (hp.pole _ hU l hh hx) (norm_nonneg _) (by positivity [fern_pos L])).trans_eq (by unfold a' Z; ring)))
    have hL0:0 < (L.val:ℝ):= zero_lt_one.trans_le hr.1
    refine ⟨hQ',hF, ⟨by positivity [fern_pos L],fun U hU l hh hx=> (hW.2 _ hU l hh hx).trans (mul_le_mul_of_nonneg_right hq (pow_nonneg ht'.le _))⟩,?_,?_⟩
    · cases hx:gain
      · change ‖F 1‖ ≤ Jive v*(C*rampFee gain L)*a'^5
        rw [hx]; apply (hW.2 1 (AnalyticBridge.VerifiedReset.flat_ok ..) [] (by simp) (by simp)).trans_eq
        unfold Z rampFee a' fern; simp; field_simp; try ring
      change ‖g (bill S N (M 1))‖ ≤ Jive v*(C*rampFee gain L)*fern _^5
      apply (he (bill S N (M 1))).trans; have hz':=H.rank hx
      have he' := rebate_weak hQ h ht hV hv _ (H.all 1) hz'.1 hz'.2 -- shadow
      apply he'.trans; let f' := Jive v; have he : nickel L false=fern L^4 := rfl
      rw [he]; apply (mul_le_mul (mul_le_mul_of_nonneg_right hp₂ (pow_nonneg ht'.le _)) (hp.sizeU _ (AnalyticBridge.VerifiedReset.flat_ok ..)) (norm_nonneg _) (mul_nonneg hL (pow_nonneg ht'.le 4))).trans_eq
      rw [hx]; change _= f'* (C* (L.val:ℝ))*fern L^5; unfold f' a' fern; field_simp; try ring
    intro i T hh hh'; have he:1 ≤ R.order:=(le_trans (by decide) R.order_ge)
    have hl:= K.born 1 (fun _ : Fin 1=>i) (fun _=>T) (show 1 ≤ k from by assumption) he hF hW (AnalyticBridge.VerifiedReset.flat_ok ..) (fun _=>hh)
    rw [iteratedFDeriv_one_apply,Fintype.prod_unique] at hl
    apply hl.trans; rw [mul_assoc (T*K.fee)]; apply mul_le_mul_of_nonneg_left _ (mul_nonneg hh.1 (zero_le_one.trans K.large))
    have he: Z*a'^3 = Z*(L.val:ℝ)*a'^4:=by unfold a' fern; field_simp
    rw [he]; refine mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hr.2 hz).trans_eq ?_) (pow_nonneg ht'.le _); unfold Z Q; ring
end YM.QCD.Dust
