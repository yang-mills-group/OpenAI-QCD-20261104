import YM.QCD.Port.Gloom
/-! # fixed-moment estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Port
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Tree
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Paths Metric Extra AtomF Sway OrbitG ConnectedActivityE6 Push.AbsoluteSums Footprint Jets.Touch Pressure
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {j k:ℕ}{a A b C r R Y X w θ D hH e u:ℝ}
variable (L:Side)
-- shutter β-hat at x fine; a post-L cost

def wink (x:ℝ):ℝ:= betaF su x L^(-(1/2):ℝ)
def coreRate (x:ℝ):ℝ:= betaF su x L ^ (-(2/5):ℝ)
def highW (K θ x:ℝ):= K*fan L θ x

def prize (U V p d θ:ℝ)(x:ℝ)(b:ℕ):ℝ:= (2*(radiusB x:ℝ)+1)^4*(d*wink L x)+(Real.exp (-p * fossil (radiusB x) b)+(coneK L θ x/2)⁻¹ * (AValue U x))*V
where AValue U x:= U*(radiusB x+1:ℝ)^5*fiery su x L
lemma prize_rate (U V p d θ:ℝ)(hh:θ≠0)(b:ℕ)(hp:0<p): Rate su L (-7/16) (fun x=> prize L U V p d θ x b):=by
   unfold prize
   apply Rate.add
   · have ht:= (Rate.mul (w:=fun x:ℝ=> (2*↑(radiusB x)+1:ℝ)^4) (v:=fun x=>d*wink L x) (Rate.pow ((Rate.radius_price.mul_left _).add (Rate.const _)) _) (Rate.power.mul_left _)); exact ht.weaken (by norm_num)
   apply Rate.mul_right; apply Rate.add; · simpa only [sub_zero] using Touch.pale (L:=L) (v:=-7/16) p 0 hp b
   unfold prize.AValue
   have hp:= (shade_e L hh).mul ((((Rate.radius_price.add (Rate.const (G:=su) (L:=L) 1)).pow 5).mul_left U).mul Rate.flame); exact hp.weaken (by norm_num)
lemma bounty (F B:ℕ)(K x U V p θ β D Z:ℝ)(hp:0<p)(ht:0<θ):∀ᶠ x in atTop,
   F*(AtomF.rays*(Z/(coneK L θ x/2)*prize.AValue L U x)) ≤ coreRate L x ∧
   highW L K β x^2*fingers F^2*(2*prize L U V p D θ x B) ≤coreRate L x :=by
   have he : Rate su L (-7/16) (fun x=> F*(AtomF.rays*(Z/(coneK L θ x/2)*prize.AValue L U x))):=by
     apply Rate.mul_left; apply Rate.mul_left
     simp_rw [div_eq_mul_inv Z (coneK .. /2)] -- placeholder may not know
     unfold prize.AValue
     exact (((shade_e L ht.ne' |>.mul_left Z)).mul (((Rate.radius_price.add (Rate.const _)).pow 5|>.mul_left U).mul Rate.flame) |>.weaken (by norm_num))
   have hf := ((Rate.mul_right (Rate.pow ((Rate.rpow_monitor (G:=su) (L:=L) β).mul_left K) 2) (fingers F^2)).mul ((prize_rate L U V p D θ ht.ne' B hp).mul_left 2))
   filter_upwards [he (-(2/5)) (by norm_num),hf (-(2/5)) (by norm_num)] with x hx hk using ⟨(le_abs_self _).trans hx,(le_abs_self _).trans hk⟩

def foamD (L: Side)(P:Plan j)(d:ℝ) := massL L*(stamp P L*d⁻¹)* massL L
lemma frameTrust (P:Plan j)(p' D K γ t g:ℝ)(B F i:ℕ)(a b A C w h h' θ :ℝ)(N:Plan k) (hT:0<t)(hh:0 < θ)(hK:0<K): ∀ᶠ x in atTop,∀ (f c :Side),2*(radiusB x+1)< f.val→
    ∀ (G:Flight j k)(e:f.val=c.val*G.L.val), G.L=L→∀ (O:Offer 1 a A)(Q: Offer 2 b C)(m:ℝ), |m| ≤ wink L x →
      let s:=coneK L θ x; let Z:= park G e P O Q (haloK L x) m
      Species G e w h s t h' B Z → ∀ W:ℕ→Atom su 2, ∀ U:Swathe G e Z W N w s t p' D i, ∀ y : Varn f c,waxV y=none→∀ V:Grid f, nearby V (orbitM (sliceL G e) y) (radiusB x+1) (fiery su x L)→ load (fun _=> highW L K γ x) (light _ (sliceF U F (radiusB x) y V)) ≤ coreRate L x:=by
   obtain ⟨Y,hy,hY⟩:= Fork.travelQ
   filter_upwards [Delay.shift_pos su L,kentucky L hh,bounty L F i K 0 Y p' t θ γ (foamD L P h') D hT hh,filming L hh Y] with x hx hv hB hp f c he G e hg O Q m hM s Z H W U y ht V hH
   have hz : 0<s:=mul_pos hh (pow_pos hv.1 _)
   let q:= radiusB x; let o:= orbitM (sliceL G e) y
   have hV : 0 < fiery su x L:=mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr hx)) (Real.exp_pos _)
   obtain ⟨X,hX⟩:= hY q f _ V o he hV.le hH
   -- eliminate ht; get new hX by general y? o let
   rcases y with ⟨i,z⟩|⟨i,z⟩ <;> change z=none at ht <;> subst z
   · exact le_trans (scalar_trim U F q V i X hz hX hp hT.le) hB.1
   let q':= foamD L P h'
   have hη : ‖dusk G e N Z 1‖≤q'* wink L x:= by
      apply le_trans (unspent H); rw [hg]; unfold q' foamD; have ht:= healthy P L; have hv:= H.calf; have he:= mass_pos L
      exact (le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM ht.le) (by positivity)) he.le) he.le) (le_of_eq (by ring)))
   have hp' := crop_p U F q V i X hz hX hp hT.le hη
   have hh' := farm_price U F q i V none hz (show 0<highW L K γ x from mul_pos hK (fan_pos ..)) _ _ (fun _=> le_rfl) (fun _=> le_rfl)
   apply le_trans hh'; apply le_trans _ hB.2; rw [two_mul]; exact mul_le_mul_of_nonneg_left (add_le_add hp'.1 hp'.2) (by positivity)
lemma funding (F B b:ℕ)(γ p q u w D θ:ℝ)(hp:u>w)(v :ℝ): Rate su L v (fun x=> loftCost p q F b (radiusB x) (highW L D γ x) u w):=by
   have hg:=Jets.Touch.pale (L:=L) (v:=v) u w hp b
   unfold loftCost; apply Rate.add; exact (hg.mul_right _).mul_left _
   exact (((Rate.pow ((Rate.rpow_monitor (G:=su) (L:=L) γ).mul_left D) 2).mul_right (fingers F^2)).mul ((hg.mul_right p).mul_left 2)).weaken (by linarith)
lemma upward (F p b:ℕ)(w D η u θ Y X q Ω:ℝ)(he:η>u):
    let v x:=highW L D θ x; let C x:=2*coreRate L x*Real.exp u+loftCost Y X F b (radiusB x) (v x) η u
    ∀ᶠ x in atTop,C x≤1 ∧ Real.exp 1*rem L p (radiusB x) w (C x) Ω ≤ betaF su x L^(-(3/8):ℝ):=by
    intro v C
    have hp: Rate su L (-(2/5)) C:= (Rate.power.mul_left 2|>.mul_right (Real.exp u)).add (funding L F p b θ Y X η u D 0 he _)
    have hv : Rate su L (-(2/5)) (fun x=> Real.exp 1*rem L p (radiusB x) w (C x) Ω):=by
       simp_rw [leeway L (C _)]; exact (((earned (L:=L) p w Ω).ruled.mul hp |>.weaken (by linarith)).mul_left _)
    filter_upwards [hp.below (by norm_num) 1 one_pos,hv (-(3/8)) (by norm_num)] with x h w using ⟨(le_abs_self _).trans h,(le_abs_self _).trans w⟩
end YM.QCD.Port
