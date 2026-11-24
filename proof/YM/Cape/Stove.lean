import YM.Cape.Pico
import YM.Mills.Spoors
/-!
# Handling soft mask terms in marked K transactions
Bank plane implementation. Fixed old unmarked representation. Right Spine.
Soft entries appear precisely when W overlaps flags; we do not substitute an all-flat complement.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Cape
open ConnectedActivityE6 QCD Lattice Finset Wilson RG Pressure Function Filter MeasureTheory NormedSpace
open Sway OrbitG Ruby Kites Grass Lat Cove Push Push.AbsoluteSums Patron
open Cupola Ribbon Loom Loom.Fleet Plate Twist Stitch
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ}{I D Z U:Type}[Fintype I]
variable (p:I→Site c)(q:I→Bool) (Y:Lure c N I Z) (F:Film c N I D)(M: Patron.Rail c N U)
variable {t v:ℝ}
local notation "K"=> Keys c N
local notation "R"=> Ribbon.Spine I
local notation "Φ"=> banknote N p v
local notation "Sh"=> withdraw N p v
local notation "φ"=> rootR R (Keys c N)
local notation "X"=> torah p F M v
local notation "Z'"=> vesta p Y v
local notation "P"=> Stalk p Y F M v
local notation "Γ"=> fog p Y F M v
variable (hY:Y.On p q t) (hF:F.Beat N p q t)(hM:M.Reg t)(hC:∀ i,Cove.shadeG (M.warp i))(hP:0<v)
local notation "T!"=> Trail Z' X t
local notation "Cz"=> Cob p Y F M v
local notation "H"=> coverP p Y F M v t

open Jets.Touch Footprint Trees GasP Creek
-- total not beyond Vale.A
variable {w:Z→ℝ}{g:U⊕ D→ℝ}{h:ℝ}{a s b m A B e ε δ u z κ C x:ℝ}{n:ℕ}
lemma sketch (hv:0<κ)(hp:0 ≤ g) (he:Ac.Hit (Ruby.home X) n (taxed (oriD X) g s) a m) (ht:1 ≤ b)(hh:Real.exp A*κ*b ≤ s)(hW:1 ≤ κ): Ac.Hit (Ruby.home X) n ((metal X A)*taxed (oriD X) g b) a (κ⁻¹*m):=by
    intro x; let Pz:=oriD X; let y i:=(Pz i).card; refine budget_mono (budget_scale (inv_pos.mpr hv).le (he x)) (fun i=>?_) fun i=>?_
    · split; next h=> exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (mul_nonneg (pow_nonneg (zero_le_one.trans ht) _) (hp _))) (Real.exp_pos _).le
      next _=> exact le_rfl
    split
    next h=>
       dsimp only [Pi.mul_apply,metal,taxed]; rw [Real.exp_nat_mul,←mul_assoc,←mul_assoc,←mul_assoc]
       apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; apply mul_le_mul_of_nonneg_right _ (hp _); have ht':1 ≤ y i:=(Finset.card_pos.mpr ((X).addr i).alive)
       rw [mul_comm (κ⁻¹), ← div_eq_mul_inv, le_div_iff₀ hv]; apply le_trans ?_ (pow_le_pow_left₀ (by have h:=zero_lt_one.trans_le ht; positivity) hh _); rw [mul_pow,mul_pow,mul_right_comm]
       exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_self_pow₀ hW (Nat.ne_of_gt ht')) (pow_nonneg (Real.exp_pos _).le _)) (pow_nonneg (zero_le_one.trans ht) _)
    next=> rw [mul_zero]
include hY hF hM hP
lemma gold (S E e:ℝ)(hp:0 ≤ w)(hx:∀ i V,Stitch.Tablet.credits v (Y.wick i V) ≤ wig w i)(he:Quits X n S s (a+b) v)(hw:Ac.Hit Y.spot n w (a+b+1) E)(ht:1 ≤ e)(hh:Real.exp E*e*B≤ s)(hB:1 ≤ B)(hb:e⁻¹*S+e⁻¹*S*Animals.ballCost n*E ≤ m)(ha:0≤a)(hp':0 < b)(hK:degreePrice n m b ≤ δ)(hm:0 < m)(hg:δ < 1)(hV:m*(1-δ)⁻¹ ≤ C): Film.Stock N H n B a v C (fun _=>1) :=by
   obtain ⟨g,hΦ,hq⟩:=he.cost; have ht':0 ≤ g:=fun i=> (norm_nonneg _).trans (hq _ 1)
   refine arise p q Y F M hY hF hM hP hp ht' hx hq (fun i=> budget_loosen (scoring p Y F M E hp ht' hw (sketch p F M (zero_lt_one.trans_le ht) ht' hΦ hB hh ht) hb ha hp' hK hm hg hB i) hV) -- need parentheses
omit hY hM hP hF
-- radix ceiling not just at outer B.A.
def ash (L:Side)(x:ℝ):=fan L (1/8) x
-- choose eCoeff > gain wanted post Stock. S total per-site.
lemma teases (L:Side)(a b r z v' S₀:ℝ)(ha:0≤a)(hb:0 < b)(hz:z>0)(hr:0≤r)(hp:r+z<v')(hm:0<S₀) : ∀ᶠ x:ℝ in atTop, ∀ (n:ℕ), n≤ highR L x →∀ (c:Side)(N:ℕ)(D Z I U:Type)[Fintype I] (p:I→ Site c) (q:I→Bool) (Y:Lure c N I Z)(F:Film c N I D) (M:Patron.Rail c N U)(t v:ℝ)(w:Z→ℝ),Y.On p q t→F.Beat N p q t→M.Reg t→0<v→0≤w→(∀ i V,Tablet.credits v (Y.wick i V) ≤ wig w i)→Ac.Hit Y.spot n w (a+b+1) (ash L x)→ Quits (torah p F M v) n S₀ (taxK L x v') (a+b) v → Film.Stock N (coverP p Y F M v t) n (taxK L x r) a v (taxK L x z)⁻¹ (fun _=>1):=by
   let s':=(v'-r-z)/2; have hs:0<s':=by unfold s'; linarith
   let Gd x:= taxK L x (s'+z)
   let f x:=16*(1+(highR L x:ℝ))^4; have hf: Rate su L 0 f:= (Kites.radH L).mul_left 16
   let m' x:= S₀+S₀*f x *ash L x; let m x:=(Gd x)⁻¹*m' x
   have hu: Rate su L 0 m':=Rate.add (Rate.const _) (by simpa only [zero_add] using (hf.mul_left S₀).mul (show Rate su L 0 (ash L) from Rate.rpow_monitor _)) -- increased? inspect
   have hv: Rate su L (-1) m:=by simpa only [add_zero] using (couplings L (a:=-1) (add_pos hs hz)).mul hu
   have hp0:= (((hf.mul hv).mul_right b⁻¹).mul_left 4).below (by norm_num) (1/2) (by norm_num)
   have hp' := upperTax L s' hs _ _ (hu.mul_right ((1-1/2:ℝ)⁻¹))
   have ht:∀ᶠ x in atTop, ash L x ≤ s'*fan L (1/3) x:=by filter_upwards [(Seat.keeps.timesL (L:=L) (a:=1/8) s'⁻¹) (1/3) (by norm_num)] with x h; refine (div_le_iff₀' hs).mp (?_: ash L x /s' ≤_); rw [div_eq_inv_mul]; exact (le_abs_self _).trans h
   filter_upwards [hp0,hp',ht] with x hx hZ h n hn c N D Z I U _ p q Y F M t v w hY hF hM hP hw hX hB hE
   have hz : 1 ≤ Gd x:= Real.one_le_exp (mul_nonneg (add_pos hs hz).le (fan_pos ..).le)
   have hd:f x≥0:=by unfold f; positivity
   have h0:(0:ℝ) ≤ ash L x:=(fan_pos ..).le; have h1:0 < Gd x:=zero_lt_one.trans_le hz
   have hγ:m' x>0:= add_pos_of_pos_of_nonneg hm (mul_nonneg (mul_nonneg hm.le hd) h0); have hQ:0 < m x:=mul_pos (inv_pos.mpr h1) hγ
   have hi : (Animals.ballCost n:ℝ) ≤ f x:=by unfold f Animals.ballCost; push_cast; apply (pow_le_pow_left₀ (show 0≤ (n:ℝ)+ n+1 from by positivity) (show (n:ℝ)+n+1 ≤ 2*(1+(highR L x:ℝ)) by exact_mod_cast (by omega : n+n+1≤2*(1+highR L x))) 4).trans ; linarith -- exact_mod_cast
   refine gold p q Y F M hY hF hM hP S₀ (ash L x) (Gd x) hw hX hE hB hz ?_ (Real.one_le_exp (mul_nonneg hr (fan_pos ..).le)) ?_ ha hb (δ:=1/2) ?_ hQ (by norm_num) ?_
   · unfold Gd taxK; rw [← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone; unfold s' at h ⊢; linarith only [h]
   · unfold m m'; rw [mul_add]; apply add_le_add le_rfl; simp_rw [←mul_assoc]; gcongr
   · unfold degreePrice Trees.stretch; refine le_trans ?_ ((le_abs_self _).trans hx); rw [div_eq_mul_inv]; gcongr
   dsimp only [m]; rw [mul_assoc]; apply (mul_le_mul_of_nonneg_left hZ (inv_pos.mpr h1).le).trans_eq; unfold Gd taxK; rw [←Real.exp_neg,← Real.exp_add, ←Real.exp_neg]; apply congr_arg; ring
end YM.MassiveQCD.Cape
#print axioms YM.MassiveQCD.Cape.teases
