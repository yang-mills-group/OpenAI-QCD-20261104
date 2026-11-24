import YM.MassiveQCD.Plate.Payer
/-!
# Cover costs of every publication label in the same filtered price. Even one.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{k B N:ℕ}{h θ φ b t C τ ε v w d₁ z x δ A:ℝ}{U I J:Type}[Fintype I]
namespace Film
variable (p:I→Site c)(a:ℝ)(S:Set (Finset I))(Y:Cove.Hat c)
local notation "Z"=> coverNumber B Y.place
noncomputable def allowance (H B:ℕ)(a b:ℝ) :ℝ:=b*(B+B+1:ℝ)^4*H/a+1
-- singleton & many, withdrawing over *nonempty* few.Dense.Face
lemma totalFuel (H:ℕ)(hz:Fires p H)(h:∀ i∈S,Spaced p i B)(ha:0<a)(hv:0≤b) (hp:(∑ i∈ Cupola.mixed p Y.place B,b^i.card*Real.exp (-(2*a)*Z)) ≤ 1) :
  (∑ i∈ seats p S Y,b^i.card * Real.exp (-(2*a)*Z)) ≤ allowance H B a b:=by
    let u:= Cupola.barn p Y.place; let v:= u.image fun i=>({i}:Finset I); let f (i:Finset I):= b^i.card * Real.exp (-(2*a)*Z); let g:= Cupola.mixed p Y.place B; let r:= Real.exp (-(2*a)*Z); let z:ℝ:=Z
    have hh:seats p S Y⊆ v∪g:=by
       intro i hi; obtain ⟨hi,hu,hx⟩:= (mem_filter.mp hi).2; by_cases H:i.card=1; · obtain ⟨j,hj⟩:= card_eq_one.mp H; subst i; exact mem_union_left _ (mem_image.mpr ⟨j,(inside ..).2 (hx (by simp)),rfl⟩)
       exact mem_union_right _ ((Cupola.shore ..).mpr ⟨hx,by have hx:=card_pos.mpr hu; omega,h i hi⟩)
    have hk i:0 ≤f i:=mul_nonneg (pow_nonneg hv _) (Real.exp_nonneg _); refine (sum_le_sum_of_subset_of_nonneg hh (fun i _ _=>hk i)).trans ((show _ ≤ (∑ i∈v,f i)+∑ i∈g,f i from ?_).trans (add_le_add ?_ hp)) -- lemma
    ·  have hf :0 ≤ ∑ i∈v∩g,f i:= sum_nonneg fun i _=>hk i; exact (le_add_of_nonneg_right hf).trans (le_of_eq sum_union_inter)
    -- equal footing : T.card=1
    rw [sum_image (s:=u) (show Set.InjOn (fun i:I=>({i}:Finset I)) _ from fun i _ j _ h=> singleton_injective h)]; unfold f; simp only [Finset.card_singleton,pow_one,sum_const,nsmul_eq_mul]; let HH :ℝ:=H; let D:=(B+B+1:ℝ)^4; have he: (u.card:ℝ)≤ z*D*HH:=by unfold z D HH; exact_mod_cast barncard p _ H B hz
    have hz: z*a*r ≤ 1:=by
       have h':0 ≤ z:=Nat.cast_nonneg _; unfold r; rw [neg_mul,Real.exp_neg]; apply (mul_inv_le_iff₀ (Real.exp_pos _)).mpr; rw [one_mul]; refine le_trans ?_ (Real.add_one_le_exp _)
       change z*a ≤ 2*a*z+1; nlinarith -- syntax edit!
    have hr:0≤ r:= Real.exp_nonneg _; have hf:0≤ D:=pow_nonneg (by positivity) _; apply (le_div_iff₀ ha).mpr
    change (u.card:ℝ)*(b*r)*a ≤ b*D*H; dsimp only [HH] at he; nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he (mul_nonneg hv hr)) ha.le, mul_le_mul_of_nonneg_left hz (mul_nonneg (mul_nonneg hv hf) (Nat.cast_nonneg (α:=ℝ) H))]
variable (q:I→Bool)(F: Patron.Rail c (ample N I) U) (θ:ℝ)
local notation "St"=> Seats N p F S
local notation "S!"=> publication N p q F S θ
lemma budgeting (h:Pill F t θ B (v+2*a) C)(hm:0< θ)(hp:∀ i U,Well N p θ q (F.warp i U))(w:I→ℝ)(he:∀ i, |w i|≤ b)(_hb:0≤b)(h₀:0≤ε)(ht:0<τ)(hv:τ≤C)(hz:∀ i, (∑ j∈ seats p S (F.addr i), b^j.card*Real.exp (-(2*a)*coverNumber B (F.addr i).place))*τ/C ≤ ε) : Stock N S! B τ v θ ε w:=by
    obtain ⟨G, hG,hF⟩:=h.sold.cost; refine ⟨fun i=> G i.1,fun i U=> (cost_g N p q F S θ hm i U (hp i.1 U)).trans (hF i.1 U),?_⟩; intro V
    let H (i:U):=taxed (oriD F) G C i; let H' (i:U):= if V∈(F.addr i).place then H i*Real.exp ((v+2*a)*coverNumber B (F.addr i).place) else 0
    let W i:=(F.addr i).place; let X (i:St) := if V∈ W i.fst then fares N S! (fun j=> G j.1) w τ i*Real.exp (v*coverNumber B (W i.1)) else 0
    have hf i:0≤ G i:=(norm_nonneg _).trans (hF i 1); have hC:0 < C:= ht.trans_le hv
    have hX i:0 ≤ X i:=by unfold X fares taxed; split; exact mul_nonneg (mul_nonneg (pow_nonneg ht.le _) (mul_nonneg (prod_nonneg fun i _=> abs_nonneg _) (hf _))) (Real.exp_nonneg _); exact le_rfl
    have uv:SumBudget (fun i=> ε*H' i) ε := by simpa only [mul_one] using budget_scale h₀ (show SumBudget H' 1 from hG V)
    refine budget_fiberwise (Sigma.fst (β:=fun i:U=> ↥(seats p S (F.addr i)))) hX ?_ uv -- body; estimate
    intro i u hh; let J:= seats p S (F.addr i); let g (j:↥J):St:=⟨i,j⟩; let A:= Finset.univ.image g
    have hg:Injective g:=fun _ _ h=> Sigma.mk.inj_iff.mp h|>.2|>eq_of_heq; have hU:u⊆ A:=by rintro ⟨k,j⟩ hj; have hm:k=i:=hh _ hj; subst k; exact mem_image_of_mem g (mem_univ j)
    apply le_trans (sum_le_sum_of_subset_of_nonneg hU (fun i _ _=> hX i)); rw [sum_image hg.injOn]; unfold H'; split
    swap; next hx=> rw [show ∑ j:↥J,X (g j)= 0 from sum_eq_zero (fun j _=>if_neg hx),mul_zero]; -- bad; edit
    next h0=>
      let k:=coverNumber B (W i); let TR:=(oriD F i).card; have hy (j:↥J): X (g j) ≤ H i * Real.exp ((v+2*a)*k)*(b^j.val.card*Real.exp (-(2*a)*k))*(τ/C) :=by
          have hu:0≤ τ/C:= (div_pos ht hC).le; have ht':1≤ TR:= Finset.card_pos.mpr (F.addr i).alive; unfold X fares; rw [if_pos (show V∈W _ from h0)]; have hp: τ^TR ≤ C^TR*(τ/C):=by
             rw [← div_le_iff₀' (pow_pos hC TR),←div_pow]; exact (pow_le_pow_of_le_one hu ((div_le_one₀ hC).mpr hv) ht').trans_eq (pow_one _) -- lemma sig
          -- inequality exponents
          have h1: (∏ j∈j.val, |w j|) ≤ b^j.val.card:=by rw [← prod_const]; exact prod_le_prod (fun _ _=>abs_nonneg _) (fun i _=>he i)
          change τ^TR*((∏ j∈j.val, |w j|)*G i)*Real.exp (v*k)≤_; refine (mul_le_mul_of_nonneg_right (mul_le_mul hp (mul_le_mul_of_nonneg_right h1 (hf _)) (mul_nonneg (prod_nonneg fun i _=> abs_nonneg _) (hf _)) (mul_nonneg (pow_nonneg hC.le _) hu)) (Real.exp_nonneg _)).trans_eq ?_
          change _=C^TR*G i*Real.exp _*(_*_)*_; rw [show v*(k:ℝ)=(v+2*a)*k+-(2*a)*k from by ring,Real.exp_add]; ring
      refine (sum_le_sum fun i _=> hy i).trans ?_
      rw [← Finset.sum_mul,← Finset.mul_sum,mul_assoc]; refine le_trans (mul_le_mul_of_nonneg_left (?_ : ((∑ j:↥J,b^j.val.card*Real.exp (-(2*a)*k))*(τ/C)) ≤ ε) ?_) (le_of_eq (mul_comm ..)); rotate_left
      · exact mul_nonneg (mul_nonneg (pow_nonneg hC.le _) (hf i)) (Real.exp_nonneg _)
      refine le_trans ?_ (hz i); rw [← sum_coe_sort (seats p S (F.addr i)),mul_div_assoc]

open Pressure Orbit Jets.Touch ConnectedActivityE6
variable (L:Side)(M:ℝ)
lemma priceFade (t:ℝ) (h:0<M): Rate su L t (fun x=> (priceK L M x)⁻¹):=by
    refine (Rate.monitor_cutoff (show 0<M/4 by linarith) (show (0:ℝ)<2 by norm_num)).congr (Eventually.of_forall fun x:ℝ=>?_)
    unfold priceK Delay.hatWin; dsimp only; rw [← Real.exp_neg,Real.rpow_two]; congr 1; ring
lemma div_price (x:ℝ): priceK L (M/4) x* priceK L (M/4) x=priceK L (M/2) x:=by unfold priceK Delay.hatWin; rw [← Real.exp_add]; congr 1; ring
lemma govern (H:ℕ)(ha:0<a){x:ℝ→ℝ}(v:ℝ)(hM:0<M)(e:ℝ)(hp:Rate su L e x) : ∀ᶠ t:ℝ in atTop,∀ (σ:ℝ)(N:ℕ) (c:Side)(U I:Type)[Fintype I](F: Patron.Rail c (ample N I) U)(A:Set (Finset I))(p:I→ Site c)(q:I→Bool)(b:ℝ)(w:I→ℝ), Fires p H → (∀ i∈A,Spaced p i (radiusB t)) → Pill F b σ (radiusB t) (v+2*a) (priceK L M t) → (∀ i U,Well N p σ q (F.warp i U)) → (∀ i, |w i|≤ |x t|) → 0<σ → Stock N (publication N p q F A σ) (radiusB t) (priceK L (M/2) t) v σ ((priceK L (M/4) t)⁻¹) w:=by
   let C:=(M/2:ℝ); have hC:0<M/4:=by linarith
   let D t:=allowance H (radiusB t) a (|x t|); let e':=max e 0; have he:Rate su L e' D:=by
      have hx:Rate su L e fun t=> |x t|:=fun v h=> (hp v h).mono (fun i h=>  le_trans (abs_abs (x i)|>.le) h); let K t:=(radiusB t+radiusB t+1:ℝ); have hk:Rate su L 0 K:= (Rate.radius_price.add Rate.radius_price).add (Rate.const 1)
      have hf:Rate su L e fun i=>|x i| *(K i)^4*H/a:=by simpa only [div_eq_mul_inv,zero_mul,add_zero] using (((hx.mul (hk.pow 4)).mul_right (H:ℝ)).mul_right a⁻¹)
      exact Rate.add (hf.weaken (le_max_left ..)) ((Rate.const 1).weaken (le_max_right ..))
   let g t:=priceK L M t; let V t:=priceK L (M/2) t; let W t:=priceK L (M/4) t
   filter_upwards [(he.mul (priceFade L (M/4) (-e'-1) hC)).below (by linarith) 1 zero_lt_one, Cupola.exsteam L ha H hp] with i hi hW
   intro σ N c U I _ F A p q b w hx ht hf hV he hh
   have hz: V i*V i=g i:=by unfold g V priceK Delay.hatWin; rw [← Real.exp_add]; congr 1; ring
   have hz':W i*W i= V i:= div_price L M i
   have h₁:0<W i:=Real.exp_pos _; have h₂:1≤V i:= Real.one_le_exp (by unfold Delay.hatWin; positivity)
   have h₃:0<V i:=zero_lt_one.trans_le h₂; have h₄:0<g i:=Real.exp_pos _
   have ht': D i≤ W i :=by apply (div_le_one₀ h₁).mp; rw [div_eq_mul_inv]; exact (le_abs_self _).trans hi
   refine budgeting p a A q F σ hf hh hV w he (abs_nonneg _) (inv_pos.mpr h₁).le h₃ ((le_mul_of_one_le_left h₃.le h₂).trans_eq hz) fun j=>?_ -- order
   apply (div_le_iff₀ h₄).mpr; have hp':=mul_le_mul_of_nonneg_right ((totalFuel p a A (F.addr j) H hx ht ha (abs_nonneg _) (hW c I p (F.addr j).place hx)).trans ht') h₃.le; refine hp'.trans_eq ?_; change W i*V i=(W i)⁻¹ *g i; rw [← hz,← hz',← mul_assoc,← mul_assoc]; field_simp
end Film
end YM.MassiveQCD.Plate

#print axioms YM.MassiveQCD.Plate.Film.govern
