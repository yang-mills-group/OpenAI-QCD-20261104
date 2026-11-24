import YM.Portland.Earn
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC.Brave.CoatB
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward Grass.Ovule
open YM.Next.Free QCD.Flume QCD.Globe QCD.Globe.HalfMass Finset NormedSpace
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical ComplexOrder
variable {A B:Type*}[Fintype A][Fintype B]{c f:Side} {n k j F:ℕ}
variable (x y:Site c)(i j:Lat.Fiber) (a b:Flavor F)
set_option quotPrecheck false
local notation "M"=> Modes c F
local notation "F!"=> Keys c F
variable (X:Spike)(D: Fields c F)(T:Flavor F→ Sheet c)
local notation "Kq"=> Cove.Keys c F
local notation "BO"=> Ovule.core (Cove.Keys c F)
variable (p q: Lat.Row c)
variable (ht:a≠b) (he: Stew.panel 2 D=form (Matrix.blockDiagonal T))
local notation "sι"=> spr (talon b q)
local notation "s²"=> spr (graphB a p)
local notation "sp"=> spr (planeL a i)
local notation "sQ"=> spr (planeR b j)
open QCD.Comet
variable (Z:ℂ)
local notation "u"=> (Z * BO (exp D))
local notation "B₁"=> (spr (planeR b j))
variable (K C0 C2 C4:ℝ)
local notation "xc"=> spinPrice Lat.g5
local notation "bc"=> wingC K C0 C2 C4
local notation "varA" p=> vary (X:=Pairs (Modes c F)) (Sum.inl (p,a))
local notation "varB" p=> vary (X:=Pairs (Modes c F)) (Sum.inr (p,b))
variable (hD:Plus D)(hZ:Z * Grass.Ovule.core (Cove.Keys c F) (exp D)≠0)
variable (hp:∃ y:Alg (Cove.Keys c F),True) -- unused drop
-- estimator per pair plus E4. normalized.L.Clock true.
variable (hk:0 ≤K)(hv:0 ≤C0)(h₂:0≤C2)(h₄:0≤ C4)(hM:Tempo (T a))(hW:∀ i x,‖stalk (T i) x‖ ≤K)
-- invoice for any command Hearth.D...
variable (t:ℕ) (P: PCAC.Deck c F)
abbrev Bordered (P:PCAC.Deck c F):Prop:=∀ i j,P i j≠0→ i.2=a∧ j.2=b
local notation "H"=> Z* BO (exp D)
structure Tuned (a b:Flavor F)(t:ℕ)(X:Fields c F)(p v w:ℝ)(P:PCAC.Deck c F):Prop where
   apart : Bordered a b P
   lineB : ∀ i j,t< separation i.1.1 j.1.1→ P i j=0
   bent :∀ i j:Lat.Row c,separation i.1 j.1 ≤ t→ QCD.Comet.BreezeX X p v w (P (i,a) (j,b))
variable (h:Tuned a b t (Z • NormedSpace.exp D) C0 C2 C4 P)
-- fiscal exponent bounds. suprem
include h
lemma feast (v:Grid c): passenger P v=∑ i:Lat.Row c,∑ j:Lat.Row c, pairD (i,a) (j,b) (P (i,a) (j,b) v):=by
    rw [pax_apply]; unfold Modes; rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro i _; rw [sum_eq_single a]
    · rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro j _; rw [sum_eq_single b]; intro k _ hk; have he : P (i,a) (j,k)=0:=not_ne_iff.mp fun hP => hk (h.apart _ _ hP).2; rw [he,ContinuousMap.zero_apply,map_zero]; simp
    · intro z _ hz; apply sum_eq_zero; intro j _; have he:P (i,z) j=0:=not_ne_iff.mp fun hP=> hz (h.apart _ _ hP).1; rw [he,ContinuousMap.zero_apply,map_zero]
    simp
include ht he hD hZ hM hW hk hv h₂ h₄
noncomputable def circleW (t:ℕ):ℝ:= ((t+t+1)^4:ℕ) * (Fintype.card Lat.Fiber:ℝ)
noncomputable def rowsW(c:Side):ℝ:= Fintype.card (Lat.Row c)
noncomputable def rootM (t:ℕ)(K C0 C2 C4:ℝ):ℝ:= (Fintype.card Lat.Fiber:ℝ)*circleW t*wingC K C0 C2 C4
lemma caption : ‖(Z*BO (exp D))⁻¹ * murphy a b i j (passenger P 1)‖ ≤ rowsW c * circleW t *wingC K C0 C2 C4+ C0* bins Kq D 4:=by
   rw [feast a b D Z C0 C2 C4 t P h] -- order check
   let f(k l:Lat.Row c):= aroma a b i j k l (P (k,a) (l,b) 1) H; let w(k l:Lat.Row c):= bins Kq (pairD (k,a) (l,b) D) 2; have hm:= (wingPos K C0 C2 C4 hk hv h₂ h₄)
   have hp(k:Lat.Row c): ∑ l, ‖f k l‖ ≤ circleW t*bc +∑ l,C0*w k l:=by
       let S:= Lattice.halo t {k.1}; let Y:Finset (Lat.Row c):= S×ˢ univ; have hX: (Y.card:ℝ)≤circleW t:=by
            have hx:S.card ≤ (t+t+1)^4:=by simpa only [card_singleton,one_mul] using Lattice.Corona.halo_size ({k.1}:Support c) t
            unfold Y circleW; rw[card_product,card_univ,Nat.cast_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hx) (Nat.cast_nonneg _)
       have hj(l:Lat.Row c):l∈ Y ↔ separation k.1 l.1 ≤ t :=by
           unfold Y S; simp only [mem_product,mem_univ,true_and,and_true,halo_spec]; simp [separation_comm]
       rw [← Finset.sum_subset (subset_univ Y) (f:=fun l=>‖f k l‖) fun l _ hv=>by rw [show f k l=0 from ?_,norm_zero]; unfold f; rw [h.lineB _ _ (show t < separation k.1 l.1 from lt_of_not_ge (mt (hj l).mpr hv))]; simp [aroma]]
       apply le_trans (b:=∑ l∈Y,(bc+C0*w k l)) (sum_le_sum fun l ht' => jumper i j a b D T k l ht he Z K C0 C2 C4 hD hZ hk hv h₂ h₄ hM hW (P (k,a) (l,b)) (h.bent _ _ ((hj l).1 ht'))); rw [sum_add_distrib,sum_const,nsmul_eq_mul]; exact add_le_add (mul_le_mul_of_nonneg_right hX hm) (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _=>mul_nonneg hv (r_nn ..))
   simp_rw [map_sum,mul_sum]; refine (norm_sum_le ..).trans ((sum_le_sum fun p _=> (norm_sum_le ..).trans (hp p)).trans ?_); rw [sum_add_distrib,sum_const,nsmul_eq_mul,card_univ]
   apply add_le_add; · change rowsW c * (circleW t * bc)≤ _; rw [mul_assoc]
   simp_rw [← mul_sum]; apply mul_le_mul_of_nonneg_left _ hv; rw [sum_comm]; let H' (i:Flavor F) : Lat.Row c ↪ Modes c F:=⟨fun x=>(x,i),fun _ _ h=>congr_arg Prod.fst h⟩; let E': Lat.Row c ↪ Kq:= (H' b).trans Embedding.inr; let D' : Lat.Row c ↪ Kq:=(H' a).trans Embedding.inl
   exact le_trans (sum_le_sum (s:=(univ:Finset (Lat.Row c))) fun i _=> subset_ship (vary (X:=Pairs (Modes c F)) (E' i) D) D' 2) (subset_ship D E' 3)
local notation "V"=> Fintype.card (Site c)
variable (W:ℝ)(hV: ‖Stew.panel 4 D‖≤ (Fintype.card (Site c):ℝ)*W)
include hV
lemma penny : ‖(H)⁻¹ * murphy a b i j (passenger P 1)‖ ≤ (Fintype.card (Site c):ℝ)*(rootM t K C0 C2 C4+C0*24*W):=by
     apply (caption i j a b D T ht he Z K C0 C2 C4 hD hZ hk hv h₂ h₄ hM hW t P h).trans
     have he : bins Kq D 4 ≤ 24*((V:ℝ)*W):=by
          have hp:=prices D 4; rw [rem_price,show (((4:ℕ).factorial):ℝ)=24 by norm_num [Nat.factorial]
          ] at hp; exact hp.trans (mul_le_mul_of_nonneg_left hV (by norm_num))
     apply (add_le_add le_rfl (mul_le_mul_of_nonneg_left he hv)).trans_eq; unfold rootM rowsW; rw [Fintype.card_prod]; push_cast; ring
noncomputable def cupSize (X:Spike)(t:ℕ)(K C0 C2 C4 W:ℝ):ℝ:= (Fintype.card Lat.Fiber:ℝ)*spinPrice X*(rootM t K C0 C2 C4 + C0*24*W)
set_option maxHeartbeats 450000 in
lemma cupTop : ‖horn X a b (Z * BO (exp D)) (passenger P 1)‖≤ cupSize X t K C0 C2 C4 W:=by
      let d:=Fintype.card Lat.Fiber; let D₀:= Fintype.card (Site c)
      let A:=rootM t K C0 C2 C4+C0*24*W; have hz :0 < (D₀:ℝ):=by unfold D₀; positivity
      have hv :0 < (d:ℝ):=by unfold d; positivity
      let m(i j:Lat.Fiber):= (H)⁻¹ * murphy a b i j (passenger P 1); have hc : horn X a b H (passenger P 1) = -(∑ i:Lat.Fiber,∑ j:Lat.Fiber, Lat.wave X j i*m i j) / ((D₀:ℂ)*(d:ℂ)):=by unfold horn; rw [spinC]; congr 1; rw [div_eq_mul_inv,neg_mul,sum_mul]; apply congr_arg (-·); apply sum_congr rfl; intro i _; rw [sum_mul]; apply sum_congr rfl; intro j _; unfold m; rw [mul_assoc, mul_comm ((H):ℂ)⁻¹]; rfl
      rw [hc, norm_div,norm_neg,norm_mul,Complex.norm_natCast,Complex.norm_natCast,div_le_iff₀ (mul_pos hz hv)]; refine (norm_sum_le ..).trans ((sum_le_sum fun i _=> (norm_sum_le ..).trans (sum_le_sum («g»:=fun _=>spinPrice X*(D₀*A)) fun j _=>?_)).trans (le_of_eq ?_))
      · rw [norm_mul]; exact mul_le_mul (PCAC.Brave.hC ..) (penny i j a b D T ht he Z K C0 C2 C4 hD hZ hk ‹0≤C0› h₂ h₄ hM hW t P h W hV) (norm_nonneg _) (spinPrice_nn _)
      simp only [sum_const,card_univ,nsmul_eq_mul]; unfold d cupSize A; ring
end YM.Massive.PCAC.Brave.CoatB
#print axioms YM.Massive.PCAC.Brave.CoatB.cupTop
