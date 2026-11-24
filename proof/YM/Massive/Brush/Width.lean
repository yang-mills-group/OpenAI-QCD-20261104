import YM.Massive.Brush.Apex
import YM.Massive.PCAC.Gift
/-! One-step immediate-birth window, accounting in units of `LocalPrice`. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open YM.Next.Free
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical ComplexOrder
variable {A B:Type*} [Fintype A][Fintype B]
variable {c f:Side}{n N j k F:ℕ}
variable (P:Flight j k)(K:KernelChoices)(h:f.val=c.val*P.L.val) (β w:ℝ)(hk:P.patch.Branches K su)
namespace Brave
open Finset NormedSpace Loft QCD.Globe QCD.Globe.HalfMass
open MeasureTheory
open scoped Kronecker
variable (a b:Flavor F) (X:Spike)
local notation "d"=> (Fintype.card Lat.Fiber:ℝ)
local notation "Z"=> (Fintype.card (Site c):ℝ)
local notation "g₅"=> Lat.g5
local notation "p"=> Run.plane
local notation "Y"=> flavorW g5 a b c
local notation "cell"=> QCD.Run.cell
-- Structured proximity estimates at AP wave. Inverse spacing parameter must track in actual theorem; no Fourier log error lost.
abbrev beamSize (A:ℝ):ℝ:= (Massive.Reading.budget+20)*A
lemma budget_nn : 0≤ Massive.Reading.budget:=by unfold Reading.budget; positivity
lemma halo {A:Sheet c}{w:ℝ}(hw:Beam A 6 w)(hA:Tempo A) (i:Site c): amount c * ‖stalk A i-(Globe.mass A:ℂ) • 1‖ ≤ beamSize w:= HalfMass.near A i pCoin (show 1 ≤ 6 by omega) budget_nn Massive.Reading.closeRe hw hA
lemma haloM {A:Sheet c}{w:ℝ}(hx:Beam A 6 w)(hV:Tempo A): amount c*‖artPrice 1 A-(Globe.mass A:ℂ)‖ ≤ beamSize w:=by
    have hp(i:Lat.Fiber) :=HalfMass.coat A pCoin (m:=6) (A:=w) (u:=i) (by norm_num) budget_nn Massive.Reading.closeRe hx hV -- ordering?
    let v:= (Fintype.card Lat.Fiber:ℂ); let h':= HalfMass.center A pCoin; let w':=(Globe.mass A:ℂ); have he : 0<d:=by positivity
    have hh: artPrice 1 A=v⁻¹ * ∑ i:Lat.Fiber,h' i i :=by
         let f(x y:Site c)(u:Lat.Fiber):=(pCoin x y)*cell A x y u u
         have hx(i j:Site c): star (p i)*spinTest 1 i j A*p j= ∑ u:Lat.Fiber,f i j u:=by unfold spinTest; rw [wave_one,mul_one]; unfold f Matrix.trace; rw [mul_sum,sum_mul]; apply sum_congr rfl; intro u _; change _*cell A i j u u*_= _; unfold pCoin; ring
         unfold artPrice; simp_rw [hx]; have hp₁ : ∑ x:Site c,∑ y:Site c,∑ u:Lat.Fiber,f x y u= ∑ u,∑ x,∑ y,f x y u:=by rw [sum_comm (f:=fun u x=>∑ y,f x y u)]; apply sum_congr rfl; intro _ _; rw [sum_comm]
         rw [hp₁]; unfold v h' HalfMass.center HalfMass.cashRow; simp only [Matrix.smul_apply,Matrix.sum_apply, smul_eq_mul]; rw [← mul_sum]; unfold f; ring

    rw [hh, show v⁻¹ * ∑ i:Lat.Fiber,h' i i - w'= v⁻¹ * ∑ i:Lat.Fiber,(h' i i-w') from ?_,norm_mul,norm_inv, show ‖v‖=d from Complex.norm_natCast _,mul_left_comm,inv_mul_eq_div]; swap
    · rw [sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,mul_sub]; rw [inv_mul_cancel_left₀ (show v≠0 by unfold v; positivity)] --
    apply (div_le_iff₀ he).mpr; apply le_trans (mul_le_mul_of_nonneg_left (norm_sum_le ..) (show 0≤amount c from Nat.cast_nonneg _)); rw [Finset.mul_sum]; exact (sum_le_sum fun i _=> hp i).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul]; exact mul_comm ..)
lemma stalk_cost {A:Sheet c}{w:ℝ}(hp: Beam A 6 w)(he:Tempo A)(i:Site c): amount c * (‖stalk A i‖- ‖artPrice 1 A‖) ≤ 2*beamSize w:=by
    have h:= halo hp he i; have hx:=haloM hp he; let b:ℂ:=Globe.mass A
    have hc:(0:ℝ)≤amount c:=Nat.cast_nonneg _; have hs:‖(b • (1:Bundle))‖=‖b‖:=by rw [norm_smul,norm_one,mul_one]
    have hv:= norm_sub_rev (artPrice 1 A) b
    nlinarith only [h,hx,mul_le_mul_of_nonneg_left (norm_sub_norm_le (stalk A i) (b • (1:Bundle))) hc, mul_le_mul_of_nonneg_left (norm_sub_norm_le b (artPrice 1 A)) hc,congr_arg (amount c*·) hs,congr_arg (amount c*·) hv]

variable {R:Side}{S: Scheme}(T:Run S N R F)
lemma principal_stat (P:Density c F)(U:Fields c F): artPrice X ((Stiffness.body P 1)⁻¹ • piece a b (traceP U))= horn X a b (Stiffness.body P 1) U:=by rw [art_horn,art_mul]
-- cast C notation not through.Profile read.L
lemma width (m:ℕ)(w r v A:ℝ)(hv: LocalPrice (T.density m) w r)(he:a≠b)(ht:∀ i, ‖T.massRead m i‖≤v)(hx: 2*beamSize r ≤ amount (S.side R m)*(A-v)) : let U:=T.density m 1; let f:=S.side R m; let V:=flavorW X a b f; ‖horn X a b (coef ∅ U) (Ward.lap V U)‖ ≤ productTariff X*A^2+quartic X*w:=by
    intro U c T₁; obtain ⟨W,z,t,hW,hz,hZ,hQ,H,hp,hP⟩:= hv.source
    rw [show U= _ from hW]; apply beamAt a b X W t w A z hz he hZ hQ (hP a).1 _ hp
    have hh(i:Flavor F)(j:Site c): ‖stalk (t i) j‖ ≤ A:=by
         have he := stalk_cost (hP i).2 (hP i).1 j; have hw : artPrice 1 (t i)= T.massRead m i:=by rw [H i, art_mul]; rw [show (T.massRead m i)=_ from Eq.symm (point_cost (T.density m) i),art_horn] -- finish
         rw [hw] at he; apply le_of_mul_le_mul_left _ (show 0 < amount c from Nat.cast_pos.mpr c.property)
         nlinarith only [hx,he,mul_le_mul_of_nonneg_left (ht i) (show 0≤amount c from Nat.cast_nonneg _)]
    exact fun i j=> ⟨hh a i,hh b j⟩
lemma chord_scale {u:ℂ}{m:ℕ}(Z':Insertion (S.side R m) F) : chord X a b T m (u • Z')= u • chord X a b T m Z':=by unfold chord; rw [ContinuousMap.smul_apply]; rw [art_horn,art_horn,Loft.basic,pack_scale,art_mul, smul_comm]
lemma quiltZero : Quilt P K h β w hk (0:Deck f F)=0:=by
    have hh(a b:Modes f F)(i j:Modes c F): berth P h a b i j (0:Insertion f F)=0:=ContinuousMap.ext fun U=> smul_zero ..
    ext i j; change Transfer.blockMap _ _ _ _ _ _ _ _ = 0 -- ext goes U?
    simp [hh]
-- Charge immediate step. Includes ordered layout at any m.
lemma one_step (m:ℕ)(hi:m<N)(w r v A:ℝ)(hx:a≠b)(he:T.Actual)(hZ:LocalPrice (T.density m) w r)(hM:∀ i, ‖T.massRead m i‖≤v)(hV:2*beamSize r≤ amount (S.side R m)*(A-v))(hT:1/2≤ T.w m):
      ‖chord g₅ a b T m (S.toStop R T.β T.w (m+1) m (axialSum a b g₅ T (m+1))) - (T.massRead m a+T.massRead m b)‖ ≤ 8* (productTariff g₅ *A^2+quartic g₅*w) :=by
    obtain ⟨M,hH,hU,hR⟩:=(PCAC.charge a b g₅ g₅ T he hx g5_sq g5_sq (m+1) hi m (by omega)).2; have hq:= hU m (by omega); let t:= T.w m; let s:ℂ:= (t:ℂ)⁻¹^2; let F0:= actor T m; let E:= flavorW g₅ a b (S.side R m)
    rw [show passenger (M m)= s • stroll (lap E) F0 from ?_] at hR; swap
    · rw [hq,hH]; unfold liftM toward; rw [quiltZero,add_zero,pax_scale,bore_at]
    rw [hR,chord_scale]; simp only [smul_eq_mul]; rw [show _-(T.massRead m a+T.massRead m b)= -(2*(s*chord g₅ a b T m (stroll (lap E) F0))) from by abel, norm_neg,norm_mul,norm_mul]; have hh: ‖chord g₅ a b T m (stroll (lap E) F0)‖ ≤ productTariff g₅*A^2+quartic g₅*w:=by unfold chord; rw [stroll_at,show F0 1=_ from congr_fun (act T he hi.le) 1]; exact width a b g₅ T m w r v A hZ hx hM hV
    have hs: ‖s‖ ≤4:=by
         unfold s; rw [norm_pow,norm_inv,Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ t from (he.w_pos hi).le)]; have hx: t⁻¹ ≤2 := by rw [← one_div]; apply (div_le_iff₀ (he.w_pos hi)).mpr; linarith only [show 1/2≤t from hT]
         nlinarith only [hx,inv_nonneg.mpr (show 0≤t from (he.w_pos hi).le)]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul hs hh (norm_nonneg _) (by norm_num)) (norm_nonneg _)).trans_eq (by norm_num; ring)
end Brave
end YM.Massive.PCAC

#print axioms YM.Massive.PCAC.Brave.one_step
