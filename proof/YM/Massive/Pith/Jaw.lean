import YM.Massive.Pith.Rent
import YM.QCD.Finch.Offer
/-! # Calibrating actual finite plane data with normalized mark invariant, price sign. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Finch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove Entr YM.Next.Free Bloch Laurent QCD.Free
variable {t s τ u :ℝ}{j k:ℕ}{B:BudgetPoint}
variable (o:Site c)(a: Flavor N)(X:Crate c N)

def tierS (a:Flavor N)(X:Crate c N):Sheet c:= Matrix.of fun i j=> grasp X (i,a) (j,a)
lemma stamped (W: Site c×Site c→ℂ)(R:ℝ) (h:0≤t)(hr:0≤R)(hp:∀ i:Site c×Site c, ‖W i‖≤R*pieD (Stew.lens o) (tag (Hx a i.1) (Hx a i.2))):
   t^2*‖(∑ i:Site c×Site c,W i*tierS a X (i.1,chad) (i.2,chad))‖ ≤ R*Stew.plank o t X:=by
    let I:=Site c×Site c; let G v:= coef v X ; let H v:= starch (Stew.lens (N:=N) o) t v * ‖G v‖; have he(v):0≤ H v:=mul_nonneg (starch_pos _ h _) (norm_nonneg _); let P(i:I):=tag (Hx a i.1) (Hx a i.2); have hx (i:I):(P i).card=2:=by simp [P,Stew.tag]
    have hQ (u v:I)(hs:P u=P v): u=v:=by
       obtain ⟨h1,h2⟩:= (tagged ..).1 hs; let k (i:Modes c N):=i.1.1; exact Prod.ext (congr_arg k h1) (congr_arg k h2)
    have hg (i:I): ‖tierS a X (i.1,chad) (i.2,chad)‖= ‖G (P i)‖:=by
       change ‖bit (Hx a i.1) (Hx a i.2)*G (P i)‖=_; obtain h|h:= bitS (Hx a i.1) (Hx a i.2)<;> rw [h] <;> simp
    let f(i:I):=tierS a X (i.1,chad) (i.2,chad)
    apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (by positivity : 0≤ t^2)).trans; rw [mul_sum]; simp_rw [norm_mul]; refine (sum_le_sum (g:=fun j=>R*H (P j)) (fun i _=> ?_)).trans ?_
    · unfold H starch; rw [hg i, hx]; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hp i) (norm_nonneg _)) (sq_nonneg t)).trans_eq (by dsimp only [P]; ring)
    rw [← mul_sum]; refine mul_le_mul_of_nonneg_left ?_ hr; rw [← sum_image (f:=H) (g:=P) (show Injective P from fun _ _=> hQ _ _).injOn]; rw [Stew.plank,pricesD _ h]; exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _=> he _

noncomputable def stowL (c:Side): Sheet c→L[ℂ]ℂ:= LinearMap.toContinuousLinearMap { toFun:=stow, map_add':=fun x y=>by unfold stow; simp [Matrix.add_apply,Finset.sum_add_distrib,mul_add], map_smul':=fun z x=>by unfold stow; rw [Finset.smul_sum]; exact sum_congr rfl (fun i _=>by simp [Matrix.smul_apply]; ring) }
noncomputable def tierL (a:Flavor N):Crate c N→L[ℂ] Sheet c:= LinearMap.toContinuousLinearMap { toFun:=tierS a, map_add':=fun x y=>by unfold tierS; rw [grub]; rfl,map_smul':=fun z x=>by unfold tierS; rw [regalia]; rfl }
noncomputable def planeW (c:Side)(t:ℝ)(a:Flavor N): Crate c N→L[ℝ]ℝ:= t^2 • Complex.reCLM.comp (((stowL c).comp (tierL a)).restrictScalars ℝ)
lemma allegiance (ht: 0 ≤ t): QCD.Spice.rootBill o t (planeW c t a):=by
    intro X; change ‖t^2 • (stow (tierS a X)).re‖ ≤ _; rw [norm_smul,Real.norm_of_nonneg (sq_nonneg t)]; exact (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (sq_nonneg t)).trans ((stamped o a _ (fun i=>corep i.1 i.2) 1 ht zero_le_one (fun i=>by rw [shiftU,one_mul]; exact_mod_cast (ridesP o a i.1 i.2).1)).trans_eq (one_mul _))
noncomputable def watchW (c:Side)(t:ℝ)(a:Flavor N): EvenA c N →L[ℝ]ℝ:= QCD.Spice.lensQ 0 N (planeW c t a)
lemma morn (t v:ℝ)(X: EvenA c N): watchW c t a (wearK c N v X)= v^2*watchW c t a X:=by
   have h: feeF a (wearK c N v X)= v^2 • feeF a X:=by
      ext i j; let I:= tag (i,a) (j,a); have hp:I.card=2:=by simp [I,tag]
      let G:ℂ:=bit (i,a) (j,a)
      change G*coef I (engine v (Keys c N) X.val)=(v^2:ℝ) • (G*coef I X.val); rw [fundW, hp,Complex.real_smul]; push_cast; ring -- defeq coer unit
   change t^2*(stowL c (feeF a _)).re = v^2*(t^2*(stowL c (feeF a _)).re); rw [h, show stowL c (v^2 • feeF a X)= v^2 • stowL c (feeF a X) from map_smul ((stowL c).restrictScalars ℝ) .., Complex.real_smul]; rw [Complex.mul_re, Complex.ofReal_re,Complex.ofReal_im]; ring
lemma far (x:Sheet c): (stow x).re=(Fintype.card (Site c):ℝ)*flagW x:=by rw [pStow]; simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im, zero_mul,sub_zero,flagW]
lemma worldQ (X:EvenA c N) : watchW c t a X= t^2*((Fintype.card (Site c):ℝ)*flagW (feeF a X)):=by change t^2*(stow _).re=_; rw [far]; rfl
-- infinite group. aggregate price bound by t^2*density signal
abbrev flagRead (a: Flavor N)(t:ℝ)(X:EvenA c N):ℝ:= watchW c t a X/(Fintype.card (Site c):ℝ)
lemma flagP (x:EvenA c N) : flagRead a t x=t^2*flagW (feeF a x):= by unfold flagRead; rw [worldQ]; field_simp
variable (E:Gem c N I)
variable {f0:I→ℝ} {x':ℝ}
variable (h:Shells.Warmlet.Valued E.addr u f0 B.B x')(ht:0≤u)(hw:∀ i, Woven (E.addr i).site (E.addr i).support B t (E.view i) (f0 i))(hz:0<t)
open AnalyticBridge.VerifiedReset
include h hw ht hz
lemma sector_pay : ‖flagRead a t (Patron.total E B.threshold 1)‖ ≤ x':=by
    let H:=watchW c t a; have hC := Stew.permits E (show Licence B u x' t E from ⟨f0,h,hw⟩) hz ht (1:Grid c) -- arguments inspect
    let N':ℝ:=Fintype.card (Site c); let z i:= H (letters E B.threshold 1 i); have hm: Summable z:= (H.hasSum hC.hasSum).summable
    have hp i:z i= H (E.view i 1):= congr_arg H (masked_eq _ _ _ _ (AnalyticBridge.VerifiedReset.flat_ok ..)); have he(i): ‖z i‖ ≤ f0 i:= by rw [hp i]; exact (allegiance (E.addr i).site a hz.le _).trans ((hw i).sizeU 1 (flat_ok ..))
    have hT:= Stem.mast E f0 h (fun i=> (hw i).travel) ht; unfold flagRead; rw [norm_div, show (watchW c t a) (Patron.total E B.threshold 1)=∑' i, z i from (H.hasSum hC.hasSum).tsum_eq.symm]; change ‖∑' i, z i‖ / ‖N'‖ ≤ _; rw [Real.norm_of_nonneg (show 0 ≤N' from Nat.cast_nonneg _)]; apply (div_le_iff₀ (by unfold N'; positivity)).mpr; rw [mul_comm]; let hB:= budget_mono hT (fun i=>norm_nonneg (z i)) he; exact (norm_tsum_le_tsum_norm hB.2.1).trans hB.2.2
lemma totalFare (hU:0<u)(hp: CrossP E): t^2* ((c.val:ℝ)* |flagW (feeF a (Patron.total E B.threshold 1)) - Pith.gaugeMass E a|)≤ fare u B.B*x':=by
    let m:= Pith.gaugeMass E a; let X:=Patron.total E B.threshold 1; let v:= Stew.meter (c:=c) a; let A:=Complex.reCLM.comp ((stowL c).restrictScalars ℝ); let K:=Fintype.card (Site c)
    let φ x (b:EvenA c N):ℝ:=A (v b) - (coz (shape x (feeF a b) none)).re; let p:=till E a 0
    -- mux projection at each root.
    let D i (x:Site c):= if (E.addr i).site=x then f0 i*Real.exp (u*coverNumber B.B (E.addr i).support) else 0
    have hc := Stew.permits E (show Licence B u x' t E from ⟨f0,h,hw⟩) hz ht (1:Grid c)
    have hh : HasSum (fun i=>A (v (E.view i 1))) (K*flagW (feeF a X)):=by
       rw [← far]; apply (A.hasSum (v.hasSum hc.hasSum)).congr_fun; intro i; exact congr_arg (A ∘ v) (masked_eq B.threshold _ _ _ (flat_ok ..)).symm
    let g (i:I):= Stew.lane E a i none
    have he(x): HasSum (Stew.unitM E a x none) (p none):=by
       have hB:=costsE E a (Loom.sumRide _ _ _ h (fun i=>(hw i).travel) ht) hz (fun i=> (hw i).sizeU 1 (flat_ok ..)); rw [show p=till E a x from Eq.symm (plumsB E a (Licence_g (show Licence B u x' t E from ⟨f0,h,hw⟩)) hp hB x)]; exact (concession E a (hB _) x).hasSum
    let L:Spike→L[ℝ]ℝ:= LinearMap.toContinuousLinearMap { toFun:=fun z=>(coz z).re,map_add':=fun _ _=>rfl,map_smul':=fun x y=> by unfold coz; rw [Matrix.smul_apply,Complex.real_smul];simp }
    have hP (x:Site c): HasSum (fun i=> if (E.addr i).site=x then L (g i) else 0) m:=by
       apply (L.hasSum (he x)).congr_fun; intro i; by_cases h:x=(E.addr i).site
       · exact (if_pos h.symm).trans (congr_arg L (if_pos h).symm)
       rw [if_neg (Ne.symm h), unitM,if_neg h,map_zero]
    have hK : HasSum (fun i=> L (g i)) (K • m):=by
       have ht:= hasSum_sum (s:=univ) (fun i _=> hP i); simp only [sum_const,card_univ] at ht; apply ht.congr_fun; intro i; rw [sum_ite_eq,if_pos (Finset.mem_univ _)] -- check
    have hC:=hh.sub hK; let P:=(c.val:ℝ)*t^2; have hP:0 < P:=by unfold P; positivity
    let z(i:I):=A (v (E.view i 1))-L (g i)
    let d₁: I→ ℝ:=fun i=>∑ x:Site c,D i x; have hD := budget_over (univ: Finset (Site c)) (fun x i=>D i x) (fun _=>x') (fun i _=> h i); rw [sum_const,card_univ] at hD -- last rw may fail
    have hf i: P*‖z i‖ ≤ fare u B.B*d₁ i:=by
       have hh:= Complex.abs_re_le_norm (stow (feeF a (E.view i 1))-coz (g i)); have hp : P* _ ≤ _:= mul_le_mul_of_nonneg_left hh hP.le
       apply hp.trans; unfold d₁ D; rw [sum_ite_eq, if_pos (mem_univ _)]; rw [show P* ‖(stow (feeF a (E.view i 1))-coz (g i))‖=t^2*((c.val:ℝ)*‖(stow (feeF a (E.view i 1))-coz (g i))‖) from (by unfold P; ring)]; exact (rateH E a i hz.le hU (B:=B)).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ((hw i).sizeU 1 (flat_ok ..)) (Real.exp_pos _).le) (by unfold fare; positivity))
    let H:= budget_scale (show 0≤ fare u B.B by unfold fare; positivity) hD; let Y:= budget_mono H (fun i=> mul_nonneg hP.le (norm_nonneg _)) hf
    have hh: (∑' i:I,z i)= ↑K*flagW (feeF a X)-(K:ℝ)*m:=by rw [←nsmul_eq_mul K m]; exact hC.tsum_eq -- notation
    have hB: Summable (fun i=> ‖z i‖):=by apply (Y.2.1.mul_left (P⁻¹)).congr fun i=> ?_; exact inv_mul_cancel_left₀ hP.ne' _
    have he:P*‖(K:ℝ)*(flagW (feeF a X)-m)‖ ≤ (fare u B.B)*(K • x'):=by rw [mul_sub,← hh]; exact (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hB) hP.le).trans (by rw [← hB.tsum_mul_left]; exact Y.2.2)
    rw [norm_mul,Real.norm_natCast,nsmul_eq_mul] at he
    apply le_of_mul_le_mul_left (a:=(K:ℝ)) ?_ (by unfold K; positivity)
    unfold P X m at he; rw [Real.norm_eq_abs] at he; linarith only [he] -- using reals norm abs etc
end YM.QCD.Finch
#print axioms YM.QCD.Finch.sector_pay
#print axioms YM.QCD.Finch.totalFare
