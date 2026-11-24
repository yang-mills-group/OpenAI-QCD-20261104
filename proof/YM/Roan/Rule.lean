import YM.Roan.Golfe
import YM.Roan.Croft
import YM.Roan.Wire
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp.Stair
open Filter Function Set Lattice Wilson RG Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Poised Poised.Beacon Poised.Display Poised.Stative Poised.Sieve
open Finset Tawny Tawny.Cast Tawny.Cast.Rays Tawny.Cast.Carnal Tawny.Cast.TableT Tawny.Pane Tawny.BendR
open Oriole Counting Counting.Click PCAC Patria.Gall.Seals Patria.Gall
-- incomes cost norm.S
local notation "Z"=> RawVec 10
set_option quotPrecheck false
variable (u a α ε L Q M B C D θ e x b eΛ g t₀ R:ℝ)
variable (n:ℕ)(Pt:ℕ→BudgetPoint)(A V:ℕ→ℝ)
-- Faith = dependencies; later choose posts. b upper root derivative,money, flux_B0
local notation "D0"=> D*(C*M)
local notation "De"=> D*(C*e)
local notation "eM" p:arg=> 6*p
variable (p t:ℕ→Z)(Qv S:Flavor 6→ℕ→Z) (hp:Pueblo u a α ε L M B C D θ e x b eΛ g t₀ n) -- order need fields explicitly.L.
local notation "A0"=> (A n)^2
local notation "u₀"=> (Pt n).threshold
local notation "S0"=> (Pt n).threshold*(A n)^2
local notation "EA"=> fun i:Flavor 6=> Qv i 0
local notation "EZ"=> fun i:Flavor 6=> S i 0
local notation "rZ"=> Pi.single
local notation "BT" i:arg=> cashR (L^4) A0 n i
local notation "KT" i:arg=> cashR (L^4) S0 n i
variable (hV:∀ i,0 < A i) (hL:3 ≤ L)
local notation "FQ"=>Flavor 6→ℂ
local notation "uδ"=> compass (BT 0) (A 0)
local notation "wδ"=> torque (BT 0) (A 0)
include hp hV hL
variable {W:Type}[AddCommGroup W][Module ℂ W]
variable (F: Z→ₗ[ℂ] W)
variable (p0 p1 q0 r: Flavor 6→Z)(c:Flavor 6→Flavor 6→ℂ)
local notation "uB"=> compass 1 (A 0)
local notation "uQ"=> point ((Pt 0).threshold) 1 (A 0)
local notation "Lu"=> cashR (L^4) A0 n 0
local notation "LB"=> point ((Pt 0).threshold) Lu (A 0)
local notation "Ku"=> cashR (L^5) S0 n 0
local notation "PB"=> point ((Pt 0).threshold) Ku (A 0)
local notation "Pu"=> compass Ku (A 0)
local notation "Pz" i:arg=> p1 i+knotW p0 (c i)
set_option maxHeartbeats 600000 in
lemma progress (S0_:ℝ)(hS:0 ≤ t₀)(hA: ∀ i:Flavor 6,‖(uδ) (p0 i)- Pi.single i 1‖ ≤De +e)(hB:∀ i, ‖(LB) (p0 i)‖≤2*D0)(hR:∀ i, (Pu) (Pz i)=0)(hc:∀ i, ‖c i‖ ≤1)(hz:∀ i, ‖(PB) (Pz i)-Pi.single i 1‖ ≤ 2*t₀*D0+ De+3*e+2*(6*(2*D0)*g))
        (htA:D*(A 0)^2*S0_ ≤eΛ)(ht:∀ i:Flavor 6, ∃ p:Z,p∈ F.ker∧‖(Lu:ℂ) • p0 i-p‖≤ S0_)(hT:∀ i:Flavor 6,∃ p:Z,p∈ F.ker∧‖(Ku:ℂ) • p0 i-p‖≤S0_)(hV1:∀ i:Flavor 6,∃ p:Z,p∈ F.ker∧‖(Ku:ℂ) • p1 i-p‖≤S0_) :
        Surjective (((uB).prod uQ).domRestrict F.ker):=by
       choose X hX hx using ht; choose Y hY hy using hT; choose Z₁ hZ hz' using hV1
       let U:=uB; let V:= uQ; let T (i):= Z₁ i+knotW Y (c i); have h_t(i: Flavor 6):T i∈ F.ker:= Submodule.add_mem _ (hZ i) (Submodule.sum_mem _ fun i _=> F.ker.smul_mem _ (hY i)); let z:ℂ:=Ku; let y:ℂ:= Lu
       have hb(X:Z):= timeR u a α ε L M B C D θ e x b eΛ g t₀ n Pt A hp hV hL X; have hg(p x':Z)(h:‖p-x'‖ ≤ S0_):= paidV u a α ε L M B C D θ e x b eΛ g t₀ n Pt A hp hV hL p x' S0_ h htA
       let r:= eΛ+6*eΛ
       have h'p(A: Z→ₗ[ℂ](Flavor 6→ℂ))(h:∀ i, ‖A (Z₁ i)-A (z • p1 i)‖ ≤ eΛ)(hV:∀ i, ‖A (Y i)-A (z • p0 i)‖ ≤ eΛ)(i:Flavor 6) : ‖A (T i)- A (z • (Pz i))‖ ≤ r:=by
            let Yv(j:Flavor 6):= A (Y j)-A (z • p0 j); have hh: A (knotW Y (c i))-A (z • knotW p0 (c i))= knotW Yv (c i):=by unfold knotW Yv; simp only [map_sum,map_smul, smul_sub,Finset.smul_sum, Finset.sum_sub_distrib]; congr 1; exact Finset.sum_congr rfl fun i _=>smul_comm ..
            unfold T; rw [map_add, smul_add, map_add A (z • _),show _-(_+_)= (A (Z₁ i)-A (z • p1 i))+(A (knotW Y (c i))-A (z • knotW p0 (c i))) from by abel,hh]; apply (norm_add_le ..).trans; apply add_le_add (h _) -- tags
            exact (knots _ eΛ hV _).trans (mul_le_of_le_one_right (mul_nonneg (by norm_num) hp.ca.le) (hc i))
       let s0:=2*t₀*(D*C*M)+D*C*e+3*e+2*(6*(2*(D*C*M))*g)
       have hr:r+s0 ≤x:=by unfold r s0; linarith only [hp.earn]
       have hb':D0=D*C*M:=by ring
       have hD:De=D*C*e:=by ring
       have hΛ:eΛ+ (De+e) ≤ x:=by rw [hD]; linarith only [hp.first]
       have ht0:=hp.north.m_ng; have hC:=hp.sig.pos; have hDz:=hp.sig.ng; have he:=hp.cal; have he':=hp.ca; have hvG :0 ≤g:= le_trans (by positivity [hp.cc]) hp.graft
       have hρ': 0 ≤ x:=by refine le_trans (b:=eΛ+(De+e)) (by positivity) hΛ
       have hX':SplitX X T U V x b:=by
           refine ⟨hρ',hp.cc,hp.safety,hp.yaw,fun i=>?_ ,fun i=>?_ ,fun i=>?_ ,fun i=>?_⟩
           · refine (norm_sub_le_norm_sub_add_norm_sub (U _) (U (y • _)) _).trans ((add_le_add (hg _ _ (hx i)).1 (show ‖U (y • p0 i)- _‖ ≤De+e from ?_)).trans hΛ); rw[(show U (y • _) = _ from (hb _).1)]; exact hA i
           · refine ((norm_le_norm_sub_add (V (X i)) _).trans (add_le_add (hg _ _ (hx i)).2 (show ‖V (y • p0 i)‖ ≤2*D0 from ?_))).trans ?_ ; · rw [show V (y • _)= _ from (hb _).2.1]; exact hB i
             rw [add_comm,hb']; exact hp.fuel
           · refine (norm_sub_le_norm_sub_add_norm_sub (V _) (V _) _).trans ((add_le_add (h'p V (fun i=>(hg _ _ (hz' i)).2) (fun i=>(hg _ _ (hy i)).2) i) (show ‖V (z • (Pz i))- _‖ ≤ s0 from ?_ )).trans hr); rw [show V (z • (Pz i))= _ from (hb (Pz i)).2.2.2]; have h:=hz i; rw [hb',hD] at h; exact h
           have h:=h'p U (fun i=>(hg _ _ (hz' i)).1) (fun i=>(hg _ _ (hy i)).1) i; rw [show U (z • (Pz i))=(Pu) (Pz i) from ?_,hR,sub_zero] at h; swap; · exact (hb _).2.2.1
           exact h.trans ((le_add_of_nonneg_right (show 0 ≤ s0 from (by unfold s0; positivity))).trans hr)
       intro x; obtain ⟨⟨v,u⟩,h⟩:= facesB hX' x; refine ⟨⟨knotW X v +knotW T u,F.ker.add_mem (F.ker.sum_mem fun i h=> F.ker.smul_mem _ (hX i)) (F.ker.sum_mem fun i h=>F.ker.smul_mem _ (h_t i))⟩,h⟩
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.progress
