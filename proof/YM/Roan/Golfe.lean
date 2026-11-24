import YM.Roan.Realm
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
include hV hp hL
variable (f z:Flavor 6→ℂ)(hf:‖(f,z)‖ ≤ g*(Pt n).threshold) (X:ℕ→Z)
local notation "pT" t':arg=> point (Pt t').threshold (cashR (L^5) S0 n t') (A t')
local notation "PL"=> pT 0
local notation "Ez" i:arg=> X i -p i -doubleW (fun j=> Qv j i) (fun j=>S j i) (f,z) -- etc
include hf
lemma elevated (i:Flavor 6)(ht:∀ i,GlowZ (L^4) M C D e Pt A n A0 (Qv i))(hZ:∀ i,GlowZ (L^4) M C D e Pt A n A0 (S i))(hq:‖prismB (p n)-Pi.single i 1‖≤2*e)(hx:X n=p n+doubleW (fun i=> Qv i n) (fun i=>S i n) (f,z))(hδ:‖(PL) (X 0)-(pT n) (X n)‖ ≤ 2*t₀*(D0)+De): ‖(PL) (X 0)- Pi.single i 1‖ ≤2*t₀*(D0)+De+3*e + 2*(6*(2*D0)*g):=by
      have he:=hp.cal; have ht':0< L:= lt_of_lt_of_le (by norm_num) hL; have hv:= (Pt n).threshold_pos; let t:= (Pt n).threshold; let s:=A n; have hw:0<s:=hV _
      have h5:= (cash_κ (L^5) S0 (by positivity) (by positivity [pow_pos (hV n) 2]) n).2.2; have h4:= (cash_κ (L^4) A0 (by positivity) (by positivity [hV n]) n).2.2
      let F:=prismB; let W:= 2*(D0); have hW:0≤ W:=by unfold W; have h₀:=hp.north.m_ng; have hC:=hp.sig.pos; have hD:=hp.sig.ng; positivity
      have hy(x:ℕ→Z)(hx:GlowZ (L^4) M C D e Pt A n A0 x):‖F (x n)‖ ≤ W/t:=by
           have h:= hx.yields n le_rfl; rw [h4,T_compare (A n) t (hV _) hv,norm_smul,Complex.norm_real,Real.norm_of_nonneg hv.le] at h; rw [le_div_iff₀ hv,mul_comm]; exact h
      have hm (p:Flavor 6→ℕ→Z)(x:Flavor 6→ℂ)(hx:‖x‖≤g*t)(hp:∀ i, GlowZ (L^4) M C D e Pt A n A0 (p i)): ‖F (knotW (fun i=> p i n) x)‖≤6*W*g:=by unfold knotW; rw [map_sum]; simp_rw [map_smul]; apply (knots _ (W/t) (fun i=>hy _ (hp i)) x).trans; refine (mul_le_mul_of_nonneg_left hx (mul_nonneg (by norm_num) (div_nonneg hW hv.le))).trans_eq (by have h:0 < t:=hv; field_simp; unfold t; ring)
      let p':= fun i=> Qv i n; let q':=fun i=>S i n; let Y:= doubleW p' q' (f,z)
      have hK:‖F Y‖≤2*(6*(2*D0)*g):=by
            change ‖F (knotW _ _+knotW _ _)‖ ≤ _; rw [map_add,two_mul]; apply (norm_add_le ..).trans; exact add_le_add (hm _ _ ((le_max_left ..).trans hf) ht) (hm _ _ ((le_max_right ..).trans hf) hZ)
      let V:= PL; have hz : ‖F (X n)-Pi.single i 1‖≤ 3*e+2*(6*(2*D0)*g):=by
            rw [hx, map_add, show (F (p n)+ F _)-Pi.single i 1=F (p n)-Pi.single i 1 + F Y from (by change F (p n)+F Y-_ = _; abel)]; exact (norm_add_le ..).trans (add_le_add (hq.trans (by linarith only [he])) hK)
      rw [h5,(oR_t (A n) _ (hV _) hv _).2.2.1] at hδ; exact (norm_sub_le_norm_sub_add_norm_sub (V (X 0)) (F (X n)) _).trans ((add_le_add hδ hz).trans_eq (by ring))
omit hf
-- Rank conditional. Use `Kδ<=...`: ker approx for Sc columns; lifted at root supremum.Raw.Actual. keep eΛ small on both points determined.Bound. Define Ξ projections Sc.S.
local notation "Rω"=>Flavor 6
variable {W:Type}[AddCommGroup W][Module ℂ W]
variable (Pole: Z→ₗ[ℂ] W)
variable (p0 q0 su0 sz:Rω→Z) (fl:Rω→FQ)
local notation "κb"=> compass 1 (A 0)
local notation "κM"=> point ((Pt 0).threshold) 1 (A 0)
local notation "Ku"=> cashR (L^5) S0 n 0
local notation "Kl"=> cashR (L^4) A0 n 0
local notation "Hf" pz:arg=> (Pt 0).threshold
-- near null synopsis.Bills.E projection errors. inputs scaled. NO existential trick.
lemma timeR(X:Z): (κb) ((Kl:ℂ) • X)=(uδ) X ∧ (κM) ((Kl:ℂ) • X)= (point (Pt 0).threshold Kl (A 0)) X∧ (κb) ((Ku:ℂ) • X)= compass Ku (A 0) X∧ (κM) ((Ku:ℂ) • X)= (PL) X:=by
     simp only[map_smul]; unfold compass point signature; simp only [LinearMap.smul_apply]; simp_rw [smul_smul]; simp only[one_mul]; push_cast; constructor; · rfl
     refine ⟨?_,rfl,?_⟩ <;> congr 1 <;> ring
lemma paidV (p z:Z)(A':ℝ)(h:‖p-z‖≤ A')(hx:D*(A 0)^2*A' ≤ eΛ): ‖(κb) z-(κb) p‖ ≤eΛ ∧ ‖(κM) z-(κM) p‖≤eΛ:= by
       let C':=(A 0)^2; have hC:0<C':= sq_pos_of_pos (hV _); have hW:0≤ D:= zero_le_one.trans hp.sig.ng; let v:=z-p; have hz: D*‖v‖≤ D*A':= mul_le_mul_of_nonneg_left ((norm_sub_rev z p).le.trans h) hW; have hv: C'*(D*‖v‖) ≤eΛ:= (mul_le_mul_of_nonneg_left hz hC.le).trans (le_trans (show C'*(D*A')=D*C'*A' from by ring).le hx)
       rw [←map_sub,←map_sub]; unfold compass point signature; simp only [LinearMap.smul_apply, norm_smul,Complex.norm_real, one_mul]; rw[Real.norm_of_nonneg hC.le,Real.norm_of_nonneg (mul_nonneg (Pt 0).threshold_pos.le hC.le)]; refine ⟨(mul_le_mul_of_nonneg_left (hp.sig.read1 _) hC.le).trans hv,(mul_le_mul ?_ (hp.sig.read2 v) (norm_nonneg _) hC.le).trans hv⟩
       exact mul_le_of_le_one_left hC.le (Pt 0).threshold_le
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.elevated
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.paidV
