import YM.Needle.Slots
import YM.Bwana.Mono
import YM.Intag.Cavity
-- sup norm shell dimensions.B
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Hub
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory Cells QCD.RP
open Massive.Romance Poised Plans Display Poised.Plans Stamp
open Massive.Patria.Depth Intag Next.Rank.Station Needle Laurent
namespace Duon
lemma sizeB (x:Cover)(a:ℝ)(ha:0<a): a*(Laurent.size x:ℝ) ≤ 4*‖digit a x‖:=by
     let f:=digit a x; have hp(i:Axis):‖f i‖=a*((x i).natAbs:ℝ):=by change ‖a*(x i:ℝ)‖=_; rw [norm_mul,Real.norm_of_nonneg ha.le]; simp
     have h(i:Axis):‖f i‖≤‖f‖:= PiLp.norm_apply_le ..
     unfold Laurent.size; push_cast; rw [mul_sum]; exact (sum_le_sum (fun i (_:i∈ Finset.univ)=> ((hp i).symm.le.trans (h i)))).trans_eq (by simp [Axis,f])
variable {S:Scheme}{N J q m ℓ:ℕ}
lemma parent_base (R:Side)(h:J ≤ N): (viewW S R h).parent 0=0:=by
       let g:=viewW S R h; apply owner g 0 0 (?_); rw [show g.embed 0=0 from g.root.map_zero,separation_self,mul_zero]; exact g.count.property
variable (M0:ℕ)
local notation "a" i:arg=> S.spacing i
local notation "Qᴮ"=> ratioTo S N q
local notation "αP"=> (a q * M0)
local notation "DΩ"=> Needle.digit (S.spacing N)
set_option quotPrecheck false
lemma inFrame{x:Cover}(hq:q ≤ N)(hh:‖digit (S.spacing N) x‖ ≤3*αP): Laurent.size x ≤ Qᴮ*(12*M0):=by
       rw [←footprint S q N hq] at hh
       have h := (sizeB x (a N) (space0 _ _)).trans ((mul_le_mul_of_nonneg_left hh (show 0 ≤ (4:ℝ) by norm_num)).trans_eq (show 4*(3*(S.spacing N*(Qᴮ:ℝ)*(M0:ℝ)))=a N * (Qᴮ*(12*M0):ℕ) from by push_cast; ring)); exact Nat.cast_le (α:=ℝ)|>.mp (le_of_mul_le_mul_left h (space0 _ _))
variable (R:Side) (x:Cover)
local notation "Qϱ"=>wrap (S.side R N)
local notation "fp"=>viewW S R
lemma ΔV (b r:ℕ)(h:q ≤ N)(hy:J ≤ q)(hk: 25*M0+1 ≤ ratioTo S q J)(hw:4*(b+1) ≤ M0)(hu: 1+12*M0 ≤ r)(hv:‖digit (a N) x‖≤3*αP) (ht: αP/4 ≤ a N * separation (wrap (S.side R N) x) 0): (∀ i≤J, Off.faceC S N x i=0) ∧ b ≤ separation (wrap (S.side R q) (Off.faceC S N x q)) 0 ∧ separation (wrap (S.side R q) (Off.faceC S N x q)) 0 ≤ r:=by
       have hk' := inFrame M0 h hv; refine ⟨fun i hi=> Off.lead_face x hi (hy.trans h) ?_,?_,?_⟩
       · rw [Off.ruler hy h]; let wa:= ratioTo S q J; have hz:(2*(12*M0))<wa:=(by unfold wa; omega); exact (le_trans (Nat.mul_le_mul_left 2 hk') (le_of_eq (show _= Qᴮ*(2*(12*M0)) from by ring))).trans_lt (Nat.mul_lt_mul_of_pos_left hz (odd_to (S:=S) h).pos)
       · rw [Off.face_seat x h,← parent_base (S:=S) R h]; apply Intag.Film.apert_ineq (fp h) (odd_to h); rw [←footprint S q N h] at ht; refine Nat.cast_le (α:=ℝ)|>.mp (le_of_mul_le_mul_left ((le_trans ?_ ht)) (space0 S N)); push_cast; have hx:4*((b:ℝ)+1)≤M0:=(by exact_mod_cast hw); have he : (a N)*(Qᴮ:ℝ)>0:=mul_pos (space0 S N) (Nat.cast_pos.mpr (odd_to h).pos)
         change a N * ((Qᴮ:ℝ)*_)≤_; linarith only [mul_le_mul_of_nonneg_left hx he.le]
       rw [Off.face_seat x h,← parent_base (S:=S) R h]; have hh:= Film.chin (fp h) (odd_to (S:=S) h) ((Qϱ) x) 0; have hP:separation ((Qϱ) x) 0 ≤ Laurent.size x:= by rw [separation_comm]; exact Planned.PrimaryIntegral295.Cabins.spans ..
       refine Nat.le_of_mul_le_mul_left ((le_trans hh (?_))) (odd_to (S:=S) h).pos; change Qᴮ+_≤ Qᴮ*r; apply le_trans _ (Nat.mul_le_mul_left _ hu); rw[mul_add,mul_one]; exact Nat.add_le_add_left (hP.trans hk') _
variable {C:Sequence}{f:ℕ→ℕ}{β e:ℝ} (H:C.Path β e)
local notation "a₀" i:arg=> C.S.spacing (C.N i)
local notation "ΔS"=> C.S.spacing
local notation "ι" i:arg=> C.S.side (C.R i)
include H
variable (w: ℕ→ Cover)
-- for all sequences approaching a fixed point in annulus.Constit.
set_option maxHeartbeats 400000 in
lemma annals (b r:ℕ)(hJ:J ≤ q)(hk:25*M0+1 ≤ratioTo C.S q J)(hw:4*(b+1) ≤M0)(hu:1+12*M0 ≤ r) (y:E4) (hv:Tendsto (fun i=>digit (C.S.spacing (C.N i)) (w i)) atTop (𝓝 y))(hy: C.S.spacing q*M0 ≤ ‖y‖)(h': ‖y‖≤ 2*(C.S.spacing q*M0)) : ∀ᶠ i in atTop, (∀ j≤J, Off.faceC C.S (C.N i) (w i) j=0)∧ b≤ separation (wrap (C.S.side (C.R i) q) (Off.faceC C.S (C.N i) (w i) q)) 0 ∧ separation (wrap (C.S.side (C.R i) q) (Off.faceC C.S (C.N i) (w i) q)) 0≤r:=by
       let A:= C.S.spacing q*M0; let P:= fun i=> digit (a₀ i) (w i); have hp:0<A:=mul_pos (space0 ..) (Nat.cast_pos.mpr (show 0<M0 from by omega)); have ht:Tendsto (fun i=>‖P i‖) atTop (𝓝 ‖y‖):=hv.norm
       change A ≤ _ at hy; change _ ≤ 2*A at h'
       filter_upwards [ht.eventually_le_const (show ‖y‖ < 3*A from by linarith),ht.eventually_const_le (show A/2 < ‖y‖ from by linarith),H.uv.tendsto_atTop.eventually_ge_atTop q,Needle.fullPrice H (A/2) (3*A)] with i hv₁ hv₂ Hi Hφ
       apply ΔV M0 (C.R i) (w i) b r Hi hJ hk hw hu hv₁
       have hv:dist (P i) (digit (a₀ i) 0)=‖P i‖:=by rw [digit_zero,dist_zero_right]
       have hh :A/2/2≤ C.S.spacing (C.N i) *separation (wrap (C.S.side (C.R i) (C.N i)) (w i)) (wrap _ 0):=Hφ (w i) 0 (hv.symm ▸ hv₂) (hv.symm ▸ hv₁); rw[map_zero] at hh; convert hh using 1; unfold A; ring
end Duon
end YM.Massive.Patria.Hub
#print axioms YM.Massive.Patria.Hub.Duon.annals
