import YM.Needle.Rack
import YM.Avena.Rest
/-!
   A frame certificate in an averaged stencil. It doesn't rely on parity of the relative shifts.
   Supports of checks shrink with actual rung spacing, not observer horizon or regulator lease.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Set Function Filter Lattice Cells Lyre Lyre.Goblet Romance QCD QCD.Lat QCD.Tide QCD.Grass Plum QCD.RP Patria Patria.Depth Patria.Hub Intag Intag.Vale
open Finset UV Poised Poised.Plans Poised.Plans.Stamp Poised.Stative
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {C:Sequence} (P:Calibration C) {d:ℕ}(Z:Laurel d) (J:Landing P.sym Z)
local notation "S"=> C.S
set_option quotPrecheck false
local notation "Rᴮ" i:arg => (C.A i).regulator
local notation "nᴮ" i:arg => C.S.side (C.R i) (C.N i)
local notation "a" i:arg=> C.S.spacing (C.N i)
variable {β ν:ℝ}(hC:C.Path β ν)
variable {P Z J} (E:Invest P d)
namespace GaugeP
variable (K: GaugeP P Z J)(i j ℓ:ℕ)(hj:j≤ℓ)
noncomputable abbrev goalJ:=bead (C.S.spacing j) K.coast
noncomputable abbrev goalL:=ratioTo C.S ℓ j • K.goalJ j
open CardsT
lemma gears {V:Scheme} {t n:ℕ} (h:t≤n)(x:Cover): digit (V.spacing t) x=digit (V.spacing n) (ratioTo V n t • x):=by
     unfold digit; rw [← footprint V t n h,mul_smul]; refine congr_arg _ (?_); ext i; simp [vector]
include hj in
lemma indented : dist (digit (C.S.spacing ℓ) (K.goalL j ℓ)) K.coast ≤ 2*C.S.spacing j :=by
     unfold goalL; rw [← gears hj]; exact smoothV (space0 _ _) _
local notation "X"=> ratioTo C.S (C.N i) ℓ
local notation "γ"=> flex C.S ℓ (C.N i)
local notation "ψ"=>K.goalL j ℓ
lemma port (he:ℓ ≤ C.N i)(z:Cover)(hz:z ∈ box (flex C.S ℓ (C.N i))) : ‖digit (C.S.spacing (C.N i)) z‖ ≤ 200*C.S.spacing ℓ:=by
    rw[presenting]; have h0:=space0 C.S (C.N i); have hp:=Consent.solo ((a i)⁻¹) 1 (inv_pos.mpr h0) z _ hz; apply hp.trans; rw [pow_one,div_inv_eq_mul,← footprint C.S ℓ _ he]; apply le_trans (mul_le_mul_of_nonneg_right (show 2*(γ:ℝ) ≤2*(100*(X:ℝ)) from (mul_le_mul_of_nonneg_left (by exact_mod_cast CardsT.peg C.S ℓ (C.N i) he) (by norm_num))) h0.le); exact le_of_eq (by ring)
variable (ht:202*C.S.spacing j≤ K.extent) (hi:ℓ ≤ C.N i)
include hj ht hi in
lemma places (x:Cover) (hx:x∈ box (flex C.S ℓ (C.N i))): K.fault i (ratioTo C.S (C.N i) ℓ • (K.goalL j ℓ)+x):=by
    have hv:= indented K j ℓ hj
    have h:= (port i ℓ hi x hx).trans (mul_le_mul_of_nonneg_left (spacing_antitone C.S hj) (show (0:ℝ)≤200 from by norm_num))
    rw [fault,beach, Metric.mem_closedBall,dist_eq_norm, digit_plus, ← gears hi]; rw [dist_eq_norm] at hv
    rw[add_comm _ (digit _ x), add_sub_assoc]; apply (norm_add_le ..).trans; linarith only [h,hv,ht]
include ht hi hj
lemma notch (u:Averaging)(w:stalk C i):∃ O:Merit K i,∀ t:Stokes d,O.testR w t=((C.A i).regulator).average (K.heads i t 0 * CardsT.checkedT u (ratioTo C.S (C.N i) ℓ) w (K.goalL j ℓ)):=by
    obtain ⟨f,hg,h,hf⟩:= strummed C.S (K.goalL j ℓ) u w hi
    let W:= ↥(box γ); let V:= Fintype.equivFin W; let p(j:Fin (Fintype.card W)):=X • ψ + (V.symm j).val -- ψ macro j shadow !! hygiene 
    refine ⟨⟨_,p,f ∘ V.symm,fun i=> places _ _ _ _ hj ht hi _ ((V.symm i).property),fun i=>hg (V.symm i),(Equiv.sum_comp V.symm _).trans h⟩,?_⟩
    intro t; unfold Merit.testR CardsT.checkedT; rw [LinearMap.sum_apply,Finset.sum_apply,hf]
    conv_rhs=> rw [← Equiv.sum_comp V.symm]
    rw [Finset.mul_sum,map_sum]; refine sum_congr rfl fun v _=>?_
    change ((f (V.symm v):ℝ):ℂ) • ((Rᴮ i).average ((K.heads i t 0)*w (p v)))=(Rᴮ i).average ((K.heads i t 0)*( ((f (V.symm v):ℝ):ℂ) • w (p v))); rw [mul_smul_comm,map_smul]
omit ht hi hj
lemma joinsC {c n : Side}(g: Ratio c n)(he:Even c.val)(x:Cover)(h:Odd g.count.val): wrap n (g.count.val • x) ∈ (mural g he 0).margin ((wrap c) x) (g.count.val/16):=by
      rw [← Ratio.embed_wrap, Intag.key_margin _ _ _ _ _ h, zero_add, separation_self, Nat.zero_add]; omega
include hj hC ht
-- carry nonzero torus lamp across stencils.
lemma nonzeroV : ∀ᶠ i:ℕ in atTop,(wrap (C.S.side (C.R i) j) (K.goalJ j))≠0:=by
    obtain ⟨e,he,h⟩:= GaugeP.sepF hC K; filter_upwards [h,hC.uv.tendsto_atTop.eventually_ge_atTop ℓ] with i h hi hZ; let b:= ratioTo C.S (C.N i) ℓ • (K.goalL j ℓ)
    have hp:K.fault i b:=by rw [← add_zero b]; exact places K i j ℓ hj ht hi 0 (center_box _)
    have he':wrap (C.S.side (C.R i) (C.N i)) b=0:=by unfold b goalL; let g₀:=viewW C.S (C.R i) hj; let g:=viewW C.S (C.R i) hi; change wrap _ (g.count.val • (g₀.count.val • (K.goalJ j)))=_; simp_rw [← Ratio.embed_wrap,hZ]; simp only [Ratio.embed]; simp
    have hh:e ≤ (a i)*separation (wrap _ 0) (wrap (C.S.side (C.R i) (C.N i)) b):=h b hp 0 1 (by decide); rw[map_zero,he',separation_self,Nat.cast_zero,mul_zero] at hh; exact not_le_of_gt he hh
end GaugeP
end YM.Massive.Needle
#print axioms YM.Massive.Needle.GaugeP.nonzeroV
#print axioms YM.Massive.Needle.GaugeP.notch
