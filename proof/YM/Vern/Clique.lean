import YM.Vern.Hut
set_option autoImplicit false
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Vern
open Function Set Filter Analysis MeasureTheory Lattice QCD QCD.Lat
open Massive Massive.UV Massive.Tarn Massive.Tarn.Choir Massive.Tarn.Choir.Strip Massive.Patria.Gall.Onyx
open Massive.Tarn.ChargeQ Massive.Poised.Plans.Stamp.Stair Massive.Gust
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix InnerProductSpace
open Sprig Intag.Sprig UV.Free Massive.Poised.Plans.Stamp Heron Iceberg Lobo NativeV
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K}{d:ℕ}
variable {φ:ℕ→ℕ}(hf:Foil P K T)(HQ:K.Harmony P φ)(E:Canopy P φ K)(X:Lanterns T E)
variable (V:Axis× Axis→ K.W)(hV: Persona T V)(J:Axle K (fun a b=>V (a,b))) (B:Vane J)
variable (r:ℝ)(hr:0<r)(s:ℝ)(z:IceT→ℝ)
set_option quotPrecheck false
local notation "H₁"=> ↥(seedP T 8)
local notation "H₂"=> ↥(seedP T 10)
local notation "N₁"=> ↥(seatP 8)
local notation "N₂"=> ↥(seatP 10)
variable (L:Tri→Module.End ℂ ↥(seatP 8))(L':Tri→Module.End ℂ ↥(seatP 10))
variable (F: ↥(seatP 8)≃ₗ[ℂ]↥(seedP T 8))(F': ↥(seatP 10)≃ₗ[ℂ]↥(seedP T 10))
variable (a:Axis)
variable (hF:Feasible hf HQ E X V hV J (d:=8) (Nat.le_refl _) s z L F)
variable (hW:Feasible hf HQ E X V hV J (d:=10) (by decide) s z L' F')
variable (e:Hail.RightAuth P.sym)
variable (f:Flavor 6)(he:z none ≠ z (some f))
local notation "C₀"=> metal hf HQ V hV J B r hr s
local notation "D₀"=> dayV hf HQ V hV J B r hr s

open Finset
noncomputable def Starx(f:Flavor 6):(seatP 10):= Mango f 2 1 - Mango f 1 2 + Pont f 0
lemma star0 : (Starx f).val= projection ((Tawny.Cast.Zinc.starV f).val 0):=by rw [act_star,map_sub]; rfl
include hW he e hr B
lemma sunup : ∀ i j:Tri,(C₀).T.knot (glowZ F' f 1 2) (pearlZ F' f 0)=0:=by
       let T:= glowZ F' f; intro i j
       exact rain (C₀) _ _ _ (meetT hf HQ E X V hV J B r hr s z L' F' hW e f) (pearlZ F' f) (z none) (fun i j=>(smears hf HQ E X V hV J B r hr s z L' F' hW e f i j).1) (fun i j=>(smears hf HQ E X V hV J B r hr s z L' F' hW e f i j).2) he
private lemma salute {W:Type}[AddCommGroup W][Module ℂ W](T:Tide W)(x y:W): T.knot x (y-x) = T.knot x y - T.knot x x:= map_sub (T.zz x) ..
lemma forge_bar : (metal hf HQ V hV J B r hr s).T.knot (glowZ F' f 1 2) (F' (Starx f)) ≠ 0 :=by
     intro h
     let W:= glowZ F' f; let Q:= (C₀).T; let R:= (C₀).K (0:Tri); let p:=W 2 1-W 1 2; have hp:p≠0:=by
          intro hP; have hx: Mango f 2 1=Mango f 1 2:= F'.injective (sub_eq_zero.mp hP); have he : projection (pulseT f false 2 1)-projection (pulseT f false 1 2)=0:=sub_eq_zero.mpr (congr_arg Subtype.val hx); exact rock f (Eq.trans (map_sub projection _ _) he)
     have hv:=meetT hf HQ E X V hV J B r hr s z L' F' hW e f;
     have H: R (W 2 1) = -(W 1 2):=by unfold R W; rw [hv.cov 0 2 1]; rw[show τc 0 2=(-1:ℂ) from by unfold τc charI; simp +decide, show τc 0 1=(1:ℂ) from rfl,one_smul]; exact neg_one_smul ℂ (W 1 2)
     have H':R (W 1 2) = -W 2 1:=by unfold R W; rw[hv.cov 0 1 2]; rw[show τc 0 2=(-1:ℂ) from by unfold τc charI; simp +decide, show τc 0 1=(1:ℂ) from rfl,one_smul]; exact neg_one_smul ℂ (W 2 1)
     have hz:R p=p:=by unfold p; rw [_root_.map_sub,H,H']; abel
     unfold Starx at h; change Q.knot _ _= _ at h; rw[_root_.map_add,_root_.map_sub,Q.add] at h; have hy: Q.knot (W 1 2) p=0:=by
           change Q.knot (W 1 2) p+Q.knot (W 1 2) (pearlZ F' f 0)= 0 at h; rw [show Q.knot (W 1 2) (pearlZ F' f 0) = _ from sunup hf HQ E X V hV J B r hr s z L' F' hW e f he 0 0, add_zero] at h; exact h
     have HE:Q.knot (W 2 1) p=0:=by
           have hx: Q.knot (W 2 1) p= Q.knot (R (W 2 1)) (R p):=((C₀).unit 0 ..).symm
           rw [hx,H, hz]; calc Q.knot (-W 1 2) p= Q.knot ((-1:ℂ) • W 1 2) p:= by rw[show (-1:ℂ) • _= _ from neg_one_smul ℂ (W 1 2)]
                               _=0:=by rw [Q.seals,hy,mul_zero]
     have hM: Q.knot p p=0:=by -- subtract via conj
           rw [← Q.con p]; nth_rw 2 [show p= _ from (rfl:p= W 2 1-W 1 2)]; change star (Q.zz _ _)= _; rw [map_sub]; change star (Q.knot p _- Q.knot p _)=_; rw [← Q.con (W 1 2),← Q.con (W 2 1),HE,hy]; simp
     have hu:= Q.positive p hp; rw[hM] at hu; exact lt_irrefl _ hu
-- Rank gives D-space.M
variable (hP:P.System)(hD:(swingE K 1).range=(bits K).range)(hχ:∀ d, ∃ n:Lattice.Side, Injective (P.candidate d n 0))
include hP hD hχ hF hW he
open Massive.Patria.Rolls -- etc
lemma priced (k:ℕ) : (C₀).T.knot (glowZ F' f 1 2) (simV E X k 10 (Starx f))= 0:=by
    obtain ⟨n,h⟩:= hχ 10; obtain ⟨y,H⟩:= paddle 10 claw n hP h

    let w:= X.frame k 10; have ht:= reach_point T claw 10 shelV w (X.leaders k 10) H equalV (fun _=>rfl) HQ.h
    let Y:= Tawny.Cast.Zinc.starV f; let q:= (grab 10 claw (fun _=>proves 10 w) Y); have hv:q∈(swingE K 1).range:= by rw[hD]; exact ht.symm ▸ LinearMap.mem_range_self (grab 10 claw _) Y
    obtain ⟨Λ,hA⟩:= hv; let A:= obσ 1 K Λ; have hT:Tense T A:= (tense hP T HQ A hχ).1 (LinearMap.mem_range_self _ _)
    let S(i j:Axis): H₁:= ⟨⟨A (i,j),hT.lv _⟩,(show A (i,j)∈ safeV T from ⟨hT.parity _,fun k=> hT.flux k _⟩)⟩; let Xk:= (simV E X k 10 (Starx f))
    have hTz : Spire (C₀) (D₀) S:=by
          refine ⟨fun i a b=>Subtype.ext (Subtype.ext ?_),fun a b=> Subtype.ext (Subtype.ext (hT.sym a b))⟩
          change (shipP HQ.h i _ (S a b)).val.val=_; rw[sails]; exact hT.geo _ (Cup i) (fL i) a b
    have hp:Xk= ∑ i:Axis, (D₀).d i (S i 0):=by
          apply toe hf HQ; have hw:(scalarD T 10 Xk)= q 0:=by change (w (Starx f).val).val=_; rw [star0]; rfl
          rw [hw,_root_.map_sum,← hA]; exact lifta ..
    have hh(x:Axis): haze (C₀) (D₀) (glowZ F' f) x (S x 0)=0:=by
          have h:= nullOrig hf HQ E X V hV J B r hr s z L L' F F' x hF hW e f he (S x 0); rw[LinearMap.comp_apply,fixP (C₀) (D₀) S hTz,map_smul] at h; exact (mul_eq_zero.mp h).resolve_left (by norm_num)
    change (C₀).T.zz _ Xk= _; rw[hp,map_sum]; exact sum_eq_zero fun i _=>hh i
end YM.Vern
#print axioms YM.Vern.priced
#print axioms YM.Vern.forge_bar
