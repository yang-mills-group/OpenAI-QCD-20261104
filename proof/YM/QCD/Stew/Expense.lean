import YM.QCD.Stew.Supr
/-! # Prefix coins for pre-limit move. requires 4<=period already.
Power weights can be reduced after making columns. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N n z:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ} {w r a u t:ℝ}{p:BudgetPoint}{o:Site c}
open Revolve Flume Quarry AnalyticBridge.VerifiedReset Port Footprint
variable {ι:Type}(E:Gem c N ι)(b:Flavor N)
open Residual
lemma sprayer (t:ℝ)(f g:Support c)(X:Grid c→EvenA c N)(U V:Grid c)(K:EvenA c N →+* EvenA c N)(Y:Grid c→EvenA c N)(he:Healthy t f U↔Healthy t g V) (h : K (X U)=Y V): K (masked t f X U) = masked t g Y V:=by
   by_cases hv:Healthy t f U; · rw [masked_eq _ _ _ _ hv, masked_eq _ _ _ _ (he.1 hv)]; exact h
   rw [masked_ne _ _ _ _ hv,masked_ne _ _ _ _ (mt he.2 hv), map_zero]
lemma shadesU (t:ℝ)(f:Support c)(X:Grid c→EvenA c N)(U V:Grid c)(G:Equiv.Perm (Site c)) (hx: (flags t U).image G=flags t V): Healthy t f U↔ Healthy t (f.image G) V:=by unfold Healthy; rw [←hx, Finset.disjoint_image G.injective]
lemma auto (hf:E.Gather)(h:Crossing E)(t:ℝ): (lien E b t).Garish:=by
    have hx := (lunar E b hf h).blank
    let X := dearth E b; let p:=lien E b t
    have he(i:ι)(Z:Lat.Frame c) (M :EvenA c N→+*EvenA c N)(U:Grid c) (V: Grid c)(hp:V = gauge Z U)(ht: M (E.view i V)=E.view i U)(hk:M (mintF E b V i)=mintF E b U i): M (p.mean i V)=p.mean i U:=by
        have hd P:Healthy t P V↔Healthy t P U:=by unfold Healthy; rw [hp,gauge_flags]; -- semicolon
        rw [show p.mean i V=_ from Stew.dry .., show p.mean i U=_ from Stew.dry ..]; by_cases h:Healthy t (way (E.addr i)) V
        · rw [if_pos h, if_pos ((hd _).mp h),map_zero]
        rw [if_neg h,if_neg (mt (hd _).2 h), map_sub,hk]; apply congr_arg₂ (·-·) _ rfl; exact sprayer _ _ _ _ V U _ _ (hd _) ht
    constructor
    · intro i U k; exact congr_arg Subtype.val (he i k (trade (Lat.rotates N k)).passL U _ rfl (Subtype.ext (h.blank.gauge i U k)) (Subtype.ext (gainR E b i U k)))
    · intro i U; exact he i (fun _=>1) _ U U (Villa.presenceP U).symm (h.blank.real i U) (warpR E b h.blank i U)
    · intro i U W hk; exact he i (fun _=>1) _ U U (Villa.presenceP U).symm (h.blank.num i U W hk) (form_fit _ N W hk)
    intro s k g hS; obtain ⟨e,hF⟩:= h.rays s k g hS
    have hE i : way (E.addr (e i))=(way (E.addr i)).image (act s):=by rw [(hF i).1]; exact congr_arg RegularAddress.support (skyRose _ _)
    refine ⟨e,hE,fun i U=>?_⟩; obtain ⟨ht,hH⟩:= hF i; let V:=sky s U; rw [Stew.dry,Stew.dry, hE]
    have hv: (flags t V).image (act s)=flags t U:=Work.H03.flags_send ..; have hi:=shadesU t (way (E.addr i)) (E.view i) V U _ hv
    by_cases hk: Healthy t (way (E.addr i)) V; · rw [if_pos hk,if_pos (hi.mp hk),map_zero] -- V definitional may fail
    rw [if_neg hk,if_neg (mt hi.mpr hk),map_sub]; exact congr_arg₂ (·-·) (sprayer t _ _ _ V U _ _ (ht.symm ▸ shadesU t (E.addr i).support (E.view i) V U _ hv) (hH _)) (turnC E b s _ _ hS i (e i) ht hH (hf.role ..) (h.blank.num i 1) (h.blank.gauge i) U)
-- temperature.
lemma invoices (n m N:ℕ): ∃ C:ℝ,1 ≤ C∧∀ (c:Side)(b:Flavor N)(B:BudgetPoint)(u:ℝ),B.order≤ n→B.power≤ m→0<u→∀ (ι:Type)(E:Gem c N ι)(j:ι) (r:ℝ), Woven (E.addr j).site (E.addr j).support B u (E.view j) r→ let p:= (dearth E b)
     Woven (E.addr j).site (stand (E.addr j).site) B u (fun V=>mintF E b V j) (C*r) ∧ (∀ V, Sen (E.addr j).site u (mintF E b V j)≤ C*r) ∧
       Woven (p.addr j).site (p.addr j).support B u (p.view j) ((1+C)*r)∧∀ V, Sen (p.addr j).site u ((lien E b B.threshold).mean j V) ≤ (1+C)*r :=by
   obtain ⟨K,h,hk⟩:=monarch n m N; obtain ⟨V,hV,hQ⟩:=preMoment
   let D:= Fintype.card SampleX; let c:= K*V; let Z:= c*D; have hv:0<c:=mul_pos h (by linarith)
   refine ⟨max 1 Z,le_max_left ..,fun b' l B u hn hm hu ι E j r he=>?_⟩; intro p
   let X:= (E.addr j).site; let A:= stand X; have he' :=he.travel
   have hz(i:SampleX) :u^2*‖lane E l j i‖ ≤V*r:=by
      unfold lane mote; split; swap; · rw [norm_zero,mul_zero]; positivity
      apply (hQ _ _ _ X _ _ _ hu.le).trans; exact mul_le_mul_of_nonneg_left (he.sizeU 1 (flat_ok ..)) (zero_le_one.trans hV)
   let f i (V:Grid b'):=paleF N (entry X (lane E l j i) i V); have hp(i):Woven X A B u (f i) (c*r) ∧∀ V, Sen X u (f i V)≤ c*r:=by
      have hb:= hk b' B hn hm X u hu i (lane E l j i); have hL:K* (u^2*‖lane E l j i‖) ≤ c*r:=(mul_le_mul_of_nonneg_left (hz i) h.le).trans_eq (mul_assoc ..).symm
      exact ⟨hb.1.stretches (Subset.refl _) hL,fun V=> (hb.2 _).trans hL⟩
   let C:=max 1 Z; have hH : D • (c*r) ≤ C*r:=by rw [show D • (c*r)=Z*r from ?_]; exact mul_le_mul_of_nonneg_right (le_max_right ..) he'; unfold Z; rw [nsmul_eq_mul]; ring
   let g V := mintF E l V j; have hG:g=∑ i,f i:=by funext V; simp_rw [Finset.sum_apply]; exact map_sum (nozzle _ N) ..
   have hg:Woven X A B u g (C*r):=by rw [hG]; apply (Woven.sumX f _ (fun _=>c*r) (fun i _=> (hp i).1)).stretches (Subset.refl _); rwa [sum_const]
   have hc V:Sen X u (g V) ≤ C*r:=by rw [hG,Finset.sum_apply,← measures,map_sum]; apply (norm_sum_le ..).trans; exact (sum_le_sum (fun i _=>(hp i).2 V)).trans (by rwa [sum_const]) -- sum apply ambigu
   refine ⟨hg,hc,?_,?_⟩
   · let h1:= (he.stretches (subset_union_left (s₂:=A)) le_rfl).addition ((hg.byScalar (-1)).stretches (subset_union_right (s₁:=(E.addr j).support)) le_rfl)
     rw [norm_neg,norm_one,one_mul,neg_one_smul,← sub_eq_add_neg] at h1; rw [add_mul,one_mul]; exact h1
   intro V; rw [Stew.dry]; split; next h=> rw [← measures,map_zero,norm_zero]; exact mul_nonneg (by have H:= le_max_left 1 Z; linarith) he'
   next _=> rw [← measures,map_sub, add_mul,one_mul]; apply (norm_sub_le ..).trans; apply add_le_add _ (hc V); unfold letters
            by_cases hb:Healthy B.threshold (E.addr j).support V; · rw [masked_eq _ _ _ _ hb]; exact he.sizeU V hb
            rw [masked_ne _ _ _ _ hb,map_zero,norm_zero]; exact he'
end YM.QCD.Stew
