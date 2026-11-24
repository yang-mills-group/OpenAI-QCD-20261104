import YM.MassiveQCD.Stitch.Bell
import YM.QCD.Loom.Many
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Stitch
open QCD QCD.Grass QCD.Lat QCD.Creek Lattice Wilson RG QCD.Cove QCD.Cove.Send QCD.Creek.Ledge
open Function Ribbon Finset Filter MeasureTheory NormedSpace Fj
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I E D J:Type} [Fintype I] {N:ℕ} {f c:Side}{P:Rise f N E J}
local notation "S"=> Spine I
local notation "X'"=> Keys f N⊕Spine I
local notation "Y'"=> Keys c N⊕Spine I
variable (X:Tablet P I)
namespace Tablet
variable {R:Ratio c f}{t:ℝ}
variable (G:Send R N D)
local notation "A"=> Modes f N
local notation "B"=> Modes c N
local notation "W"=> Junta c f N
variable {q:I→Bool}{o:I→Site f}(hw:X.Wave t q o) {M:Fj D E J→Support c} (h:Cove.Count G P M)
-- charter coins for all rooted terms through their REAL booked height. Latest q arbitrary. No per-marker radius in books here; presumed charges already scaled by choosing input values.
abbrev chip (a:ℝ) (A':Type*) (B':Type*) : A'⊕B'→ℝ:= Sum.elim (fun _=>a) (fun _=>1)
noncomputable def credits (a:ℝ)(x:Tine c N I):ℝ:= load (chip a _ _) (light _ x)
structure Coins (u:E→ℝ)(w:J→ℝ)(a t:ℝ) :Prop where
 pos :0≤u
 non:0≤w
 ready i x : credits a (X.read t x i) ≤ u i
 fee i x: credits a (X.plug i x) ≤ w i
variable {u:E→ℝ}{w:J→ℝ}{m:D→ℝ}{a b r:ℝ}
variable (hh:X.Coins u w a t)(hc:Peak G t a b r m)
include hh
lemma receipt (s:Finset (Fj D E J))(V:Grid f): credits a (X.made t V s) ≤ (∏ i∈leftE s, (Real.exp (u i)-1))*∏ j∈spent s,w j:=by
    have hx:=funded (chip a (Keys f N) S) (leftE s) (fun i=> exp (X.read t V i)-1) _ (fun i _=> bought _ _ _ (hh.ready i V))
    unfold credits made; rw [map_mul]; exact (load_mul ..).trans (mul_le_mul hx (funded _ (spent s) _ _ (fun i _=> hh.fee i V)) (load_nn ..) ((load_nn ..).trans hx))
omit hh
include hc
lemma remitFee (s:Finset (Fj D E J))(U:Grid f)(he:closeS G P t s U)(x: Alg (Keys f N))(hx:x∈region (limits (coreW G P s))):
    load (fun _=>b) (tunnel G s U x)≤ r^(kappa (G.trim+1) N * invSize P s)*((∏ i∈ops s,m i)*load (fun _=>a) x):=by
   let z':= (near A B x); let x':= axle G U s z'; let y:= rateF c f N a b; let T := halo (G.trim+1) (P.wish (spent s)); let V:Finset W:= (limits T).map (ha c f N); let Q i:= if i∈V then r*y i else y i; have hv:V.card ≤ _:=k_payment G P s; have hy(i:W):0<y i:=by cases i with
     | inl i => cases i <;> first| exact hc.bud|exact hc.cup
     | inr i => cases i <;> first| exact hc.bud|exact hc.cup
   have hQ i:0<Q i:=by unfold Q; split; exact mul_pos (zero_lt_one.trans_le hc.post) (hy _); exact hy _
   have hg :load y z'=load (fun _=>a) x:=by
      change load y (embed (ha c f N) x)=_; rw [transplant hy]; exact congr_arg (fun p=> load p x) (funext fun i=>wagesA B i a b)
   have hk:Ledge.Pledge y (axle G U s) (∏ i∈ops s,m i):=pledge_spin _ _ y m (fun i _=> hc.spare i U) _
   exact (ferry (wipe A B (G.shortP U)) hQ (per_bill G P hc s U he) x' (lamp G s U x hx)).trans ((sail V y r hy hc.post x').trans (mul_le_mul (pow_le_pow_right₀ hc.post hv) (hg ▸ hk.rates z') (load_nn ..) (pow_nonneg (zero_le_one.trans hc.post) _)))
omit hc
lemma polite_bill (s:Finset I)(x:Tine c N I)(h:Polite q s x)(he:0<a): credits a x=load (fun _=>a) (scrape _ (burst q s) x.val):=by
   unfold credits; rw [show light _ x=stake _ (burst q s) (scrape _ (burst q s) x.val) from h.exact.symm,show chip a (Keys c N) S=expRate (p:=fun _=>a) (q:=fun _=>1) from rfl, stakesBill (p:=fun _=>a) (q:=fun _=>1) (fun _=>he) (fun _=>one_pos)]; simp
include hh hw hc
lemma wage (s:Finset (Fj D E J))(U:Grid f): credits b (X.hue t G s U)≤r^(kappa (G.trim+1) N * invSize P s)*priceSet s m u w:=by
    unfold Tablet.hue; split
    next ht=>
      let x:= X.made t U s; let Y:= X.markers s; let z:= burst q Y; let p:= scrape (Keys f N) z x.val; have ⟨hp,hV⟩:=X.lights_made G hw s U; have he:Polite q Y (X.dye t G s U):=politeStep _ hp rfl; let k:=∏ i∈ops s,m i; rw [polite_bill _ _ he hc.cup,show scrape (Keys c N) (burst q Y) (X.dye t G s U).val= tunnel G s U p from wing ..];
      apply (remitFee G hc s U ht.2 p (hV z)).trans -- x param not included?
      rw [← polite_bill _ _ hp hc.bud]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (X.receipt hh s U) (prod_nonneg fun i _=>(hc.spare i U).nn)) (pow_nonneg (zero_le_one.trans hc.post) _)
    rw [credits,map_zero,QCD.Cove.load_zero]; unfold priceSet; refine mul_nonneg (pow_nonneg (zero_le_one.trans hc.post) _) (mul_nonneg (prod_nonneg fun i _=>(hc.spare i U).nn) (mul_nonneg (prod_nonneg fun i _=> sub_nonneg.mpr (Real.one_le_exp (hh.pos i))) (prod_nonneg fun i _=> hh.non i))) -- implicit U missing!
lemma pinch_new (U:Grid f){s:Finset (Fj D E J)}(he:Further.ShellBirth49.Fusing.Collide.spark M s): credits b (X.hue t G s U) ≤ jewel G P M m u w r s:=by
    unfold jewel; split
    · exact X.wage G hw hh hc s U -- order
    next hj=>
     push Not at hj
     obtain ⟨h1,h2⟩:=hj he; unfold hue; split
     · unfold credits; rw [show light _ (Tablet.dye X t G s U) = 0 from ?_,QCD.Cove.load_zero]
       have hs:= he.1; have hp:(ops s).Nonempty:=by
           have hv:=pinch s; rw [h1,h2] at hv; rw [←hv] at hs; obtain ⟨w,hw⟩:=hs; unfold pin at hw; cases w
           next i=> exact ⟨i,by simpa using hw⟩
           next i=> rcases i with v|v <;> simp at hw
       have hk: axle G U s 1=0:=by
          unfold axle; obtain ⟨i,hi⟩:=hp; rw [← noncommProd_erase_mul _ hi,mul_apply_eq_comp,show bucks G _ U 1=0 from G.fuel U _,map_zero]
       change carry S _ _=_; rw [show Tablet.made X t U s=1 from by unfold made; rw [h1,h2,prod_empty,prod_empty,mul_one],show (1:Tine f N I).val=stake (Keys f N) ∅ 1 from (Eq.trans (quiet ..) (map_one _)).symm,speaks]; rw [show tunnel G s U 1=0 from ?_,map_zero]; change wipe A B _ (axle G U s (near _ _ 1))=0; rw [map_one,hk,map_zero]
     unfold credits; rw [map_zero,QCD.Cove.load_zero]
end Tablet
end YM.MassiveQCD.Stitch
