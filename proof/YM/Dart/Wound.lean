import YM.Dart.Fabric
/-!
  # Additive deterministic aperture for matching all finite sums
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Set Function Filter Lattice Cells Lyre Lyre.Goblet Romance QCD QCD.Lat QCD.Tide QCD.Grass Plum QCD.RP Patria Patria.Depth Patria.Hub Intag Intag.Vale
open Finset UV Poised Poised.Plans Poised.Plans.Stamp Poised.Stative
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {C:Sequence} (P:Calibration C) (d:ℕ)
local notation "S"=> C.S
set_option quotPrecheck false
variable {P d} {E:Hub.Invest P d}(H:Rack E)
-- analytic reach: point-point open box probes.All at actual scales, not restricted to priors/meshes.
namespace GaugeP
variable {Z: Laurel d}{J: Landing P.sym Z}(K:GaugeP P Z J){β ν:ℝ}(hp:C.Path β ν)(hS:Sway C.S)(G:Capital P d 1)
include hS hp G
lemma shearsH : ∀ᶠ j in atTop,∃ L:ℝ,0 ≤ L∧ ∀ᶠ i:ℕ in atTop,∀ x:Cover, K.fault i x → ∀ U:stalk C i,∀ z:ℝ,0 ≤ z → FocusK C i (j+1) U z→ ‖K.heightH i x U‖ ≤ L * z:=by
    obtain ⟨e,he,h⟩:= sepF hp K
    obtain ⟨N,hN,hP⟩:= shyness hp e he 0
    filter_upwards [hS.high.eventually (eventually_gt_atTop (2*8)),(G.gains (v:=K.price)),eventually_ge_atTop N] with j hj hJ ht
    let V:= K.price*Hub.rayM C.S d 1 G.v j; have hV:0≤V:=mul_nonneg K.realH (G.power _)
    refine ⟨V,hV,?_⟩; filter_upwards [h,hJ,hp.uv.tendsto_atTop.eventually_ge_atTop (j+1),K.tall] with i hi hs hl hz0 x hx U z hz hu
    have h': seaM C i j (![0,x]:Fin 2→ Cover):= tide j i _ (hi x hx) (le_trans (Nat.le_succ _) hl) (lt_of_le_of_lt (spacing_antitone C.S ht) hP)
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hV hz)).2 fun k=>?_
    have hc:= hs (K.g i k) (hz0 k).1; let f: Fin 2→ stalk C i:=![K.heads i k,U]; let v:Fin 2→ℝ:= ![V,z]; have hy(s:Fin 2)(h:s≠1): GreenP C i j (f s) (v s):=by fin_cases s; exact hc; contradiction
    have hh:= oneK hp i j 1 f v hy hu ![0,x] h' hj hl
    unfold readS at hh; simp only[List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_nil, mul_one,f,v,Fin.prod_univ_succ] at hh; change ‖((C.A i).regulator).average ((K.heads i k) 0* U x)‖ ≤_; simpa using hh
omit hS hp G
variable {H}{x:(i:ℕ)→stalk C i}{a:ℕ→ Label d}
include hS hp G
lemma starlet (h:Arc H x a) : ∀ᶠ i in atTop,∀ (O: Merit K i), ‖O.testR (x i-stem P d i (a i))‖ ≤ 1:=by
   obtain ⟨j,⟨L,hL,Hj⟩,F,hF,hN⟩:= ((K.shearsH hp hS G).and ((tendsto_add_atTop_nat 1).eventually h.tideP)).exists
   have hh:Tendsto (fun i=>L*F i) atTop (𝓝 0):=by simpa only [mul_zero] using hF.const_mul L
   filter_upwards [Hj,hN,hh.eventually_le_const zero_lt_one] with i hi hx hh O
   apply (Merit.heldR O _ (L*F i) _).trans hh; intro j; exact hi _ (O.hi j) _ (F i) hx.1 hx.2
lemma twain (h:Arc H x a) (T:ℝ)(hT:0≤T)(hU:∀ᶠ i:ℕ in atTop,∃ O:Merit K i, ‖O.testR (x i)‖≤T):∃ V Z:ℝ,0≤V∧0≤Z∧∀ᶠ i in atTop, ‖K.tip E i (a i)‖ ≤ V∧ ‖K.tipEnd E i (a i)‖≤ Z*E.scale i:=by
   obtain ⟨V,hV,hx⟩:= h.wealth; obtain ⟨Z,C,hZ,hc,Hv⟩:= K.racks hp hS G H V (T+1) hV (by positivity:0≤T+1) -- order 
   refine ⟨Z,C,hZ.le,hc,?_⟩; filter_upwards [hU,hx,Hv,K.starlet hp hS G h] with i hi hx hp h1
   obtain ⟨O,hO⟩:=hi; refine hp (a i) hx ⟨O,?_⟩; have hh : ‖O.testR (x i)-O.testR (stem P d i (a i))‖ ≤ 1:=by rw[← map_sub]; exact h1 _
   have ht:= norm_sub_le (O.testR (x i)) (O.testR (x i)-O.testR (stem P d i (a i))); rw [sub_sub_self] at ht; exact ht.trans (add_le_add hO hh)
end GaugeP
end YM.Massive.Needle
#print axioms YM.Massive.Needle.GaugeP.twain
