import YM.Lust.Beam
import YM.Dart.Hill
/-!
   Priced envelope uniformly on all kernels. Bouquet lifetime claims.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Set Function Filter Lattice Cells Lyre Lyre.Goblet Romance QCD QCD.Lat QCD.Tide QCD.Grass Plum QCD.RP Patria Patria.Depth Patria.Hub Intag Intag.Vale
open Finset UV Poised Poised.Plans Poised.Plans.Stamp Poised.Stative
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {C:Sequence} {P:Calibration C} {d:ℕ}{E:Hub.Invest P d}{H:Rack E} (h:Wealthy H)(hS:Spring P d)(G:Capital P d 1)
abbrev LightP (C:Sequence) (x:(i:ℕ)→stalk C i):Prop:=∀ᶠ j in atTop, ∃ V:ℝ,0≤V∧∀ᶠ i in atTop, GreenP C i j (x i) V
abbrev DimP (C:Sequence) (x:(i:ℕ)→stalk C i):Prop:=∀ᶠ j in atTop,∃ f:ℕ→ℝ,Tendsto f atTop (𝓝 0) ∧ ∀ᶠ i in atTop,0 ≤ f i ∧ GreenP C i j (x i) (f i)
namespace GaugeP
open Investment
variable {Z:Laurel d}{J:Landing P.sym Z}(K: GaugeP P Z J)
-- arbitrary coefficients. projection+remainder uniform is strong.Based. Useful conversion to Slabs later.
include G in
lemma vine : ∀ᶠ j in atTop,∃ V:ℝ,0 ≤ V∧ ∀ᶠ i in atTop,∀ p:Stokes d→ ℂ, GreenP C i j (stem P d i (K.ridge i p)) (‖p‖*V):=by
    filter_upwards [G.nest] with j h; let V:= rayM C.S d 1 G.v j; refine ⟨K.heightM * V,mul_nonneg K.h_positive (G.power _),?_⟩; filter_upwards [h,K.pluck] with i hi hp p; exact GreenP.mono (hi _) ((mul_le_mul_of_nonneg_right (hp _) (G.power _)).trans_eq (by ring))
variable {β ν:ℝ}(hC:C.Path β ν)(hr:Sway C.S)(u:Averaging)
local notation "Ψ" i:arg=> stemV P d i u
include h hS hr hC G
-- exact calibrated averaged primaries uniform decomposition.K.Sea.
lemma card :∀ᶠ j in atTop,∃ L M:ℝ,0 ≤ L∧0≤M∧ ∃ F:ℕ→ℝ,Tendsto F atTop (𝓝 0)∧∀ᶠ i in atTop,0 ≤ F i∧∀ x:Label d, GreenP C i j ((Ψ i) x) (‖x‖*L)∧GreenP C i j (stem P d i (K.ridge i (glean (E:=E) K u i x))) (‖x‖* M)∧ GreenP C i j ((Ψ i) x-stem P d i (K.ridge i (glean (E:=E) K u i x))) (‖x‖* F i):=by
   obtain ⟨T,D,hT,hD,hX⟩:= K.attests hC G H hr h hS u
   filter_upwards [K.vine G, Investment.creditW E] with j hj ht; obtain ⟨C',hc,hh⟩:=hj
   obtain ⟨F,hF,H0⟩:=ht; let V(i):=D*(E.scale i*F i)
   have hv:Tendsto V atTop (𝓝 0):=by simpa only [V,mul_zero] using hF.const_mul D
   let M:= T*C'; have hM:0 ≤ M:=mul_nonneg hT hc
   refine ⟨M+1,M,by linarith,hM,V,hv,?_⟩; filter_upwards [H0,hh,hX, K.weave E hC G hr u,hv.eventually_le_const zero_lt_one] with i hi h hx hA hV
   have hl:0 ≤ V i :=mul_nonneg hD (mul_nonneg (E.pos _) hi.1); refine ⟨hl,fun x=>?_⟩
   let r:= glean (E:=E) K u i x; let q:=grains (E:=E) K u i x; let A:= stem P d i; let W:=A (ridge K i r); have he: (Ψ i) x=W+A (face E i q):=hA x
   have hw:GreenP C i j W (‖x‖*M):= GreenP.mono (h r) ((mul_le_mul_of_nonneg_right (hx x).1 hc).trans_eq (by unfold M; change T*‖x‖*C'= _; ring))
   have hz: GreenP C i j (A (face E i q)) (‖x‖*V i):= GreenP.mono (hi.2 q) ((mul_le_mul_of_nonneg_right (hx x).2 hi.1).trans_eq (by unfold V; ring))
   change GreenP _ _ _ _ _ ∧ GreenP _ _ _ W _ ∧ GreenP _ _ _ (_-W) _; rw [he, add_sub_cancel_left]; refine ⟨GreenP.mono (GreenP.add hw hz) ?_,hw,hz⟩; rw [← mul_add]; gcongr
lemma edges (z:ℕ→Label d)(V:ℝ)(hV:0 ≤V)(hz:∀ᶠ i in atTop, ‖z i‖≤V):LightP C (fun i=> (Ψ i) (z i))∧ DimP C (fun i=> (Ψ i) (z i)-stem P d i (K.ridge i (glean (E:=E) K u i (z i)))):=by
    have hp:= card h hS G K hC hr u
    constructor <;> filter_upwards [hp] with j h <;> obtain ⟨L,M,hL,hM,F,hF,H⟩:=h
    · refine ⟨_,mul_nonneg hV hL,?_⟩; filter_upwards [hz,H] with i hi hh; exact GreenP.mono (hh.2 (z i)).1 (mul_le_mul_of_nonneg_right hi hL)
    refine ⟨fun i=> V*F i,by simpa only [mul_zero] using hF.const_mul V,?_⟩; filter_upwards [H,hz] with i hi hh; exact ⟨mul_nonneg hV hi.1, GreenP.mono (hi.2 _).2.2 (mul_le_mul_of_nonneg_right hh hi.1)⟩
end GaugeP
end YM.Massive.Needle
#print axioms YM.Massive.Needle.GaugeP.edges
#print axioms YM.Massive.Needle.GaugeP.card
