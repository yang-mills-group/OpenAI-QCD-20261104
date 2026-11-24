import YM.Bwana.Sol
import YM.Pods.Cove
/-! reflected paths recalibrate offset readings. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Depth.Off
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory
open Poised Plans Display Orientation Exposure Rolls Canvas
variable {S:Scheme}{r:Side}{N J d i j m k:ℕ}(A:Run S N r 6)(H:SourceRead.TaperHol)(sym:RawSym) (B:Bore d)(hf:Rubric sym B) (hA:A.Actual)(W:Market S r d)(hW:Wager A H B W m)
variable (b:ℕ→ Cover)(hB:Borders S m N b)(v w:Label d)
local notation "Tr"=> carrier A B
local notation "Φ"=> Signed.mirror
open Planned.PrimaryIntegral295 Carrier
lemma act_times(s:Signed)(c:ℕ)(x:Cover):s.act (c • x)=c • s.act x:=by induction c with|zero=> simp|succ n ih=> rw [add_smul,one_smul, add_smul,one_smul,Signed.act_add,ih] -- typo
lemma lup_shift (u:N = N)(s:Signed)(x:Cover): lup S (s.act ∘ b) N i (s.act x)= s.act (lup S b N i x):=by unfold lup; rw [Signed.act_add,act_times,Signed.act_sub]; rfl
lemma vport {L:Side}(h:Odd L.val)(s:Signed)(x:Cover):cellar L (s.act x)= s.act (cellar L x):=by
      have hh:= congr_arg s.act (Carrier.balance L x); have ht:= Carrier.balance L (s.act x)
      apply smul_right_injective Cover L.pos.ne'; dsimp only
      rw [← wrap_signed,Ratio.lift_signed_of_odd h] at ht; rw [Signed.act_add,act_times] at hh; exact add_left_cancel (ht.symm.trans hh)
include hB
lemma mirror_b(s:Signed): Borders S m N (s.act ∘ b):=by intro i hn hi; simp_rw[Function.comp_apply, vport (S.step i).odd,hB i hn hi]
omit hB
include hf hA
lemma inherits(a:Axis)(x:Cover)(h:i ≤ N): Action.adj a (Tr b i x v)= Tr ((Φ a).act ∘ b) i ((Φ a).act x) (sym.adj _ a v):=by
      let p:= lup S b N i x; unfold carrier; rw [lup_shift b rfl] -- sig
      refine eyes A a _ _ ?_ h
      funext U; rw [eye_value]; let s:= Φ a; let g:= tilt (eyeP (S.side r N) a); let V:=pull (K:=su.El) s 0 U; let T:= A.regulator.density
      have hh: g (B (S.side r N) p v V)=B _ (s.act p) (sym.adj _ a v) U:= (eye_value ..).symm.trans (congr_fun (hf.eye _ v p a) U)
      have hh': g (T V)= T U:= (eye_value ..).symm.trans (congr_fun (eye_pivot a _ rfl) U)
      let Z:= B (S.side r N) p v; change g (T V * Z V)= _; rw [show g (T V * Z V)=g (Z V)* g (T V) from tilt_mul ..,hh',show g (Z V)=_ from hh]; have hZ:Plus (T U):=by rw [show T U=A.density N U from (congr_fun hA.start U).symm]; exact hA.even le_rfl U
      exact (hZ.central _).eq -- orientation?
include hW
open Hub
lemma thrust (a:Axis)(he:b m=0)(h:Hora A H B m b v w): Hora A H B m ((Φ a).act ∘ b) (sym.adj _ a v) (sym.adj _ a w):=by
      let V:= Tr b m (b m) v; have hm : Tally H 0 w (A.density m) V := by exact Eq.mp (congr_arg (fun x:Cover=> Tally H x _ _ V) he) h
      unfold Hora; rw [Function.comp_apply, ←inherits A sym B hf hA b v a _ hW.siteM]; change Tally H ((Φ a).act (b m)) _ _ (Action.adj a V); rw [he, Signed.act_zero]
      have hv:= arrives A m hW.siteM; exact Canvas.flux H _ a hW.living _ (fun x:Label d=>⇑(B (S.side r m) 0 x)) hm hW.reading (by rw [pier A hA hW.siteM]; exact hv.2.1 a) (by rw[pier A hA hW.siteM]; exact hv.2.2.2.2) (by have hh:=hf.eye (S.side r m) w 0 a; rw [Signed.act_zero] at hh; exact hh)
omit hW hf hA
abbrev sawC : List Axis→(ℕ→ Cover)
 | []=> b
 | a::l=> (Φ a).act ∘ sawC l
lemma sticks (l:List Axis)(hx:b j=0): sawC b l j=0:=by induction l with|nil=> exact hx|cons a l ih=> unfold sawC; rw[Function.comp_apply,ih, Signed.act_zero]
lemma respects (l:List Axis) : sawC (fun _=>0) l=(fun _=> (0:Cover)):=funext fun i=> sticks (fun _=>0) l rfl
include hB in
lemma bordered (l:List Axis): Borders S m N (sawC b l):=by induction l with|nil=>exact hB|cons a l ih=> exact mirror_b (sawC b l) ih (Φ a)
include hW hf hA
lemma flagsV (l:List Axis)(he:b m=0)(hp:Hora A H B m b v w): Hora A H B m (sawC b l) (spine sym v l) (spine sym w l):=by induction l with|nil=> exact hp|cons a l ih=> exact thrust A H sym B hf hA W hW (sawC b l) _ _ a (sticks b l he) ih
end YM.Massive.Patria.Depth.Off
#print axioms YM.Massive.Patria.Depth.Off.bordered
#print axioms YM.Massive.Patria.Depth.Off.respects
#print axioms YM.Massive.Patria.Depth.Off.flagsV
