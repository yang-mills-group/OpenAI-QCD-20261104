import YM.Needle.Stove
/-!
   Relative offsets and one-special-slot prices. Does NOT require the root cost held in
   an arbitrary offset background tiling. Big tile centres shift on the exact comparison plane.
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
abbrev FocusK (C:Sequence)(i j:ℕ)(w:stalk C i)(v:ℝ):Prop:=∀ (h:j ≤C.N i)(he:Even (C.R i).val)(b:Cover),let g:=viewW C.S (C.R i) h; Gold ((C.A i).regulator) (mural g (evenW C.S (C.R i) he _) (wrap _ b)) 0 (w b) v
namespace FocusK
variable {i j:ℕ}{x y:stalk C i}{k c:ℝ}(hx:FocusK C i j x k) (z:ℂ)
include hx
protected lemma smul : FocusK C i j (z • x) (‖z‖*k):= fun h p b=> Gold.minted (hx h p b) z
protected lemma mono (he:k≤c):FocusK C i j x c:= fun h p b=>Gold.mono (hx h p b) he
protected lemma add (hy:FocusK C i j y c):FocusK C i j (x+y) (k+c):=fun h p b=> Gold.together (hx h p b) (hy h p b)
omit hx
protected lemma zero : FocusK C i j 0 0:=fun h p b=> Gold.nil
protected lemma sum {I:Type*}(s:Finset I)(x:I→stalk C i)(v:I→ℝ)(hp:∀ k∈s, FocusK C i j (x k) (v k)): FocusK C i j (∑ k∈s,x k) (∑ k∈s,v k):=by
   induction s using Finset.induction_on with | empty=>simp only [sum_empty]; exact FocusK.zero | insert a s ha ih=> rw [sum_insert ha,sum_insert ha]; exact FocusK.add (hp a (mem_insert_self ..)) (ih fun i h=>hp i (mem_insert_of_mem h))
end FocusK
-- Root shift accepts all slots. only one tracked orientation.W
namespace Roll
variable {c n f:Side}(g:Ratio c f)(l:Ratio f n)(G:Ratio c n)(he:Even c.val)(hl:Even f.val)(hg:Odd g.count.val)(hL:Odd l.count.val)
open Intag YM.Next.Rank.Station
variable {k:ℕ}(x:Fin k→Site n)(p:Site n)
include he hl hg hL
local notation "A"=> l.count.val
lemma windowZ (h: k*8<g.count.val) : ∃ (z:Site f)(r:Fin k→Site c),∀ i, x i∈ (mural G he (p+l.embed z)).margin (r i) (3*l.count.val):=by
    let V(i):= l.parent (x i-p); have ht :Odd G.count.val:=by rw[size_comp g l]; exact hL.mul hg
    obtain ⟨z,hR⟩:= Vent.balm g he V 4 (by decide) (by simpa using h); choose R hR using hR
    refine ⟨z,R,fun i=>?_⟩
    let y:=V i; let q:=R i; have hκ:l.embed y∈(mural G he (l.embed z)).margin q (A*4):= (stepSpan g l G z y q he hg hL _).1 (hR i)
    apply (key_margin _ _ _ _ _ ht _).mpr; have hy: 2*separation (x i-p) (l.embed y)< l.count.val:= midway l hL (x i-p)
    have hh:= (key_margin _ _ _ _ _ ht _).1 hκ; have hz : separation (x i) (p+l.embed z+ G.embed q)=separation (x i-p) (l.embed z+G.embed q):=by unfold separation; congr 1; abel
    rw [hz]; have hr:= separation_triangle (x i-p) (l.embed y) (l.embed z+G.embed q); omega
end Roll
end YM.Massive.Needle
#print axioms YM.Massive.Needle.Roll.windowZ
