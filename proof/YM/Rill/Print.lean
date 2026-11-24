import YM.Rill.Lair
/-! Abstract list calculus literal. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Choir
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Filter Set Metric
open Lattice Cells Lyre QCD QCD.Lat QCD.Tide QCD.Grass QCD.Plum QCD.RP QCD.Revolve UV Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.Vale Romance
open scoped Topology ContDiff BigOperators Classical ComplexOrder
open Function Sash TorusPCAC.Geometry Strip Petals Finset
variable {C:Sequence} {P:Calibration C}(hQ:P.System) {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop) {Q: Choir}(L:Pollens P Q) (v w: Strip Q)(x y:E4)(a:Axis) {β e:ℝ}(hp:C.Path β e) {n:ℕ}
namespace Strip
noncomputable def shifting (v:Strip Q)(x:E4):Strip Q:= v.map fun i=> (i.1+x,i.2)
lemma travel : Strip.shifting (Strip.shifting v x) y=Strip.shifting v (x+y):=by simp [Strip.shifting,List.map_map,comp_def,add_assoc]
lemma rest : Strip.shifting v 0=v :=by simp [Strip.shifting]
lemma traverse : Strip.shifting (v++w) x=Strip.shifting v x++Strip.shifting w x:=by simp only [Strip.shifting,List.map_append]
lemma maintains(h: Strip.distinct v): Strip.distinct (Strip.shifting v x):=by
     rw [spots,show List.map Prod.fst (Strip.shifting v x)= (v.map Prod.fst).map (fun z=>z+x) from (by simp [Strip.shifting,List.map_map])]; exact ((spots v).mp h).map (fun _ _ h=> add_right_cancel h)
lemma spinful (a:Axis) (w:Strip Q)(x:E4): oppositeS L a (Strip.shifting w x)=Strip.shifting (oppositeS L a w) (Ortho.move (Signed.reflect a) x):=by
    simp only [Strip.shifting,oppositeS,←List.map_reverse,List.map_map]; congr 1; ext1 i; exact Prod.ext ((Ortho.motion _).map_add ..) rfl
lemma twisted (h:Q.Domestic) : oppositeS L a (oppositeS L a v)=v:=by
    suffices h: ∀ i:E4, Ortho.move (Signed.reflect a) (Ortho.move (Signed.reflect a) i)=i by
         simp only [oppositeS,← List.map_reverse,List.reverse_reverse,List.map_map]; unfold Function.comp; have hv:= L.reflex ‹Q.Domestic› a; simp [hv _,h]
    intro i; ext1 j; by_cases he:j=a <;> simp [Signed.mirrored,he]
lemma nodes : oppositeS L a (v++w)=oppositeS L a w++oppositeS L a v:=by simp only [oppositeS,List.reverse_append,List.map_append]
abbrev readV (Q:Choir) {n:ℕ}(z:Fin n→ E4 × Q.W):Strip Q:=List.ofFn z
lemma report (z:Fin n→ E4 × Q.W): tone (readV Q z)= Q.total n (points fun i=>(z i).1) (fun i=>(z i).2):=by
     let l:= List.finRange n; have he: List.length l=n:=List.length_finRange; let X:E4:=0
     have h(u:Strip Q) (hp:n=u.length)(g:Fin n→ E4 × Q.W)(ht:∀ i,u.get (Fin.cast hp i)=g i): tone u= Q.total n (points fun i=>(g i).1) (fun i=>(g i).2):=by
         clear he z l; subst n; unfold tone locus; congr 1; · congr 1; ext1 i; exact congr_arg Prod.fst (ht i)
         exact funext fun i=> congr_arg Prod.snd (ht i)
     exact h (readV Q z) (by simp[readV]) z fun i=> by simp [readV]
include hp hφ hQ
variable (H:Q.Harmony P φ)
include H
lemma migrates (hv: Strip.distinct v): tone (Strip.shifting v x)=tone v:=by
    rw [show Strip.shifting v x=readV Q (fun i:Fin v.length=> ((v.get i).1+x,(v.get i).2)) from ?_,report]; exact HarmonyF.carried hp H hφ hQ (locus v) hv _ _
    unfold Strip.shifting readV; conv_lhs => arg 2; rw [← List.ofFn_get v]
    rw[List.map_ofFn]; rfl
lemma console (hv:Strip.distinct v): tone (oppositeS L a v)=star (tone v):=by
    rw [show oppositeS L a v= readV Q (fun i:Fin v.length=> (Ortho.move (Signed.reflect a) ((v.get i.rev).1), L.adj a (v.get i.rev).2)) from ?_,report]; exact HarmonyF.swung hp H hφ hQ L (locus v) hv (fun j=> (v.get j).2) a
    unfold oppositeS; conv_lhs => arg 2; arg 1; rw [← List.ofFn_get v]
    rw [← UV.Free.Lyre.reversesV v.get,List.map_ofFn]; rfl
end Strip
end YM.Massive.Tarn.Choir
#print axioms YM.Massive.Tarn.Choir.Strip.console
#print axioms YM.Massive.Tarn.Choir.Strip.twisted
