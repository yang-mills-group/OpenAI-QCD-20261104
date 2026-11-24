import YM.Rill.Eves
/-! Strict reflected Grams.Central aperture. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Choir
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Filter Set Metric
open Lattice Cells Lyre QCD QCD.Lat QCD.Tide QCD.Grass QCD.Plum QCD.RP QCD.Revolve UV Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.Vale Romance
open scoped Topology ContDiff BigOperators Classical ComplexOrder
open Function Sash TorusPCAC.Geometry Strip
variable {C:Sequence} {P:Calibration C}(hQ:P.System) {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop) {Q: Choir}(L:Pollens P Q)(a:Axis)
noncomputable def oppositeS (v:Strip Q): Strip Q:= v.reverse.map fun z=> (Ortho.move (Signed.reflect a) z.1,L.adj a z.2)
abbrev Sunny (v:Strip Q)(a:Axis):Prop:= distinct v ∧∀ z∈ v,0<z.1 a
noncomputable abbrev crestG (n:ℕ) (v:Fin n→Strip Q)(c:Fin n→ℂ):ℂ:= ∑ i,∑ j,star (c i)*tone (oppositeS L a (v i)++ v j)*c j
lemma darkens (v:Strip Q)(hh: Sunny v a) :∀ z∈oppositeS L a v,z.1 a<0:=by
     intro z h; rcases List.mem_map.mp h with ⟨y,hb,rfl⟩; exact lt_of_le_of_lt (Eq.le (Signed.mirrored ..)) (by simpa using hh.2 _ (List.mem_reverse.mp hb)) -- oriented test
lemma dimV (v:Strip Q)(hp:distinct v): distinct (oppositeS L a v):=by
     rw [spots,show List.map Prod.fst (oppositeS L a v)= ((v.map Prod.fst).reverse.map (Ortho.move (Signed.reflect a))) from (by simp [oppositeS,List.map_map,Function.comp_def])]; exact (List.nodup_reverse.mpr ((spots _).mp hp)).map (Ortho.move_injective _)
lemma aheadV (l m:Strip Q)(hh:Sunny l a)(ht:Sunny m a):distinct (oppositeS L a l ++ m):=by
     rw [spots,List.map_append,List.nodup_append]; refine ⟨(spots _).mp (dimV L a l hh.1),(spots _).mp ht.1,?_⟩; rintro x hx y hy he; obtain ⟨x,hX,rfl⟩:= List.mem_map.mp hx; obtain ⟨y,hY,rfl⟩:= List.mem_map.mp hy; exact (darkens L a _ hh _ hX).not_ge ((congr_arg (fun y:E4=> y a) he).symm ▸ (ht.2 y hY).le)
namespace Strip
open Petals
variable (P)
variable {g:Averaging} {β e:ℝ}(hp:C.Path β e)
noncomputable def reflection (v:Petal P): Petal P:=⟨⟨v.fieldT.1,P.sym.adj v.fieldT.1 a v.fieldT.2⟩,fun i=> (Signed.mirror a).act (v.r i)+ (-step a),Ortho.move (Signed.reflect a) v.x⟩
lemma swung (v: Strip.Petal P) : (Ortho.move (Signed.reflect a) v.x,L.adj a (lap Q g v.fieldT)) = (sight g Q (reflection P a v)):= Prod.ext rfl (L.a ..)
lemma moveT (l:List (Petal P)): petals Q g (l.reverse.map (reflection P a))=oppositeS L a (petals Q g l):=by
     unfold petals oppositeS; rw [List.map_map,←List.map_reverse,List.map_map]; congr 1; -- congr blocking
     ext1 x; exact (swung P L a x).symm
variable {P}
set_option quotPrecheck false
local notation "Ω" i:arg=> panH (evenW C.S (C.R i) (hp.even i) (C.N i)) a
local notation "B" i:arg=> C.S.side (C.R i) (C.N i)
include hQ hp hφ
lemma rayT (u:Petal P)(g:Averaging):∀ᶠ i in atTop, picture (Ω (φ i)) ((C.A (φ i)).regulator.zeroCut) (signalW g u φ i)= signalW g (reflection P a u) φ i:=by
    filter_upwards [hφ.eventually (hQ.mixing u.fieldT.1)] with i hi; let k:=φ i; let v:=u.fieldT; let τ:=P.physical g k v.2 (u.r i); let z:Label v.1:=P.sym.adj _ a v.2
    let b:=(Signed.mirror a).act (u.r i); have he:Cylinder.Action.adj a ⇑τ = P.physical g k z b:=by unfold τ Calibration.physical; rw[hQ.sections.star,hi.star] 
    ext1 U; let p:= Ω k; let F:=(C.A k).regulator.zeroCut; have hf:tallH p (τ)=march (-step a) (Cylinder.Action.adj a τ):= paintC p (-step a) (earnedSign (evenW C.S (C.R k) (hp.even k) _) a) τ -- order
    change picture p F τ U=P.physical g k z (b+ -step a) U; change crown p F ⇑τ U=P.physical g k z (b+ -step a) U; rw [tallC _ _ rfl,hf,he]; apply congr_fun; unfold Calibration.physical; let V(c:Cover)(x:Label v.1):= funext (hQ.sections.localizes _ (B k) c x); rw[V,V]; exact Canvas.stylus ..
omit hQ
lemma thrum (u:Petal P)(h: Atlas C P φ u):Atlas C P φ (reflection P a u):=by
    let s:=Signed.mirror a; let A(i):=C.S.spacing (C.N (φ i)); have h':Tendsto A atTop (𝓝 0):=(tendsto_nhds_of_tendsto_nhdsWithin hp.physical).comp hφ
    let v:= vector (-step a); have ht:=(((Ortho.motion (Signed.reflect a)).continuous.tendsto _).comp h).add (h'.smul_const v); rw [zero_smul,add_zero] at ht; refine ht.congr (fun i=>?_)
    change Ortho.motion s.ortho (digit (A i) _) + A i • v=digit (A i) (s.act _+ _); rw [digit_plus]; congr 1; unfold digit; rw [map_smul,Canvas.motion_site]
end Strip
end YM.Massive.Tarn.Choir
#print axioms YM.Massive.Tarn.Choir.aheadV
#print axioms YM.Massive.Tarn.Choir.Strip.rayT
#print axioms YM.Massive.Tarn.Choir.Strip.thrum
