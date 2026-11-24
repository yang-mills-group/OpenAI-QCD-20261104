import YM.Bwana.Pits
import YM.Pods.Beaches
/- copy metabolism -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Shelv
open Function Filter Set QCD QCD.Lat QCD.Tide QCD.Revolve QCD.RP QCD.Grass Lattice Wilson Matrix
open Massive Massive.Patria Massive.Patria.Hub Massive.Patria.Depth Massive.Patria.Depth.Off Massive.Romance Massive.Chess
open YM.Next.Rank.Station Cells
open scoped Topology ComplexOrder BigOperators Matrix.Norms.L2Operator Classical
variable {S:Scheme}(R:Side){i j k n q N:ℕ} (hp:Even (S.side R j).val) (v: Site (S.side R k))(x: Cover) (hj:j≤ k) (hk:k≤ i)
local notation "Sn"=> S.side R
set_option quotPrecheck false
local notation "TL" h:arg=> Column.sky S R j _ h hp v
local notation "T₁"=> mural (viewW S R hj) hp v
local notation "TZ"=> Column.sky S R j i (hj.trans hk) hp v
local notation "I₀"=> Site (S.side R j)
local notation "V1"=> viewW S R hk
variable (w:TapeWalk (S.side R k) (mural (viewW S R hj) hp v))(t:Site (S.side R j))
open Cylinder Exposure Massive.Poised Massive.Poised.Plans
-- covariant expression on stack offsets. TILE marker hom & Awe. Anti under composition preserved.
local notation "Aδ" p:arg a:arg=> ratioTo S i k • Lattice.lift (((T₁).bandCut p a).slide)
local notation "ΩΦ"=> Insertion (Sn i) 6
variable (X:TapeWalk (S.side R k) (mural (viewW S R hj) hp v)→ Insertion (S.side R i) 6)
variable (p:Bool)
structure ShapeC (p:Bool):Prop where
     moves (w:TapeWalk (S.side R k) (mural (viewW S R hj) hp v))(t:Site (S.side R j))(a:Axis): march (ratioTo S i k • Lattice.lift (((T₁).bandCut t a).slide)) (Action.adj a ⇑(X w))= ⇑(X ((t,a)::w))
     grade : ∀ w V, QCD.Grass.Hom p (X w V)
set_option synthInstance.maxHeartbeats 90000
set_option maxHeartbeats 500000
variable (b:ℕ→ Cover)
abbrev pens (K:Bore q)(sym: UV.RawSym)(u:UV.Label q): Insertion (S.side R i) 6:= K (S.side R i) (arks R hp v hj w b i) (Hub.spine sym u (axes (pathT T₁ w)))
lemma baseK(K:Bore q)(sym:UV.RawSym)(u:UV.Label q): pens R hp v hj [] b (i:=i) K sym u= K (Sn i) (b i) u:=by unfold pens; rw[show arks R hp v hj [] b i=b i from ?_]; rfl; unfold arks lineC axes pathT layX; simp [sawC]
lemma picks (K:Bore q)(sym:UV.RawSym)(hK: Rubric sym K)(u:UV.Label q)(he: moored u.val p): ShapeC R hp v hj (fun w=> pens R hp v hj w b (i:=i) K sym u) p:=by
       have hl(l:List Axis):moored (Hub.spine sym u l).val p:=by induction l with|nil=> exact he| cons a l ih=> exact durable _ _ _ ih a
       refine ⟨fun t c a=> ?_,fun v V=> fade K sym hK (Hub.spine sym u (axes (pathT T₁ v))) p (hl _) _ _⟩
       unfold pens; rw[hK.eye (Sn i),hK.advances]; have hz : arks R hp v hj ((c,a)::t) b i=(Signed.mirror a).act (arks R hp v hj t b i) + (Aδ c a):=by unfold arks lineC; change (Signed.mirror a).act _ +ratioTo S i k • ((Signed.mirror a).act _+_) = _; rw [Signed.act_add,act_times, smul_add,← add_assoc]; -- rfl
       rw [hz]; rfl
namespace ShapeC
variable {X p}(Z:TapeWalk (S.side R k) (mural (viewW S R hj) hp v)→ Insertion (S.side R i) 6)
variable (hx: ShapeC R hp v hj X p)(hy:ShapeC R hp v hj Z p)
include hx hy
lemma sub: ShapeC R hp v hj (X-Z) p:=by
       constructor
       · intro t c a; funext V; let b₁:= Aδ c a; let G:= TorusPCAC.Geometry.crank 1 1 (wrap _ b₁) (TorusPCAC.Geometry.heat (n:=Sn i) b₁) (N:=6)
         have hp':Action.adj a (X t-Z t)=Action.adj a (X t)-Action.adj a (Z t):=by funext i; rw [Pi.sub_apply,eye_value,eye_value,eye_value,show ∀ v,(X t-Z t) v=X t v-Z t v from fun _=>rfl, map_sub]
         change march b₁ (Action.adj a (X t-Z t)) V=_; rw[hp']; exact (map_sub G _ _).trans (congr_arg₂ Sub.sub (congr_fun (hx.moves t c a) V) (congr_fun (hy.moves t c a) V)) -- needs An explicit coe.Work.
       intro t V; change QCD.Grass.Hom p (X t V-Z t V); rw[sub_eq_add_neg,← neg_one_smul ℂ]; exact QCD.Grass.Hom.add (hx.grade _ _) (QCD.Grass.Hom.smul (hy.grade _ _) _)
omit hy
lemma scale (s:ℝ) : ShapeC R hp v hj ((s:ℂ) • X) p:=by
       refine ⟨fun t c a=>?_,fun t V=> QCD.Grass.Hom.smul (hx.grade _ _) _⟩
       have he: Action.adj a ((s:ℂ) • X t) = (s:ℂ) • Action.adj a (X t):=by funext V; rw [eye_value, show ∀ V:Grid (Sn i), ((s:ℂ) • X t) V= (s:ℂ) • X t V from fun _=>rfl, map_smulₛₗ, Complex.conj_ofReal,Pi.smul_apply,eye_value] -- issue parser coe
       funext V; let b₁:= Aδ c a; let G:= TorusPCAC.Geometry.crank 1 1 (wrap _ b₁) (TorusPCAC.Geometry.heat (n:=Sn i) b₁) (N:=6); change march b₁ (Action.adj a ((s:ℂ) • X t)) V=_; rw [he]; exact (map_smul G.toLinearMap ..).trans (congr_arg ((s:ℂ) • ·) (congr_fun (hx.moves t c a) V))
-- want X tx punct (odd/...), Z T even. `(X*Z)` can reflect as X*Z. Use RIGHT of mirror after, Z target even.
lemma outer (hz:ShapeC R hp v hj Z false) : ShapeC R hp v hj (X*Z) p:=by
       refine ⟨fun t c a=> ?_,fun t V=> ?_⟩
       · funext V; let b₁:= Aδ c a; let G:= TorusPCAC.Geometry.crank 1 1 (wrap _ b₁) (TorusPCAC.Geometry.heat (n:=Sn i) b₁) (N:=6)
         have hp':Action.adj a (X t*Z t)=Action.adj a (Z t)*Action.adj a (X t):=by funext i; rw [Pi.mul_apply,eye_value,eye_value,eye_value,show ∀ v,(X t*Z t) v=X t v*Z t v from fun _=>rfl,tilt_mul]
         change march b₁ (Action.adj a (X t*Z t)) V= X ((c,a)::t) V*Z ((c,a)::t) V; rw [hp']
         refine (map_mul G _ _).trans ((congr_arg₂ HMul.hMul (congr_fun (hz.moves t c a) V) (congr_fun (hx.moves t c a) V)).trans ((hz.grade ((c,a)::t) V : Plus _).central (X ((c,a)::t) V)).symm.eq)
       have ht:= QCD.Grass.Hom.mul (hx.grade t V) (hz.grade t V); change QCD.Grass.Hom p (X t V* Z t V); simpa only [Bool.xor_false] using ht
-- pay price
include hk
variable (A:Massive.Regulator (S.side R i) 6)(ha:A.t=0)
include ha
lemma dots : SignedEq (reels A.zeroCut (pathT TZ w) (X [])) (X w):=by
       induction w with
       | nil=> rfl -- SignedEq ope?
       | cons a t ih=>
         rcases a with ⟨c,a⟩; have hZ:= pic_match A ((TZ).bandCut c a) (Aδ c a) ((slide R hp v hj hk c a).symm) rfl (X t) ha p (hx.grade _)
         rw [show ((TZ).bandCut c a).pos=a from rfl,show march _ _= _ from hx.moves t c a] at hZ; let wν:=((TZ).bandCut c a)
         have ht:SignedEq (QCD.RP.picture wν A.zeroCut (X t)) (X ((c,a)::t)):=by rcases hZ with h|h; exact Or.inl (ContinuousMap.ext (congr_fun h)); exact Or.inr (ContinuousMap.ext (congr_fun h))
         refine SignedEq.trans ?_ ht; change SignedEq (picture wν A.zeroCut (reels A.zeroCut (pathT TZ t) (X []))) _; rcases ih with h|h; · rw [(show reels A.zeroCut _ _ =_ from h)] -- SignedEq refl simp?
         apply Or.inr
         rw [(show reels A.zeroCut _ _ = _ from h)]
         exact negatePic ..
lemma priceV(t':Site (S.side R j))(h:finish (mural (viewW S R hj) hp v) t w=t'): SignedEq (replicateR TZ A (X []) t t') (X w):=by
       exact SignedEq.trans (SignedEq.symm (along TZ A.zeroCut (X []) w t t' ⟨p,hx.grade _⟩ ha rfl ((finishK R hp v hj hk w t).trans h))) (dots R hp v hj hk w hx A ha)
end ShapeC
end YM.Intag.Shelv
#print axioms YM.Intag.Shelv.ShapeC.priceV
#print axioms YM.Intag.Shelv.ShapeC.scale
#print axioms YM.Intag.Shelv.ShapeC.outer
#print axioms YM.Intag.Shelv.ShapeC.sub
#print axioms YM.Intag.Shelv.picks
