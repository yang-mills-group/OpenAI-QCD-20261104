import YM.Mako.Cameo
import YM.Mako.Melon
set_option maxHeartbeats 700000
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Set Function Filter Analysis Lattice QCD QCD.Lat
open Massive Massive.UV Massive.UV.Free Massive.Gust Massive.Tarn Massive.Tarn.Choir
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open Heron Iceberg Intag.Sprig Sprig Vern MassiveTwoEstimates
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}{K:Choir}{T:Pollens P K}{d:ℕ}
variable {E:Canopy P φ K}{X:Lanterns T E}{W:Axis×Axis→ K.W} {A: Axle K (fun a b=>W (a,b))}{I:ℕ→ℕ} (J:Glacier T E X W A I)(H:Foil P K T)(JQ:K.Harmony P φ)(B:Vane A)(R: Roof P.sym)(hd:8 ≤ d)
set_option quotPrecheck false
local notation "Wd" => K.level d
local notation "Ω"=> Free.Symbol d
local notation "Λ"=> tapeJ K W A hd
open Org
lemma flood (s:Signed) : Surjective (Org.orients s):=by
     let k:=s.ortho; intro i; refine ⟨conjSkew k⁻¹ i,Subtype.ext ?_⟩; let V:=k.val; have hi: V*star V=1:= k.property.2; show V*(star V * i.val*star (star V))*star V=i.val; rw[star_star, show V*(star V * i.val*V)*star V=(V*star V)*i.val*(V*star V) from by simp only [mul_assoc],hi,mul_one,one_mul]
include J H
lemma halo_pin (s:Signed)(p:EuPin)(hs:p.Lifts s)(q:Ortho.Skew)(w:K.W): T.spin p (A.jet q w)= A.jet (Org.orients s q) (T.spin p w):= (Gust.liven W H A J.n s p hs q w).symm
include JQ R -- H needed ↑
variable (m:Module.End ℂ (Free.Symbol d →ₗ[ℂ] ↥(K.level d)))
lemma install (h:Split m (range fun i=> power (rain i d) (Λ i)))(i:ℕ)(u:Ω≃ₗ[ℂ] ↥(K.level d))(hu:u.toLinearMap=m (X.frame (I i) d).toLinearMap): Prose u T:=by
     have hh(x:Ω):u x=m (X.frame (I i) d).toLinearMap x:= DFunLike.congr_fun hu x
     refine ⟨fun x s k hw=>?_,fun x p=>?_,fun x=>?_,fun x=>?_,fun x a=>?_,?_⟩
     · rw[hh,hh]; exact approvals J hd m h (P.sym.pin d s) (T.spin s) (show Continuous (RingHom.id ℂ) from continuous_id) (fun i j=> (X.leaders i d).rotates j s k hw) (Org.orients k) (flood k) (halo_pin J H k s hw) i x
     · rw[hh,hh]; exact approvals J hd m h (P.sym.flavor d p) (T.flavor p) (show Continuous (RingHom.id ℂ) from continuous_id) (fun i j=>(X.leaders i d).turns j p) id surjective_id (fun y v=>halo H _ v (fun n x hx u=> H.flavor n x hx p u) W J.n A y (fun j=>J.n.tense.flux p j)) i x
     · rw[hh,hh]; exact approvals J hd m h (P.sym.charge d) T.charge (show Continuous (RingHom.id ℂ) from continuous_id) (fun i j=>(X.leaders i d).jumps j) id surjective_id (fun y v=> halo H _ v H.charge W J.n A y J.n.tense.charge) i x
     · rw[hh,hh]; exact approvals J hd m h (P.sym.parity d) T.parity (show Continuous (RingHom.id ℂ) from continuous_id) (fun i j=>(X.leaders i d).spins j) id surjective_id (fun y v=> halo H _ v H.parity W J.n A y J.n.tense.parity) i x
     · rw[hh,hh]; let k:= Signed.mirror a; refine approvals J hd m h _ (T.adj a) continuous_star (fun i j=>(X.leaders i d).reflects j a) (Org.orients k) (flood k) ?_ i x
       intro p v; rw [←steal T JQ.h a (A.jet p v),←steal T JQ.h a v, ← axle_Ch JQ.h H W J.n A p a v]; exact halo_pin J H k _ (couture _) _ _
     rw [hh]; let Y:= X.frame (I i) d; let Q:= projection (P.sym.unit d); have hv:(Y Q).val=lampU P K:= (X.leaders _ _).unit
     rw[show m Y.toLinearMap Q=Y Q from ?_]; exact hv
     refine recode (fun i=>rain i d) (Λ) Y.toLinearMap m Q (fun i=> fcore i R) (fun p=>Subtype.ext ?_) h.budget; change A.jet p (Y Q).val=0; rw[hv,tapsX J H JQ.h]
structure Flyers (A:Axle K (fun a b=>W (a,b)))(d:ℕ)(hd:8≤d)(T:Pollens P K) (u:Free.Symbol d ≃ₗ[ℂ] ↥(K.level d)):Prop extends Prose u T where
     revenue(g:Ortho.Skew)(v:Free.Symbol d) : u (rain g d v)= tapeJ K W A hd g (u v)
include B
lemma mints : ∃ u:ℕ→Free.Symbol d≃ₗ[ℂ] ↥(K.level d),(∀ k, Flyers A d hd T (u k))∧∀ v:Free.Symbol d,Tendsto (fun i=>(X.frame (I i) d).symm (u i v)) atTop (𝓝 v):=by
     obtain ⟨m,hm⟩:= appoint J H JQ B R hd; let L(k):=X.frame (I k) d; let F(k):=m (L k).toLinearMap; have hP:Pace L F 1:= pulse L _ _ (vacation J hd) m hm.budget
     obtain ⟨n,hn⟩:= eventually_atTop.mp (earns_h L F hP)
     let u(k):= LinearEquiv.ofBijective (F (max n k)) (hn (max n k) (le_max_left ..)); refine ⟨u,fun k=> ?_,fun v=>?_⟩
     · refine { toProse:=install J H JQ R hd m hm (max n k) (u k) rfl
                revenue:= fun g x=> ?_ }
       have he: power (rain g d) (Λ g) * m =0:=hm.hit _ ⟨g,rfl⟩; have hh:= DFunLike.congr_fun (DFunLike.congr_fun he (L (max n k)).toLinearMap) x; exact (sub_eq_zero.mp hh).symm
     apply (hP v).congr'; filter_upwards[eventually_ge_atTop n] with i hi; change (L i).symm (_)= (L i).symm (F (max n i) v); rw[max_eq_right hi]
end YM.Mako
#print axioms YM.Mako.mints
