import YM.Vern.Kerf
import YM.Vern.Gloss
import YM.Vern.Iota
import YM.Vern.Road
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Vern
open Function Set Filter Analysis MeasureTheory Lattice QCD QCD.Lat QCD.Grass
open Massive Massive.UV Massive.Tarn Massive.Tarn.Choir Massive.Tarn.Choir.Strip Massive.Patria.Gall.Onyx
open Massive.Tarn.ChargeQ Massive.Poised.Plans.Stamp.Stair Massive.Gust
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix InnerProductSpace
open Sprig Intag.Sprig UV.Free Massive.Poised.Plans.Stamp Heron Iceberg Lobo
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K}(G:K.Domestic){d:ℕ}
variable {φ:ℕ→ℕ}(hf:Foil P K T)(HQ:K.Harmony P φ)(E:Canopy P φ K)(X:Lanterns T E)
variable (V:Axis× Axis→ K.W)(hV: Persona T V)(J:Axle K (fun a b=>V (a,b))) (B:Vane J)
variable (r:ℝ)(hr:0<r)(s:ℝ)(g:Ortho.Skew)
set_option quotPrecheck false
local notation "F_" d:arg=> ↥(seedP T d)
local notation "W_" d:arg=> ↥(seatP d)
include hf HQ
variable (hd:8≤d)
noncomputable def jRoad :Module.End ℂ (seedP T d):=by
     refine (tapeJ K V J hd g).restrict (fun v hv=>?_)
     let x:= (v:K.W); change v∈ seedP T d at hv; have he:(x:K.W) ∈ safeV T:= hv; refine ⟨?_,fun p=>?_⟩
     · change T.parity _= _; exact Eq.trans (Gust.Axle.colors HQ.h hf V hV J x g).symm (congr_arg _ he.1)
     exact Eq.trans (halo hf (T.flavor p) x (fun n x H=>hf.flavor _ x H p) V hV J g (hV.tense.flux p)) (congr_arg (J.jet g) (he.2 p))
-- ship U_i already. fixed free boost.W.X. signed formula permits transfer
noncomputable def shipR (d:ℕ)(i:Tri): (seatP d)≃ₗ[ℂ](seatP d) := ((simV E X 0 d).trans (shipP HQ.h i d)).trans (simV E X 0 d).symm
#check shipR
#check jRoad
lemma cors (i:Tri) (u:W_ d)(p:Label d)(ht:u.val= projection p): (shipR HQ E X d i u).val= projection (P.sym.pin _ (SpinQ i) p):=by
      let F:=simV E X 0 d; let W:= X.frame 0 d; apply W.injective; apply Subtype.ext; change (F ((shipR HQ E X d i) u)).val.val= _; rw[← (X.leaders 0 d).rotates p _ _ (fL i)]; unfold shipR; change (F (F.symm _)).val.val=_; rw [F.apply_symm_apply]; change (shipP HQ.h i d (F u)).val.val=_; rw[sails]; exact congr_arg (T.spin _) (congr_arg (fun x=>(W x).val) ht)
lemma shire (k d:ℕ)(j:Tri)(u:seatP d): shipP HQ.h j _ (simV E X k d u)= simV E X k d (shipR HQ E X d j u):=by
      apply Subtype.ext; apply Subtype.ext; rw[sails]; let W:= X.frame k d; obtain ⟨v,h⟩:= Free.onto u.val; change T.spin _ (W u.val).val= (W _).val; rw [cors hf HQ E X j u v h.symm, ← h]; exact (X.leaders k d).rotates v (SpinQ j) _ (fL j)
include hV B hr
noncomputable def Jcost(d:ℕ): Tide ↥(seedP T d):=by
      let F:=entryQ hf HQ timeAxis r hr d
      exact ⟨fun x y=> F.knot x.val y.val,fun _ _=>F.con _ _,fun x hx=> F.positive _ (by intro h; exact hx (Subtype.ext h)), fun x y z=>F.add x.val y.val z.val,fun c x y=> F.sep c x.val y.val⟩
lemma pitG(i:Tri): Twin (Jcost hf HQ r hr d) ((s:ℂ) • jRoad hf HQ V hV J (Omega i) hd) (-((s:ℂ) • jRoad hf HQ V hV J (Omega i) hd)):=by -- want scale s binder
      let F:= Jcost hf HQ r hr d; let X:= jRoad hf HQ V hV J (Omega i) hd; intro x y; change F.knot ((s:ℂ) • X x) y= F.knot _ (-((s:ℂ) • X y)); rw [F.seals, Complex.star_def,Complex.conj_ofReal,show F.knot (X x) y= -F.knot x (X y) from ?_]
      · change _= F.zz _ _; rw [map_neg, map_smul,mul_neg]; rfl
      exact pinnacle hf HQ V hV J B hd (lieu (backK i)) (lieu (edgeK i)) timeAxis (fun h=> Fin.castSucc_ne_last _ h) (fun h=>Fin.castSucc_ne_last _ h) r hr x.val y.val
lemma pitP(i: Tri): Twin (Jcost hf HQ r hr d) (shipP (T:=T) HQ.h i d).toLinearMap (shipP HQ.h i d).symm.toLinearMap:=by
     intro x y; let B:= shipP (T:=T) HQ.h i d; obtain ⟨y,rfl⟩:= B.surjective y; change (Jcost hf HQ r hr d).knot (B x) (B y)= (Jcost hf HQ r hr d).knot _ (B.symm (B y)); rw[B.symm_apply_apply]; unfold B; change turf timeAxis r (T:=T) _ _= _; rw[sails,sails]; exact tips hf HQ i r hr _ _ x.property.1
end YM.Vern
#print axioms YM.Vern.jRoad
#print axioms YM.Vern.pitP
#print axioms YM.Vern.shire
#print axioms YM.Vern.pitG
