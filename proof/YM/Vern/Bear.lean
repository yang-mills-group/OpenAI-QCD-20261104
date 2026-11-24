import YM.Vern.Joe
set_option autoImplicit false
noncomputable section
namespace YM.Vern
open Function Set Filter Analysis MeasureTheory Lattice QCD QCD.Lat
open Massive Massive.UV Massive.Tarn Massive.Tarn.Choir Massive.Tarn.Choir.Strip Massive.Patria.Gall.Onyx
open Massive.Tarn.ChargeQ Massive.Poised.Plans.Stamp.Stair Massive.Gust
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix InnerProductSpace
open Sprig Intag.Sprig UV.Free Massive.Poised.Plans.Stamp Heron Iceberg Lobo
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K}{d:ℕ}
variable {φ:ℕ→ℕ}(hf:Foil P K T)(HQ:K.Harmony P φ)(E:Canopy P φ K)(X:Lanterns T E)
variable (V:Axis× Axis→ K.W)(hV: Persona T V)(J:Axle K (fun a b=>V (a,b))) (B:Vane J)
variable (hd:8≤d)
variable (s:ℝ)(z:IceT→ℝ)
noncomputable def geared (d:ℕ) : Qa d →ₗ[ℂ] seatP d:=
    ((projection (d:=d)).comp (Qa d).subtype).codRestrict _ (fun x => ⟨x.val,x.property,rfl⟩) -- range ≠ defeq map? fix
lemma gained : Surjective (geared d):=by
     intro v; obtain ⟨p,hp,h⟩:=v.property; exact ⟨⟨p,hp⟩,Subtype.ext h⟩
include hf hV
variable (Y:Tri→Module.End ℂ ↥(seatP d))(hE:∀ u i,(Y i u).val= (omegaQ i z d) u.val)
variable (F:↥(seatP d)≃ₗ[ℂ] ↥(seedP T d))
def Feasible :Prop:= (∀ u i,(Y i u).val=(omegaQ i z d) u.val) ∧ ∀ i x, F (Y i x)= (((s:ℂ) • jRoad hf HQ V hV J (Omega i) hd)) (F x) ∧ F (shipR HQ E X d i x)= shipP HQ.h i d (F x)
variable (A:Feasible hf HQ E X V hV J hd s z Y F)
include A
set_option quotPrecheck false
local notation "l" i:arg=> ((s:ℂ) • jRoad hf HQ V hV J (Omega i) hd)
lemma gramH (i:Tri)(u v:↥(seatP d))(he : omegaQ i z d u.val=v.val): (((s:ℂ) • jRoad hf HQ V hV J (Omega i) hd)) (F u)= F v:=by rw [←(A.2 i u).1]; exact congr_arg F (Subtype.ext ((A.1 u i).trans he))
lemma spinH (i:Tri)(u v:seatP d)(p:Label d)(hp:u.val=projection p)(he:v.val=projection (P.sym.pin d (SpinQ i) p)): shipP HQ.h i d (F u)= F v:=by rw[←(A.2 i u).2]; exact congr_arg F (Subtype.ext ((cors hf HQ E X _ _ _ hp).trans he.symm))
lemma soils {a:IceT}{p:Label d}(h:Lone a p)(u: ↥(seatP d))(hx:u.val=projection p)(s':Hail.RightAuth P.sym)(i:Tri): shipP HQ.h i d (F u)=F u ∧ (l i) (F u)=0:=by
     refine ⟨spinH hf HQ E X V hV J hd s z Y F A _ _ _ _ hx (by rw[asL i a _ P.sym h]; exact hx),?_⟩
     rw[gramH hf HQ E X V hV J hd s z Y F A i u 0, map_zero]; rw[hx]; exact atL i a _ P.sym s' z h
lemma spill {a:IceT}{p:Tri→ Label d}(h:Brook a p)(u:Tri→↥(seatP d))(hx:∀ i,(u i).val=projection (p i))(s':Hail.RightAuth P.sym)(i j:Tri):
      shipP HQ.h i d (F (u j))=(charI i j:ℂ) • F (u (roof i j)) ∧ (l i) (F (u j))=(z a:ℂ) • drive i (fun i=>F (u i)) j:=by
      have D : (l i) (F (u j)) = F ((z a:ℂ) • drive i u j):= gramH hf HQ E X V hV J hd s z Y F A i _ _ (by rw[hx,atB i j a p P.sym s' z h,Submodule.coe_smul]; unfold drive; simp only[comp_apply,AddSubmonoidClass.coe_finsetSum,Submodule.coe_smul,hx])
      rw[D, map_smul]; have hv: drive i (fun i=>F (u i)) j= F (drive i u j):=by unfold drive; simp only [map_sum,map_smul]
      refine ⟨?_,by rw[hv]⟩
      rw [← map_smul]; exact spinH hf HQ E X V hV J hd s z Y F A _ _ _ (p j) (hx _) (by rw [Submodule.coe_smul,asB i j a _ P.sym h,map_smul,hx])
lemma sprout {a:IceT}{p:Tri→Tri→ Label d}(h:BraceP a p)(u:Tri→ Tri→↥(seatP d))(hx:∀ i j,(u i j).val=projection (p i j))(s':Hail.RightAuth P.sym)(i j k: Tri): shipP HQ.h i d (F (u j k)) = (charI i j:ℂ) • ((charI i k:ℂ) • F (u (roof i j) (roof i k))) ∧ (l i) (F (u j k))= (z a:ℂ) • (drive i (fun p=>F (u p k)) j+drive i (fun p=> F (u j p)) k):=by
      constructor
      · rw [← map_smul, ← map_smul]; exact spinH hf HQ E X V hV J hd s z Y F A _ _ _ (p j k) (hx _ _) (by rw [Submodule.coe_smul,Submodule.coe_smul,hx,asS i j k a _ P.sym h,map_smul,map_smul])
      have he: (l i) (F (u j k))= F ((z a:ℂ) • (drive i (fun p=>u p k) j + drive i (u j) k)):= gramH hf HQ E X V hV J hd s z Y F A _ _ _ (by rw [hx,atS i j k a p P.sym s' z h, Submodule.coe_smul,Submodule.coe_add]; unfold drive; simp only [comp_apply,AddSubmonoidClass.coe_finsetSum,Submodule.coe_smul,hx]); rw[he,map_smul,map_add]; unfold drive; simp only [map_sum,map_smul]
end YM.Vern
#print axioms YM.Vern.sprout
#print axioms YM.Vern.soils
#print axioms YM.Vern.spill
#print axioms YM.Vern.gained
