import YM.Vern.Chunk
set_option autoImplicit false
set_option maxHeartbeats 740000
noncomputable section
namespace YM.Vern
open Function Set Filter Analysis MeasureTheory Lattice QCD QCD.Lat QCD.Grass
open Massive Massive.UV Massive.Tarn Massive.Tarn.Choir Massive.Tarn.Choir.Strip Massive.Patria.Gall.Onyx
open Massive.Tarn.ChargeQ Massive.Poised.Plans.Stamp.Stair Massive.Gust
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix InnerProductSpace
open Sprig Intag.Sprig UV.Free Massive.Poised.Plans.Stamp Heron Iceberg Lobo
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K}{d:ℕ}
variable {φ:ℕ→ℕ}(hf:Foil P K T)(HQ:K.Harmony P φ)(E:Canopy P φ K)(X:Lanterns T E)
variable (V:Axis× Axis→ K.W)(hV: Persona T V)(J:Axle K (fun a b=>V (a,b))) (B:Vane J)
variable (r:ℝ)(hr:0<r)(s:ℝ)
variable (Y:Tri→ Module.End ℂ (Free.Symbol d))(f:ℕ→ℕ)(h:Tendsto f atTop atTop)
include hf HQ hV
variable (hd:8≤d)
variable (H:∀ (u:Free.Symbol d)(i:Tri),Tendsto (fun k=>(s:ℂ) • steel V E X J hd (Omega i) (f k) u) atTop (𝓝 (Y i u)))
include H
set_option quotPrecheck false
local notation "F_" d:arg=> ↥(seedP T d)
local notation "W_" d:arg=> ↥(seatP d)
local notation "Q" i:arg=> (s:ℂ) • jRoad hf HQ V hV J (Omega i) hd
local notation "B☆" k:arg=>simV E X k d
lemma realC (x:W_ d)(i:Tri): Tendsto (fun k=> ((simV E X (f k) d).symm (( (s:ℂ) • jRoad hf HQ V hV J (Omega i) hd) (simV E X (f k) d x))).val) atTop (𝓝 (Y i x.val)):=by
     have ht:= H x.val i; apply ht.congr'; refine Eventually.of_forall fun k=>?_ ; simp only[LinearMap.smul_apply,map_smul]; change _=(s:ℂ) • ((X.frame (f k) d).symm _); rfl
lemma spout : ∃ Z:Tri→Module.End ℂ (seatP d),(∀ u i,(Z i u).val= Y i u.val)∧ ∀ (i:Tri)(x:seatP d), Tendsto (fun k=> (simV E X (f k) d).symm (((s:ℂ) • jRoad hf HQ V hV J (Omega i) hd) (simV E X (f k) d x))) atTop (𝓝 (Z i x)):=by
      have h(u:W_ d)(i:Tri) := realC hf HQ E X V hV J s Y f hd H u i; have hv(i:Tri)(p:Free.Symbol d)(he:p∈ seatP d): Y i p∈ seatP d:=(seatP d).closed_of_finiteDimensional.mem_of_tendsto (h ⟨p,he⟩ i) (Eventually.of_forall fun k=> Subtype.prop _)
      let Z(i):= (Y i).restrict (hv i); refine ⟨Z,fun _ _=>rfl,fun i x=>?_⟩; exact tendsto_subtype_rng.mpr (h x i)
omit H hV
noncomputable def Gcup (d:ℕ): Tide ↥(seatP d):=by
     let F:=GStar hf HQ E X d; exact ⟨fun x y=> F.knot x.val y.val,fun _ _=> F.con ..,fun x hx=> F.positive _ (by intro h; exact hx (Subtype.ext h)), fun x y z=> F.add x.val y.val z.val,fun c x y=> F.sep c x.val y.val⟩
include hV H B h
lemma align:∃ (k:ℕ→ℕ)(F:ℕ→ W_ d≃ₗ[ℂ]F_ d)(Z:Tri→Module.End ℂ (seatP d)), StrictMono k∧ (∀ x,Tendsto (fun i=> (F i).symm (simV E X (f (k i)) d x)) atTop (𝓝 x)) ∧ (∀ u i,(Z i u).val= Y i u.val) ∧∀ x i n,(F n) (Z i x) = (((s:ℂ) • jRoad hf HQ V hV J (Omega i) hd)) (F n x) ∧ F n (shipR HQ E X d i x)= shipP HQ.h i d (F n x)∧∀ y,(Jcost hf HQ (E.B (f (k n))).r (E.B _).realH d).knot (F n x) (F n y)= (Gcup hf HQ E X d).knot x y:=by
    obtain ⟨Z,hZ,H⟩:=spout hf HQ E X V hV J s Y f hd H
    let S(i):= Jcost hf HQ (E.B (f i)).r (E.B _).realH d; let D(j:Tri):= (Q j); let P:Tri⊕ Tri→Module.End ℂ (seedP T d):= Sum.elim D fun i:Tri=> (shipP HQ.h i d).toLinearMap; let R:= shipR HQ E X d; let Q':Tri⊕Tri→Module.End ℂ (seatP d):= Sum.elim Z (fun i=> (R i).toLinearMap)
    have hh(i:Tri⊕Tri)(x:seatP d): Tendsto (fun k=>(simV E X (f k) d).symm (P i (simV E X (f k) d x))) atTop (𝓝 (Q' i x)):=by
            cases i with
            | inl i=> exact H i x
            | inr i=> apply tendsto_const_nhds.congr'; refine Eventually.of_forall fun n=>?_ ; change _= (_: W_ d); have he:=shire hf HQ E X (f n) d i x; change R i x=(simV E X (f n) d).symm (shipP HQ.h i d (simV E X (f n) d x)); rw [he,LinearEquiv.symm_apply_apply]
    have hz(i):∃ X,∀ k,Twin (S k) (P i) X:=by
           cases i with
           | inl i=>exact ⟨-(P (.inl i)),fun k=> pitG hf HQ V hV J B _ (E.B _).realH s hd i⟩
           | inr i=>exact ⟨(shipP HQ.h i d).symm.toLinearMap,fun k=>pitP hf HQ V hV J B _ _ i⟩
    obtain ⟨k,F,hk,ht₀,h1,hR,hE⟩:= tides S (Gcup hf HQ E X d) (fun i=> simV E X (f i) d) P Q' hz (fun i j=>(paths hf HQ E X j.val i.val).comp h) hh -- inspect syntax
    -- etc.
    exact ⟨k,F,Z,hk,h1,hZ,fun x i n=>⟨hE n (.inl i) x,hE n (.inr i) x, fun y=>hR x y n⟩⟩

end YM.Vern
#print axioms YM.Vern.align
