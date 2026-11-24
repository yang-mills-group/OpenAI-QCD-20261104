import YM.Sprig.Helen
/-! Deal with the exact kernel equivalences; no guesses via counting alone. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Sprig.Canopy
open Function Filter Set Matrix Finset MeasureTheory
open Massive QCD QCD.Lat Lattice Cylinder Patria Patria.Depth Massive.Tarn UV UV.Free
open _root_.YM.Fir Massive.Fir Choir Pollens HarmonyF
open scoped BigOperators Topology InnerProductSpace Classical Matrix ComplexOrder
variable {C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}{Q:Choir}{d:ℕ}(T: Pollens P Q)(E: Canopy P φ Q)
open Compass
variable {β e:ℝ}(hc:C.Path β e)(hφ:Tendsto φ atTop atTop)(hP:P.System)(hQ:Q.Harmony P φ)(hv:Foil P Q T)
variable (x y: Label d)(i:Points 2)(hi:i∈conf 2)(p:EuPin)(s:Signed)(ht:p.Lifts s)
-- algebra subspace.Fill on valid. Precise invisibility with both.
lemma vanishing (hx:projection x =0): (∀ i:Points 2,i∈conf 2→∀ y:Label d,readK i y x=0∧readK i x y=0):=by
     have he' : projection x=projection (0:Label d):=by rw [map_zero,hx]
     intro i hi y; let f:= wick (fun _ : Fin 2=>d) i
     refine ⟨?_,?_⟩
     · exact Eq.trans (DawnS.trails (u:=fun _ : Fin 2=>d) _ hi (![y,x]) (![y,0]) (fun v=>by fin_cases v; exact rfl; exact he')) (MultilinearMap.map_coord_zero (i:=(1: Fin 2)) _ rfl)
     exact Eq.trans (DawnS.trails (u:=fun _ : Fin 2=>d) _ hi (![x,y]) (![0,y]) (fun v=>by fin_cases v; exact he'; exact rfl)) (MultilinearMap.map_coord_zero (i:=(0: Fin 2)) _ rfl)
include P
lemma fertile (h:∀ i:Points 2,i∈conf 2→∀ y:Label d,readK i y x=0): projection x=0:=by
     by_contra hp; have hY:= DawnS.detecting 1 zero_lt_one x P.sym hp; let i :Points 2:= points (![0,(1:ℝ) • basis timeAxis]); have hh: i∈conf 2:= DawnS.distinct 1 zero_lt_one; specialize h i hh (P.sym.adj d timeAxis x); exact hY.ne' h -- implicit z
include hQ hv
open LinearMap
lemma convoy (Y:Label d≃ₗ[ℂ]Label d)(A:Ortho)(S:Q.W≃ₗ[ℂ]Q.W)(h:∀ᶠ k in atTop,∀ x:Label d,E.cut k (Y x)=S (E.cut k x))(H:∀ (i:Points 2),i∈conf 2→∀ v,Q.total 2 (Points.move A i) (S ∘v)=Q.total 2 i v): projection (Y x)=0 ↔ projection x=0:=by
     constructor
     · intro hu; apply fertile (P:=P); intro i hi y
       rw [← readMap T E hQ hv y x i hi Y A S h H]; exact (vanishing (Y x) hu (Points.move A i) (show Points.move A i∈conf 2 from fun p q he=> hi (Ortho.move_injective _ he)) (Y y)).1
     intro hu; apply fertile (P:=P); intro i hi y; let p:= Points.move A⁻¹ i; have hz: Points.move A p=i := PiLp.ext fun j=> Ortho.move_inv ..; have he:p∈conf 2:=fun i j h=>hi (Ortho.move_injective _ h)
     obtain ⟨w,h₁⟩:= Y.surjective y; rw [←h₁,←hz, readMap T E hQ hv w x p he Y A S h H]; exact (vanishing x hu p he w).1
variable (u: FlavorTorus)
include E
lemma rotateP (hq:p.Lifts s):projection (P.sym.pin d p x)=0 ↔projection x=0:= convoy T E hQ hv x _ p.coord (T.spin p) ((cut_pin (d:=d) T E).mono fun i hi x=>hi x p s hq) (fun i h=> hv.discrete _ i h _ _ hq)
lemma flavorV :projection (P.sym.flavor d u x)=0 ↔ projection x=0:= convoy T E hQ hv x _ 1 (T.flavor u) ((cut_flavor (d:=d) T E).mono fun i hi x=>hi x u) (fun i h z=>by rw[show Points.move 1 i=i from PiLp.ext fun j=> Ortho.move_one ..]; exact hv.flavor 2 i h u z)
lemma chargeV :projection (P.sym.charge d x)=0 ↔ projection x=0:= convoy T E hQ hv x _ 1 T.charge (cut_charge T E) (fun i h z=>by rw[show Points.move 1 i=i from PiLp.ext fun j=> Ortho.move_one ..]; exact hv.charge 2 i h z)
lemma parityV : projection (P.sym.parity d x)=0 ↔ projection x=0:= convoy T E hQ hv x _ 1 T.parity (cut_parity T E) (fun i h z=>by rw[show Points.move 1 i=i from PiLp.ext fun j=> Ortho.move_one ..]; exact hv.parity 2 i h z)
-- dagger relation.Shape.
include hc hφ hP
lemma adornV (a:Axis):projection (P.sym.adj d a x)=0 ↔ projection x=0:=by
    let F:=P.sym.adj d a; have hp(x:Label d): projection x=0 → projection (P.sym.adj d a x)=0:=by
          intro h; apply fertile (P:=P); intro i hi y; obtain ⟨w,yEq⟩:= F.surjective y; rw [← yEq]; obtain ⟨z,hz,rfl⟩:= Choir.affined (Signed.reflect a) Fin.revPerm i hi; change readK (tilted a z) (F w) (F x)=0; unfold F; rw [oppositeK T E hc hφ hP hQ hv x w z hz a,(vanishing x h _ hz w).2,star_zero]
    refine ⟨fun h=> ?_,hp _⟩; have he:F (F x)=x:=Subtype.ext (by unfold F; rw[P.sym.adjActs,P.sym.adjActs]; exact UV.eyeTwist a x.val); exact he ▸ hp (F x) h
-- visible unit.Measured only.
lemma unitV : projection (P.sym.unit d)≠0:=by
     let x:= P.sym.unit d; intro h; let p:= points (![0,(1:ℝ) • basis timeAxis]); have hp:p∈conf 2:= DawnS.distinct 1 zero_lt_one; have hh:= (vanishing x h p hp x).1; have hT:= bonus E hQ x x p hp
     rw[hh] at hT; apply one_ne_zero (α:=ℂ); apply tendsto_nhds_unique _ hT -- wrong orientation witness: limit1 vs 0.
     refine tendsto_const_nhds.congr' (EventuallyEq.symm ?_); filter_upwards [cut_unit (d:=d) E] with i hi
     change Q.total 2 _ ![cut E i x,cut E i x]=1; rw [show cut E i x=lampU P Q from hi.trans (hv.unit d none)]; let y:Points 2:= (E.B i).r • p; have hs:y∈ conf 2:= vital P φ Q hQ p hp _ (E.B i).realH; let f:=lampU P Q
     have hb : Q.total 2 y ![f,f]=Q.total 1 (Points.tail y) ![f]:= hv.functor 1 y hs _
     change Q.total 2 y _ = _; rw [hb,show Q.total 1 (Points.tail y) ![f]=Q.total 0 0 0 from ?_, hv.empty]; have hp:= hv.functor 0 (Points.tail y) (Points.tail_in hs) Matrix.vecEmpty; rw[show Matrix.vecEmpty (α:=Q.W)=0 from Subsingleton.elim ..,show Points.tail (Points.tail y)=0 from Subsingleton.elim ..] at hp; convert hp
     funext j; fin_cases j; rfl
end YM.Intag.Sprig.Canopy
#print axioms YM.Intag.Sprig.Canopy.parityV
#print axioms YM.Intag.Sprig.Canopy.rotateP
#print axioms YM.Intag.Sprig.Canopy.adornV
