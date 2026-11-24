import YM.Kai.Stray
/-! Polar report at always. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.PCAC.Oren
open Function Filter MeasureTheory Set QCD QCD.Lat QCD.Grass Lattice Wilson UV RG QCD.Grass.Ward
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator Classical TensorProduct Kronecker
open Poised Poised.Beacon Poised.Plans Finset Module Poised.Stative Massive.Patria Patria.Exposure Depth Intag
open Entr Entr.Meridian Stew Cylinder
open QCD.Tide Revolve Onsite Tawny Tawny.Cast
variable {S:Scheme}{R c:Side}{d n i l j:ℕ}(A:Run S n R 6)(hA:A.Actual)
noncomputable def axle (q:Bool)(a:Flavor 6)(i:Axis):Slate:=⟨q,a,i,1,one_mul _⟩
variable (q:Bool)(a:Flavor 6)
local notation "L"=> axle q a
noncomputable def marque (j:Axis): Cover→Insertion (S.side R i) 6:= inkC (L j) A
include hA
lemma growth (hi:i≤ n): Roars (marque (i:=i) A q a):=by
     let p:= actor A i; have ht:= act A hA hi; rw[pier A hA hi] at ht
     have he : Action.charge (⇑p)=⇑p:=by rw [show (⇑p : Density _ 6) =_ from ht]; exact (Patria.Depth.arrives A i hi).2.2.2.1 -- coerce
     constructor
     · intro b j; rw [charge_west]; funext x; let y:= TorusPCAC.Stencil.conjGrid x; let v:= p y; let u:= wrap (S.side R i) j
       have ht:TorusPCAC.Stencil.charge _ v=p x:=by rw[charge_west] at he; exact congr_fun he x
       change TorusPCAC.Stencil.charge _ (Wagon (axle q a b) u y v)=Wagon (axle q a b) u x (p x); rw[← ht]; unfold Wagon axle; simp only [Complex.ofReal_one,one_smul]; split; exact (cStars ..).1; exact (cStars ..).2
     · intro b j u; have he : Action.flavor u (⇑p)= ⇑p:=by rw [show (⇑p:Density _ 6)=_ from ht]; exact (Patria.Depth.arrives A i hi).2.2.1 _
       rw [flavor_show] at he; rw [flavor_show]; funext x; let v:=p x; let z:=wrap (S.side R i) j; let Q:=TorusPCAC.Ward.acts (proclaim u) (S.side R i) -- R shadow Side fix
       have hx:Q v=v:= congr_fun he x
       change Q (Wagon (axle q a b) z x v)=Wagon (axle q a b) z x v; nth_rw 2[←hx]; unfold Wagon axle; simp only[Complex.ofReal_one,one_smul]; split; exact (charmB ..).1; exact (charmB ..).2
     · intro b j; funext x; have he':Action.parity (⇑p)= ⇑p:=by rw[show (⇑p:Density _ 6)=_ from ht]; exact (Patria.Depth.arrives A i hi).2.2.2.2
       let h:BudgetPoint:= ⟨2,6,1,2,1,le_rfl,le_rfl,by norm_num,by decide,by norm_num,le_rfl⟩; let z:= wrap (S.side R i) j; obtain ⟨C,_,hC⟩:=honest h.order h.power; let v:= Wagon (axle q a b) z x; have hp:Bean v:=(hC h _ le_rfl le_rfl _ z).bean x; change QCD.Grass.grade (v (p x))= v (p x); rw [← hp.grade]; exact congr_arg v (congr_fun he' x)
     intro b j s v h; let q0:= p; have he : Action.pin v s (⇑p)=⇑p:=by rw [show (⇑p:Density _ 6)=_ from ht]; exact (Patria.Depth.arrives A i hi).1 _ _ h
     rw [Patria.pinned]; rw[Patria.pinned] at he; funext U; let S':= S.side R i; let H':= pull s 0 U; let P:=Kit.disguise (copies 6 (hues (0:Site S') s (Patria.prism s) v.matrix.val)); change P (Wagon (axle q a b) _ _ _)= (↑(signT s b):ℂ) • Wagon (axle q a (s.perm b)) (wrap S' _) _ _; have hJ:= EuPin.retains s h; rw [elan _ _ _ _ U v.matrix.val 0 (Patria.prism s) (Patria.smoke s) hJ, show shiftE (n:=S') s 0 (wrap S' j)= wrap S' (s.act j) from ?_, show P _=_ from congr_fun he U]; rfl
     rw[← wrap_signed]; simp [shiftE,Signed.actEquiv]
end YM.Massive.PCAC.Oren
#print axioms YM.Massive.PCAC.Oren.growth
