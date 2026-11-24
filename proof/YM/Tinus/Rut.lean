import YM.Tinus.TiltQ
import YM.Tinus.Wreath
import YM.HONE.Pop
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open YM.Next.Free
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical ComplexOrder Kronecker
-- sphere of assets. finite shape rotation branch
structure Herald where
    (x y:Flavor 6)
    (left axial negateP:Bool)
namespace Herald
variable {S:Scheme}{c f R:Side}{i n F:ℕ}(A:Massive.Run S n R 6)
variable (r:Herald)
noncomputable def spike : Spike:= let u:= if r.axial then Lat.g5 else 1; if r.negateP then -u else u
noncomputable abbrev typeL (Y:Herald):Prop:= Y.x≠Y.y
noncomputable def turn : Herald:= ⟨r.y,r.x, !r.left,r.axial,xor r.negateP r.axial⟩
lemma tick(i:Axis):gamma i*r.turn.spike = star r.spike*gamma i :=by cases r with| mk x y v a b=> cases a <;> cases b <;> simp [turn,spike,Lat.five] -- signs syntax
noncomputable abbrev ink(i:ℕ) : Cover → Insertion (S.side R i) 6:= stalk r.spike A r.x r.y r.left i
open Massive.Patria Massive.Patria.Depth QCD.Tide Exposure
variable (h:A.Actual) (hi:i≤ n)
include h hi
lemma leveled (a:Axis)(k:Cover): Cylinder.Action.adj a (⇑(r.ink A i k))= ⇑(r.turn.ink A i ((Signed.mirror a).act k)):=by
      have he: Cylinder.Action.adj a (⇑(actor A i))= ⇑(actor A i):=by
           let f:= ⇑(actor A i); change Cylinder.Action.adj a f=f
           unfold f; rw [act A h hi,pier A h hi]; exact (Patria.Depth.arrives A i hi).2.1 a
      funext U; rw [eye_value]; let G:=eyeP (S.side R i) a; let x:=actor A i; let s:= Signed.mirror a; change tilt G (ore _ _ _ _ r.spike (x (pull s 0 U)))= ore (wrap _ (s.act k)) (!r.left) r.y r.x r.turn.spike (x U); rw[← show Cylinder.Action.adj a (⇑x) U=x U from congr_fun he U, eye_value]; rw[←wrap_signed]; apply tilt_L; exact r.tick a -- arity
omit h hi
noncomputable abbrev priceH:= max (veinFare 1) (veinFare Lat.g5)
lemma admits : veinFare r.spike ≤ priceH:=by
      have h(X:Spike): veinFare (-X)=veinFare X:= by unfold veinFare; simp_rw [QCD.Revolve.wave_neg,Matrix.neg_apply,norm_neg];
      cases r with| mk x y v a b=> cases a <;> cases b <;> first | exact le_max_left ..| exact le_max_right .. | exact Eq.trans_le (h _) (le_max_left ..)| exact Eq.trans_le (h _) (le_max_right ..)
noncomputable abbrev loans (c:Side)(u:Cover):= ore (wrap c u) r.left r.x r.y r.spike
lemma earned(c:Side)(u:Cover)(h:typeL r)(x:ℝ)(hx:priceH ≤ x): Veins (wrap c u) (r.loans c u) x:=by
      let i:=wrap c u; obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩:= veinLaw r.x r.y i r.spike r.left h; have he:= (r.admits).trans hx; exact ⟨h1,h2,h3,h4,h5,h6,h7.trans he,fun v ε hv=>(h8 v ε hv).trans (mul_le_mul_of_nonneg_right he (QCD.Creek.load_nn ..))⟩ -- signature
open Cells YM.Intag.Pilgrim YM.Intag.Hymnal
noncomputable def rod (a:List Axis): Herald:= match a with| .nil=>r|.cons _ s=>(rod s).turn
variable {f:Side}
open Cells YM.Intag.Hickory
noncomputable def charts (T:Tiling f)(p j:T.Cell):Herald:=r.rod (reversa T p j)
lemma turns (T:Tiling f)(p j:T.Cell)(h:j ≠ p) : r.charts T p j=(r.charts T p (YM.Intag.Pilgrim.μ T p j)).turn:=by unfold charts; rw [writes T p j h,rod]
lemma chart0 (T:Tiling f)(p:T.Cell) : r.charts T p p=r:=by unfold charts reversa; rw [YM.Intag.Pilgrim.at_p]; rfl
lemma charts_ok (he:typeL r)(T:Tiling f)(p j:T.Cell): typeL (r.charts T p j):=by
      suffices H: ∀ x,typeL (r.rod x) from H _
      intro x; induction x with | nil=>exact he|cons a l ih=>exact Ne.symm ih
end Herald
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.Herald.leveled
