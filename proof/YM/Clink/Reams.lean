import YM.Clink.Para
import YM.Lapin.Zink
/-! Reading hats as W-stamp columns in authentic projection. Mentor pose author fields; polar mixing.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.PCAC.Oren
open Function Filter MeasureTheory Set QCD QCD.Lat QCD.Grass Lattice Wilson UV RG QCD.Grass.Ward
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator Classical TensorProduct Kronecker
open Poised Poised.Beacon Poised.Plans Finset Module Poised.Stative Massive.Patria Patria.Exposure Depth Intag
open Entr Entr.Meridian Stew Cylinder
open QCD.Tide Revolve Onsite Tawny Tawny.Cast TorusPCAC.Geometry TorusPCAC.Ward Oriole
open Next.Free QCD.Flume TorusPCAC.Jet TorusPCAC.Spin TorusPCAC.Jet.Selector Switch AxisB
variable {S: Scheme}{c R:Side}{i n:ℕ}(A: Run S n R 6)(hA:A.Actual)(hi:i≤ n)(d:ℕ)(P:Plan d)(H:Train d)(m:ℝ)(a:Flavor 6)(x:Axis)(u:Averaging)
local notation "M"=> S.side R i
local notation "Ξ"=> actor A i
local notation "P!"=> cedar d P H m M
open MassiveQCD.Sample.Basal.Surge MassiveQCD.Sample.Basal
variable (F D: Axis → Cover → Insertion (S.side R i) 6)
lemma surgeS (h:Roars F)(z:ℂ): Roars (z • F):=by
       constructor
       · intro a b; rw [charge_west]; have he:=h.color a b; rw[charge_west] at he; funext j; let V:=TorusPCAC.Stencil.charge M (N:=6); change V (z • _) = _; rw[map_smul,show V _= _ from congr_fun he j]; rfl
       · intro a b u'; rw[flavor_show]; have he:=h.charm a b u'; rw[flavor_show] at he; funext U; let T:= TorusPCAC.Ward.acts (proclaim u') M; change T (z • _)= _; rw [map_smul,show T _= _ from congr_fun he U]; rfl
       · intro a b; funext V; change QCD.Grass.grade (z • _) =_; rw [map_smul,show QCD.Grass.grade _= _ from congr_fun (h.still a b) V]; rfl
       intro a b s v hp; have he:=h.pin a b s v hp; rw [Patria.pinned] at he; rw [Patria.pinned]; funext U; let T:= Kit.disguise (copies 6 (hues (0:Site (S.side R i)) s (Patria.prism s) v.matrix.val)); change T (z • _)=(↑(signT s a):ℂ) • _; rw[map_smul,show T _= _ from congr_fun he U]; exact smul_comm z (↑(signT s a):ℂ) (F (s.perm a) (s.act b) U)
variable (X:Cover→Insertion (S.side R i) 6)
lemma pledgeB (h:TideT A u i (report A X u))(z:ℂ): TideT A u i (report A (z • X) u):=by
       apply stampF ; intro a b; have hp:=(h.moves i le_rfl).trans b a; simp_rw [arrivesHere] at hp; funext U; let T:= Kit.disguise (copies 6 (hues (wrap M b) 1 (heat b) 1)); change T (z • _)=z • _; rw[map_smul,show T _= _ from congr_fun hp U]
local notation "G"=> corm (i:=i) A d P H m a
local notation "F'"=> marque (i:=i) A false
local notation "D'"=> sprigs (i:=i) A
variable (z:ℂ)
lemma gets0 (u:Cover): (⇑(G x u):Density M 6) =(Surge.tilde a P! x).eats (⇑Ξ) u :=by
        funext V; change Wagon _ _ V _+ _=_; unfold Wagon PCAC.Oren.axle; simp only[Complex.ofReal_one,one_smul,↓reduceIte]; rfl
lemma gets1 (u:Cover): (⇑(F' a x u): Density M 6)= (Surge.solo a M x).eats (⇑Ξ) u:=by
        funext V; change Wagon _ _ V _= _ + _*(0:Lat.Fields M 6); unfold Wagon PCAC.Oren.axle; simp only[Complex.ofReal_one,mul_zero,add_zero,one_smul,Bool.false_eq_true,↓reduceIte]; rfl
lemma getsZ (u:Cover): (⇑(D' a x u): Density M 6)= (Surge.hark a M x).eats (⇑Ξ) u:=by funext V; change _=(0:Lat.Fields M 6)+_; rw [zero_add]; rfl
lemma getsP (u:Cover): (⇑(ms a A (i:=i) u):Density M 6) =(Surge.pole a M).eats (⇑Ξ) u :=by funext V; change _= _+_*(0:Lat.Fields M 6); rw [mul_zero,add_zero]; rfl
-- Blend shaped.Ea & Z. paired scaled behind one calendar.PS.
local notation "RX"=> Flavor 6
variable (f g:Flavor 6→ℂ)
noncomputable def bead (F: Flavor 6): Axis → Cover→Insertion (S.side R i) 6:= f F • marque A false F+g F • sprigs A F
noncomputable def lobbyR := corm (i:=i) A d P H m a + ∑ b:Flavor 6,bead (i:=i) A f g b
local notation "Y"=> bead (i:=i) A f g
local notation "R!"=>lobbyR A d P H m a f g
include hA hi
lemma ΨE :Roars (lobbyR (i:=i) A d P H m a f g)∧ ∀ x:Axis, TideT A (Rolls.shelV x) i (report A (lobbyR (i:=i) A d P H m a f g x) (Rolls.shelV x)):=by
       have he(b:Flavor 6): Roars (bead (i:=i) A f g b) := Roars.addition _ _ (surgeS _ (growth A hA _ _ hi) _) (surgeS _ (spoke A hA hi _) _); have ht:Roars (corm (i:=i) A d P H m a):= Roars.addition _ _ (growth A hA true a hi) (angieP A hA hi d P H m a) -- args.s
       let z:= corm (i:=i) A d P H m a; have hp(S:Finset (Flavor 6)): Roars (z + ∑ b∈ S,Y b):=by induction S using Finset.induction_on with| empty=> simp only [sum_empty,add_zero]; exact ht| insert a s ha ih=> rw [sum_insert ha,add_comm (Y a),← add_assoc]; exact Roars.addition _ _ ih (he a)
       refine ⟨hp _,fun x=>?_⟩
       let p:= Rolls.shelV x; have hP(F): TideT A p i (report A (Y F x) p):=blendT A p _ _ (pledgeB A p _ (stampC _ A hA hi _) _) (pledgeB A p _ (nour A hA hi F x p) _)
       have hD:TideT A p i (report A (z x) p):=blendT A p _ _ (stampC _ A hA hi _) (b_stem A hA hi d P H m a x p)
       have hK (s:Finset (Flavor 6)):TideT A p i (report A ((z+∑ b∈s, Y b) x) p):=by
             induction s using Finset.induction_on with| empty=> rw [sum_empty,add_zero]; exact hD| insert a s ha ih=> rw [sum_insert ha,add_comm (Y a),← add_assoc,Pi.add_apply]; exact blendT A p _ _ ih (hP a)
       exact hK _
end YM.Massive.PCAC.Oren
#print axioms YM.Massive.PCAC.Oren.ΨE
#print axioms YM.Massive.PCAC.Oren.gets1
#print axioms YM.Massive.PCAC.Oren.getsP
