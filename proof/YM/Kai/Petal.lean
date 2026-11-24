import YM.Kai.Lasso
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.PCAC.Oren
open Function Filter MeasureTheory QCD QCD.Lat QCD.Grass Lattice Wilson UV RG QCD.Grass.Ward
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator Classical TensorProduct Kronecker
open Poised Poised.Beacon Poised.Plans Finset Module Poised.Stative Massive.Patria Patria.Exposure Depth
open Entr Entr.Meridian Stew
open QCD.Tide Revolve Onsite
variable {S:Scheme}{R c:Side}{d n i l j:ℕ}
variable (a:Flavor 6)(p:Site c)(i j:Axis)(h:BudgetPoint)(U:Grid c)
local notation "s"=> Signed.mirror j
local notation "G"=> Patria.Exposure.eyeP c j
local notation "Y"=> (s).act p
local notation "X"=> localF p (gamma i) a a
local notation "l"=> κlease -- conflicts
local notation "w"=> ((signT (Signed.mirror j) i:ℝ):ℂ)
local notation "P'"=> pull s 0 U
-- True tilt. zone case: δmix tilt ψ and bar interchanges, X_n=− sign(s i) X'; net +.
lemma surfT (V:Lat.Fields c 6): tilt G (zoneD a p i P' V)=w • (zoneD a ((s).act p) i U (tilt G V)):=by
     let q:= (s).act p
     let pχ:= ((-w) • gamma i); have he:gamma j*pχ = star (gamma i)* gamma j:=by
          by_cases h:j=i
          · subst i; unfold pχ; simp [signT,Signed.mirror]
          unfold pχ; simp [signT,Signed.mirror,h, Lat.clifford h]
     have hp:localF q pχ a a= (-w) • localF q (gamma i) a a:=by unfold pχ localF flavorW; rw [TorusPCAC.Geometry.AxisB.roll,Matrix.smul_kronecker,Matrix.mul_smul]
     let v:= zoneD a p i P'; have hz(k:Bool): tilt G (applyMark k X V)=(-w) • applyMark (!k) (localF q (gamma i) a a) (tilt G V):=by
          have hh:=tilt_L (gamma i) j a a p pχ he k V; change _ = applyMark _ _ _ at hh; rw[hp, scales] at hh; exact hh
     change tilt G (_-_:Lat.Fields c 6) = w • (_-_); change tilt G (applyMark _ _ V - applyMark _ _ V)= w • (applyMark _ _ _-applyMark _ _ _); rw [map_sub,hz,hz,smul_sub]; simp; abel
local notation "Y1"=> keel ((s).act p) i a U
local notation "Y2"=> keelB ((s).act p) i a U
local notation "X1"=> keel p i a P'
local notation "X2"=> keelB p i a P'
lemma waveRed (V:Lat.Fields c 6): tilt G (beacon a p i P' V)= w • beacon a ((Signed.mirror j).act p) i U (tilt G V):=by
     obtain ⟨he,hT⟩:= spinK a 0 p s (Patria.prism s) i (gamma j) (Patria.smoke s) U; rw [rotor,gamma_star,show shiftE s 0 p=(s).act p from (by simp [shiftE,Signed.actEquiv])] at he hT
     have hz: G* ((-w) • Y2)=star X1 * G:=by
          change X2 * G= G*(w • Y2) at hT; rw [show star X1 = - X2 from (?_),Matrix.neg_mul,hT,neg_smul,mul_neg]
          exact neg_eq_iff_eq_neg.mp ((congr_fun (starKeel p i a) _).symm) -- check
     have hu: G* ((-w) • Y1)=star X2 * G:=by
          change X1 * G= G*(w • Y1) at he; rw [show star X2= -X1 from ?_,Matrix.neg_mul,he,neg_smul,mul_neg]
          have hP:X2= -star X1:=congr_fun (starKeel p i a) _; rw[hP,star_neg,star_star]
     have ht(A B:Sour (Modes c 6))(H: G*B=star A * G): B*G= G*star A:=by calc
              _=G*G*B*G:=by rw[eye_sq,one_mul]
              _=G*star A:=by rw[mul_assoc (G) G B,H,mul_assoc,mul_assoc (star A),eye_sq,mul_one]
     change tilt G (applyMark _ X1 V - applyMark _ X2 V)= w • (applyMark _ _ _-applyMark _ _ _); rw [map_sub,L_tilt _ X1 _ G (ht _ _ hz) hz,L_tilt _ X2 _ G (ht _ _ hu) hu, scales, scales, smul_sub]; simp; abel
-- flavor.G
local notation "Rho" u:arg=> TorusPCAC.Ward.acts (proclaim u) c
lemma tidy(M:Matrix (Modes c 6) (Modes c 6) ℂ)(he:∀ i j,i.2 ≠ j.2→ M i j=0)(u: FlavorTorus)(p:Bool)(V:Lat.Fields c 6): (Rho u) (applyMark p M V)=applyMark p M ((Rho u) V):=by
    let t:=TorusPCAC.Ward.tag c (proclaim u); have hM: M*t=t*M:=by
          unfold t TorusPCAC.Ward.tag; ext i j; rw [Matrix.diagonal_mul, Matrix.mul_diagonal]; by_cases hp:i.2=j.2
          · rw [hp,mul_comm]
          rw [he _ _ hp,mul_zero,zero_mul]
    exact Eq.trans (keyζ p 1 M M t (TorusPCAC.Ward.tag_unit _) (by rwa [one_smul]) V) (one_smul ..)
lemma charmB(z: FlavorTorus)(V:Lat.Fields c 6): (Rho z) (beacon a p i U V)=beacon a p i U ((Rho z) V)∧ (Rho z) (zoneD a p i U V)=zoneD a p i U ((Rho z) V):=by
     constructor
     · have hp(x y:Modes c 6)(h:x.2≠ y.2): (Stew.delta U i ⊗ₖ spot a a) x y=0:=by
             have hh: ¬(x.2=a ∧ y.2=a):=by rintro ⟨hu,hv⟩; exact h (hu.trans hv.symm)
             simp [spot,hh]
       change (Rho z) (applyMark _ _ V-applyMark _ _ V)=applyMark _ _ _-applyMark _ _ _; rw [map_sub]; exact congr_arg₂ (·-·) (tidy (keel p i a U) (fun x y h=> by rw[keel,zleft, hp _ _ h,ite_self]) z _ V) (tidy (keelB p i a U) (fun x y h=> by rw[keelB,zright,hp _ _ h,ite_self]) z _ V)
     have hp(x y:Modes c 6)(h:x.2≠y.2): (localF p (gamma i) a a) x y=0:=by
          unfold localF; rw[zleft]; have ht: ¬ (x.2=a∧ y.2=a):= (fun hh=> h (hh.1.trans hh.2.symm)); unfold flavorW; simp [spot,ht] -- edit
     change (Rho z) (applyMark _ _ V-applyMark _ _ V)=applyMark _ _ _-applyMark _ _ _; rw [map_sub]; exact congr_arg₂ (·-·) (tidy _ hp z _ V) (tidy _ hp z _ V)
end YM.Massive.PCAC.Oren
#print axioms YM.Massive.PCAC.Oren.surfT
#print axioms YM.Massive.PCAC.Oren.waveRed
#print axioms YM.Massive.PCAC.Oren.charmB
