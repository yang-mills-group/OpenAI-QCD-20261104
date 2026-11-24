import YM.Avian.Bur
/-! True tally routes in running D forecast. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall.Jewels
open Function Lattice RG Source Wilson Filter Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator Classical
open Cylinder QCD QCD.Lat QCD.Grass UV Patria Patria.Depth Patria.Exposure Patria.Hub Poised Poised.Plans Poised.Plans.Stamp Intag MassFields
open Lining Lining.Temper
open Tawny Cast
open StressFlux.Offer (acts marks Vc)
open Patria.Rolls Patria.Rolls.Attain
variable {S:Scheme}{R:Side}{i N p n d D:ℕ}(A:Run S N R 6)(T:SourceRead.TaperHol)(sym:RawSym)(B:Bore d)(hT:Rubric sym B)(F:PatchMix d)(hf:OrderMix A T sym B (i:=0) F)
variable (x:ℂ)(Q:RawTensor x d)
local notation "c"=> S.side R N
local notation "W'"=> A.density 0
local notation "Sχ"=> skyU A B F x Q
local notation "Yχ"=> vine A B F x Q
local notation "Vχ"=> divine A B F x Q
variable (hA:A.Actual)(i j:Axis)
noncomputable def path (i j:Axis)(x':Cover): Insertion (S.side R 0) 6:= trolley A (skyU A B F x Q i j) (shelS i j) 0 x'
noncomputable def castG(i:Axis): Density (S.side R 0) 6:= trolley A (divine A B F x Q i) (shelV i) 0 0
local notation "cR"=>path A B F x Q
local notation "ℓ"=>Lattice.step i
-- ROOT stencil equation
include hf hA hT
lemma readS : Tally T 0 (Q.val (i,j)) W' (cR i j 0):=hf.smoke _ _
lemma vert1 : ⇑(trolley A (Yχ i j) (shelV j) 0 0)=stunt i (cR i j 0):=by
     have hx(b p:Cover): march b (cR i j p)=⇑(cR i j (p+b)):= Depth.axial A hA _ (shelS i j) (fun i j=> hT.advances ..) _ _ (Nat.zero_le _)
     unfold stunt; rw[hx,hx]; unfold vine; rw [show trolley A _ _ _ _=((S.spacing 0)⁻¹/2) • (trolley A (skyU A B F x Q i j) (shelS i j) 0 (0+ℓ)- trolley A (skyU A B F x Q i j) (shelS i j) 0 (0-ℓ)) from stoic i (shelS i j) (shelV j) (can_go i [j] (by simp)) A _ _ (Nat.zero_le _)]; rw [Scheme.spacing_zero,zero_sub,zero_add,zero_add,inv_one]; rfl
lemma vert0 : castG A B F x Q j= ∑ i:Axis,stunt i (cR i j 0):=by
     let e:= shelV j; unfold castG; simp_rw [← vert1 A T sym B hT F hf _ _ hA]; unfold divine; let f:=fun X=> trolley A X e 0 0
     have hp(Y: Finset Axis): f (∑ i∈Y,Yχ i j)=∑ i∈Y,f (Yχ i j):=by
         induction Y using Finset.induction_on with
         | empty=> rw[sum_empty,sum_empty]; let X:=Yχ (0:Axis) j; rw[show (0:Cover → Insertion (S.side R N) 6)= (0:ℂ) • X from (zero_smul ..).symm]; unfold f; rw [scopeY,zero_smul]
         | insert i Y h ih=>rw [sum_insert h,sum_insert h, ← ih,show f _= _ from treadM ..] -- meta
     rw[show trolley A (∑ i:Axis,Yχ i j) (shelV j) 0 0= _ from hp univ]; funext i; rw [ContinuousMap.sum_apply,Finset.sum_apply]
-- true SungP each. section requires invariant
variable (hI:∀ t b i, Lat.Invariant (B t b i))
omit hA hT hf
lemma classy (X:Insertion c 6)(h:Lat.Invariant X): SungP (AllAt A 0 (A.regulator.density * X)):=fun k V=> DFunLike.congr_fun (Scheme.transport_gauge _ _ _ _ _ (Lat.invariant_mul _ _ (Regulator.invariant (R:=A.regulator)) h) (Nat.zero_le _) k) V
include hA in
lemma lived : SungP W':=by rw [pier A hA (Nat.zero_le _)]; simpa only [mul_one] using (classy A 1 Lat.invariant_one)
include hI
lemma signs (t:Cover) : SungP (cR i j t):=by
     unfold path trolley; apply classy; intro k; ext1 y; unfold visitor; rw [roles]; let U: Insertion c 6→ₗ[ℝ] Lat.Fields c 6:= (((slots 6 k).toLinearMap).comp (ContinuousMap.evalCLM ℂ (Lattice.gauge k y)).toLinearMap).restrictScalars ℝ; let V: Insertion c 6→ₗ[ℝ] Lat.Fields c 6:= (ContinuousMap.evalCLM ℝ y).toLinearMap; let G:= Sχ i j; let A:=ratioTo S N 0; let P(v: Cover→Insertion (S.side R N) 6):=rolls 1 A (menu (shelS i j)) v (A • t); have hp(x): U (G x) = V (G x):= DFunLike.congr_fun (hI c x (F (shelS i j) (Q.val (i,j))) k) y; change U (P G)=V (P G); unfold P; rw[rollLinear,rollLinear]; exact congr_arg₂ _ (funext hp) rfl -- cong
end YM.Massive.Patria.Gall.Jewels
#print axioms YM.Massive.Patria.Gall.Jewels.vert0
#print axioms YM.Massive.Patria.Gall.Jewels.lived
#print axioms YM.Massive.Patria.Gall.Jewels.signs
