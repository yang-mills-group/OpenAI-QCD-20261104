import YM.Lapin.Audit
/-!
  True connection algebra for ACTUAL density, unweighted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC.Oren
open Function Filter MeasureTheory Set QCD QCD.Lat QCD.Grass Lattice Wilson UV RG QCD.Grass.Ward
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator Classical TensorProduct Kronecker
open Poised Poised.Beacon Poised.Plans Finset Module Poised.Stative Massive.Patria Patria.Exposure Depth Intag
open Entr Entr.Meridian Stew Cylinder
open QCD.Tide Revolve Onsite Tawny Tawny.Cast TorusPCAC.Geometry TorusPCAC.Ward Oriole
variable {S:Scheme}{R c:Side}{d n i l j:ℕ}(A:Run S n R 6)(hA:A.Actual)
variable (a b:Flavor 6)(j:Axis)(X:Spike)(u:Averaging)
variable (Z:Sour (Modes c 6))(P Y : Density c 6)(U:Grid c)
local notation "M"=> S.side R i
local notation "φ"=> A.density i
local notation "Ξ"=> actor A i
local notation "Q" t:arg=> report A (marque (i:=i) A t a j) u
local notation "E" t:arg=> Gall.viaP A (marque (i:=i) A t a j) u i
local notation "F" => ms (i:=i) a A
local notation "N" => report A F u
local notation "G"=> Gall.viaP A F u i
local notation "J"=> gamma (0:Axis)
local notation "O"=> onSpin M J
-- on hermitian Vec.Constrained.Co.Screen.
lemma Ks (B:Sour (Modes c 6))(X:Sheet c): piece b b ((X ⊗ₖ spot a a)*B)=if b=a then X*piece b b B else 0:=by
       ext i j; change ((X ⊗ₖ spot a a)*B) (i,b) (j,b)=_; rw [Matrix.mul_apply,Fintype.sum_prod_type]; split
       next ht=> subst b; simp [Matrix.mul_apply,spot,mul_assoc,ite_mul,piece]
       next ht=> simp [spot,ht]
lemma Sv (B:Sour (Modes c 6))(X:Sheet c):piece b b (B*(X ⊗ₖ spot a a))=if b=a then piece b b B*X else 0:=by
       ext i j; change (B*(X ⊗ₖ spot a a)) (i,b) (j,b)=_; rw [Matrix.mul_apply,Fintype.sum_prod_type]; split
       next ht=> subst b; simp [Matrix.mul_apply,spot,piece]
       next ht=> simp [spot,ht]
lemma skews(P F' G':Density c 6)(U:Grid c) : Canvas.foil P (F'-G') U=Canvas.foil P F' U-Canvas.foil P G' U:= mul_sub ..
noncomputable def discs (a: Flavor 6):Lat.Fields c 6→ₗ[ℂ]Sheet c:= { toFun:=fun X=> piece a a (uncoat X),map_add':=fun X Y=>by rw [map_add]; rfl,map_smul':=fun x Y=>by rw [map_smul]; rfl }
private lemma rate : traceP (Y U-P U)=traceP (Y U) -traceP (P U):=by ext i j; simp[traceP]; abel
private lemma spark (k:Bool) (hP: IsUnit (P U))(hz:Plus (P U))(hx:Y U= applyMark k Z (P U)):
       discs b (Canvas.foil P Y U)= - (Stiffness.body P U)⁻¹ • piece b b (if k then Z*traceP (P U) else traceP (P U)*Z):=by
       let f(_:Grid c):= P U; let F'(_:Grid c):= Y U; have he:uncoat (Canvas.foil f F' 1)= -(Stiffness.body f 1)⁻¹ • traceP (F' 1):= hewn f F' hz hP (show coef ∅ (Y U)=0 from hx ▸ offMark ..) -- hx subst wrong
       change piece b b (uncoat (Canvas.foil f F' 1))=_; rw [he,show F' 1= _ from hx,quote]; rfl
lemma cove(H K:Sour (Modes c 6)) (hP:IsUnit (P U))(hz:Plus (P U))(hx:Y U= applyMark false H (P U)-applyMark true K (P U)) : discs b (Canvas.foil P Y U)= (Stiffness.body P U)⁻¹ • (piece b b (K* traceP (P U))-piece b b (traceP (P U)*H)):=by
       let F'(u):=applyMark false H (P u); let g(u):=applyMark true K (P u); rw [show Canvas.foil P Y U=Canvas.foil P (F'-g) U from congr_arg (Ring.inverse (P U)* ·) hx,skews,map_sub,spark b H P F' U false hP hz rfl,spark b K P g U true hP hz rfl] -- edit
       simp only[Bool.false_eq_true,↓reduceIte,neg_smul,smul_sub]; abel
include hA
variable (V:Grid (S.side R i))(hi:i ≤ n)
include hi
lemma peek : (N i (0:Cover)) V= - applyMark true (localF 0 J a a) (φ V):=by rw[arrivesHere]; change veer a _ _ (Ξ _)=_; rw[version,map_zero,show Ξ V = φ V from congr_fun (act A hA hi) V]
lemma m_sight : Gall.SungP (⇑(F 0)):=by
      let h:BudgetPoint:= ⟨2,6,1,2,1,le_rfl,le_rfl,by norm_num,by decide,by norm_num,le_rfl⟩; let p:= wrap M 0; intro k V; let T:= Lattice.gauge k V; have he:slots 6 k (Ξ T)=Ξ V := by rw [show Ξ T= φ T from congr_fun (act A hA hi) _,show Ξ V= φ V from congr_fun (act A hA hi) V]; exact Gall.dSung A hA hi k V
      change slots 6 k (veer a p T (Ξ T))=veer a _ V (Ξ V); rw [←he,(verify a p h).gauge]
lemma call_K : G V= - applyMark true (flavorW J a a M) (φ V):=by
       let h(V):= φ V; unfold Gall.viaP; rw [ContinuousMap.sum_apply]; have ht(j):((N i (lift j)) V)= -applyMark true (localF j J a a) (Ξ V):=by rw[arrivesHere]; change veer a _ _ _=_; rw [version,wrap_lift]
       change (∑ j:Site M,(N i (lift j)) V)=_; simp_rw [ht,sum_neg_distrib,mark_collect,show Ξ V= φ V from congr_fun (act A hA hi) V]
lemma rowB (hv:IsUnit (φ V)): discs a (Canvas.foil φ G V)=O*((Stiffness.body φ V)⁻¹ • piece a a (traceP (φ V))):=by
       let X:= flavorW J a a M; have hX:G V= applyMark false 0 (φ V)- applyMark true X (φ V):=by rw[call_K A hA a u V hi,show applyMark false (0:Sour (Modes M 6)) (φ V)=0 from (by simp [column]),zero_sub] -- signature
       rw [cove a _ _ _ _ _ hv (hA.even hi V) hX,mul_zero,show piece a a (0:Sour (Modes M 6))=0 from rfl, sub_zero,cutsLeft,Matrix.mul_smul] -- edit
lemma prismT (hv:IsUnit (φ V)) (p q:Site M) : QCD.Run.cell (discs a (Canvas.foil φ (N i 0) V)) p q=if p=0 then wave J * QCD.Run.cell ((Stiffness.body φ V)⁻¹ • piece a a (traceP (φ V))) p q else 0:=by
       let X:=localF (0:Site M) J a a; have hX: (N i 0) V=applyMark false 0 (φ V)-applyMark true X (φ V):=by rw[peek A hA a u V hi,show applyMark false (0:Sour (Modes M 6)) (φ V)=0 from (by simp[column]),zero_sub]
       rw [cove a _ _ _ _ _ hv (hA.even hi V) hX,mul_zero,show piece a a (0:Sour (Modes M 6))=0 from rfl,sub_zero,Run.cell_scale,LocalH]; split; next hh=>rw[Run.cell_scale, Matrix.mul_smul,hh]
       next _=>rw[smul_zero]
local notation "D"=> delta V j
local notation "K"=> delta V j ⊗ₖ spot a a
omit hA hi
private lemma collect {I:Type} [Fintype I](b:Bool)(Z:I→Sour (Modes c 6))(x:Lat.Fields c 6): ∑ p, applyMark b (Z p) x= applyMark b (∑ p,Z p) x:=by
       cases b <;> simp only [applyMark,LinearMap.sum_apply,Bool.false_eq_true, ↓reduceIte,LinearMap.smul_apply,Matrix.sum_apply,sum_smul]; all_goals rw[sum_comm]; apply sum_congr rfl; intro _ _; rw [sum_comm]
include hA hi
lemma wake : (E true) V=applyMark false K (φ V)-applyMark true K (φ V):=by
       unfold Gall.viaP; rw [ContinuousMap.sum_apply]; simp_rw [arrivesHere]; have he(p:Site M) : marque (i:=i) A true a j (lift p) V=applyMark false (keel p j a V) (φ V)-applyMark true (keelB p j a V) (φ V):=by
            change Wagon (axle true a j) (wrap M _) V (Ξ V)=_; unfold Wagon axle; simp only [wrap_lift, ↓reduceIte,Complex.ofReal_one,one_smul]; rw [show Ξ V= φ V from congr_fun (act A hA hi) V]; rfl
       simp_rw[he]; rw [sum_sub_distrib,collect,collect]; unfold keel keelB; rw[←sum_mul, ←mul_sum,cells,mul_one,one_mul]
lemma inkX (hv:IsUnit (φ V)) : discs b (Canvas.foil φ (E true) V)= if b=a then D*(O*discs b (Canvas.foil φ G V))-(O*discs b (Canvas.foil φ G V))*D else 0:=by
       rw [cove b _ _ _ _ _ hv (hA.even hi V) (wake A hA a j u V hi),Ks,Sv]; split
       next ht=> subst b; let Z:= (Stiffness.body φ V)⁻¹; rw[rowB A hA a u V hi hv,←mul_assoc O,show O*O=1 from ?_,one_mul,Matrix.mul_smul,Matrix.smul_mul,smul_sub]; rw[on_spin_mul,gamma_sq,on_spin_one]
       next _=> rw [sub_self,smul_zero]
end YM.Massive.PCAC.Oren
#print axioms YM.Massive.PCAC.Oren.prismT
#print axioms YM.Massive.PCAC.Oren.inkX
