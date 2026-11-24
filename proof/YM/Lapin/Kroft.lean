import YM.Lapin.Craft
import YM.Lapin.Rotate
/-! Genuine U1 birth. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical Kronecker InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open Tawny Tawny.Cast.Rays
variable {C:ℝ}{c:Side}{n l d m r k p q w i N:ℕ}{U:BudgetPoint}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC Patria Patria.Depth Patria.Rolls PCAC.Oren QCD.Grass.Ward
variable {S:Scheme}{R:Side}(A:Massive.Run S N R 6)(hA:A.Actual)(hi:i≤ N)
local notation "M"=> S.side R i
variable (a b:Flavor 6) (s t:Axis)(g:su.Color)(u:Averaging)(T:TaperHol)
local notation "φ"=> A.density i
local notation "G"=> marque (i:=i) A false a s
local notation "X"=> report A G u i 0
local notation "Z"=> foil φ X
local notation "D"=> localF (0:Site M) (gamma s) a a
local notation "B"=> wave (gamma s)
local notation "P"=> rayC φ a
open QCD.Entr.Goals
local notation "U₁"=> Rod M T.T
local notation "V₁"=> Rv T.T
local notation "O"=> (0:Multi 10)
omit hA hi
lemma veil(x : Site c): Nw T.T (leadR t) x = Nw T.T (UV.first t) x ∧ Nw T.T O x= Np T.T x:=by unfold Nw; rw [profile_0,profile_L]; have hp:Nw T.T (UV.first t) x=_ := N_one T.T x t; unfold Nw at hp; rw [hp]; simp -- cast
lemma βδ (c:Side): Np T.T (0:Site c)=1:=by rw [← zeroN]; exact (Nug T 0).1
private lemma stopL (Krr: Matrix (Modes c 6) (Modes c 6) ℂ)(hp:b≠a): let K:= localF (0:Site c) (gamma s) a a; piece b b (K*Krr)=0∧piece b b (Krr*K)=0:=by
        intro v; constructor
        · ext i j; change (v*Krr) (i,b) (j,b)=0; rw [Matrix.mul_apply]; apply sum_eq_zero; intro k _; rw [show v (i,b) k=0 from ?_,zero_mul]; unfold v; rw [localB]; split
          next h=> exact (hp h.2.1).elim
          next _=>rfl
        ext i j; change (Krr*v) (i,b) (j,b)=0; rw [Matrix.mul_apply]; apply sum_eq_zero; intro k _; rw[show v k (j,b)=0 from ?_,mul_zero]; unfold v; rw [localB]; split
        next h=>exact (hp h.2.2.2).elim
        next _=>rfl
variable (y:Label 10)(h:Tally T 0 y (A.density i) (report A (marque (i:=i) A false a s) u i 0))
include hA hi h
private lemma sheets0 : discs b (Z 1)=(Stiffness.body φ 1)⁻¹ • (piece b b (D*traceP (φ 1))-piece b b (traceP (φ 1)*D)) :=by
       refine cove b _ _ _ _ _ h.unit.self_of_nhds (hA.even hi 1) ?_; rw [arrivesHere]; change Wagon _ _ _ _=_; unfold Wagon PCAC.Oren.axle; rw [map_zero]; simp only [Complex.ofReal_one,one_smul,Bool.false_eq_true,↓reduceIte]; rw [show actor A i 1= φ 1 from congr_fun (act A hA hi) 1]; rfl
private lemma verse_h(x y':Site M) : QCD.Run.cell (discs b (Z 1)) x y'= if b=a then (if x=0 then B*QCD.Run.cell P 0 y' else 0)-(if y'=0 then QCD.Run.cell P x 0 * B else 0) else 0:=by
       rw[sheets0 A hA hi a b s u T y h]; split
       next hh=>subst b; rw[QCD.Run.cell_scale]; have he(K L:Sheet M): QCD.Run.cell (K-L) x y'= QCD.Run.cell K x y'-QCD.Run.cell L x y':=rfl; rw[he,LocalH,LocalJ,smul_sub]; split_ifs<;> simp only [Oriole.rayC,QCD.Run.cell_scale,Matrix.smul_mul,Matrix.mul_smul,smul_zero,zero_sub]
       next hh=> rw[(stopL a b s _ hh).1,(stopL a b s _ hh).2,sub_self,smul_zero]; rfl
local notation "L"=> leadR t
variable (j k':Fiber)
lemma ingot : point1 t b j k' y= if b=a then (-(V₁ t P*B)-B*U₁ t P) j k' else 0:=by
       let f(i j: Site M):= QCD.Run.cell (discs b (Z 1)) i j; have hm(p q:Multi 10)(hr:spinWeight p+spinWeight q ≤ 10): chipS b p q j k' y=(∑ i:Site M,∑ h:Site M,(ballast p q T.T i h) • f i h) j k':=by
            rw [←strokeL T _ _ _ _ _ _ h p q hr,Matrix.sum_apply]; simp_rw[Matrix.sum_apply]; rfl
       have hv(x v): f x v = _:=verse_h A hA hi a b s u T y h x v; rw [point1,LinearMap.sub_apply,hm L O (by rw[gradeL,gradeV]; norm_num),hm O L (by rw [gradeL,gradeV]; norm_num)]; simp_rw [hv]; by_cases he:b=a
       · subst b
         have hh(x y:Site M): ballast L O T.T x y=Nw T.T (UV.first t) x*Np T.T y:=by unfold ballast; rw[(veil ..).1,(veil t T y).2] -- order T t? declaration
         have hg(x y:Site M): ballast O L T.T x y=Np T.T x*Nw T.T (UV.first t) y:=by unfold ballast; rw[(veil t T x).2,(veil ..).1]
         simp only [↓reduceIte,smul_sub, hh,hg,sum_sub_distrib]; rw [show (∑ x:Site M,∑ y:Site M, (Nw T.T (UV.first t) x*Np T.T y) • (if x=0 then B*QCD.Run.cell P 0 y else 0))=0 from ?_,show (∑ x:Site M,∑ y:Site M, (Nw T.T (UV.first t) x*Np T.T y) • (if y=0 then QCD.Run.cell P x 0 * B else 0))= V₁ t P*B from ?_,show (∑ x:Site M,∑ y:Site M, (Np T.T x * Nw T.T (UV.first t) y) • (if y=0 then QCD.Run.cell P x 0*B else 0))=0 from ?_,show (∑ x:Site M,∑ y:Site M, (Np T.T x*Nw T.T (UV.first t) y) • (if x=0 then B*QCD.Run.cell P 0 y else 0))= B*U₁ t P from ?_, zero_sub,sub_zero]; rfl
         · change _= B* ∑ p:Site M,_; rw[sum_comm,Matrix.mul_sum]; apply sum_congr rfl; intro x _; rw[sum_eq_single (0:Site M)]; rw [if_pos rfl,βδ,one_mul,Matrix.mul_smul]; intro j _ h; rw[if_neg h,smul_zero]; simp
         · exact sum_eq_zero fun x _=>sum_eq_zero fun j _=>by
              split; next hh=>rw [hh,(Nug T t).2, mul_zero,zero_smul]
              next _=>exact smul_zero _
         · change _=(∑ p:Site M,_)*B; rw [Matrix.sum_mul]; refine sum_congr rfl fun x _=>?_ ; rw [sum_eq_single (0:Site M)]; rw[if_pos rfl,βδ,mul_one,Matrix.smul_mul]; intro j _ hh; rw [if_neg hh,smul_zero]; simp
         · exact sum_eq_zero fun x _=>sum_eq_zero fun j _=>by
              split; next hh=>rw [hh,(Nug T t).2, zero_mul,zero_smul]
              next _=>exact smul_zero _
       · simp [he]
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.ingot
