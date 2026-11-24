import YM.Elix.Push
import YM.Elix.Dawn
/-! Nonvanishing of ARC determinant in wick. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall.Onyx.Gourd
open Function Lattice RG Source Wilson Filter Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator Classical
open Cylinder QCD QCD.Lat QCD.Grass UV Patria Patria.Depth Patria.Exposure Patria.Hub Poised Poised.Plans Poised.Plans.Stamp Intag MassFields
open Lining Lining.Temper SourceRead Oriole Patria.Rolls Tawny Cast Carnal
open YM.MassiveMasses.FreePair Tarn Tarn.Choir Tarn.Choir.Measures YM.Analysis
local notation "U"=> (fun _ : Fin 2=>6)

set_option quotPrecheck false
local notation "κ"=> (((↑(2*Maxwell.normal)):ℂ))
local notation "Λ"=> basis 2
noncomputable def s1(a b:Flavor 6)(i:Axis)(x:E4):ℂ:= UV.Free.wick (fun _ : Fin 2=>6) (Tarn.Choir.Measures.arm x) ![gamma6 a 2 0 1,gamma6 b i 0 1]
local notation "K" i:arg=> wave (trio i 0 1)
variable (a b: Flavor 6)(i j:Axis)
local notation "X" x:arg=> Tarn.Choir.Measures.arm x
lemma everyX (x:E4)(h:x≠0) : s1 a b i x= if a=b then joined (K 2) (K i) (-x) else 0:=by
      unfold s1 UV.Free.wick; let v:= (0:Multi 6); let S':= (![gamma6 a 2 0 1,gamma6 b i 0 1]:Fin 2→ UV.Label 6); rw[MultilinearMap.compLinearMap_apply]; have ht:(fun i:Fin 2=>(S' i).val)=![UV.bilinear a a (trio 2 0 1) v v,UV.bilinear b b (trio i 0 1) v v]:=by ext1 i; fin_cases i <;> rfl
      change UV.Free.moment _ _ (fun i=>(S' i).val)= _; rw [ht,tango 6 a b (show (Measures.arm x) 0 ≠ (Measures.arm x) 1 from Ne.symm h)]; rw [show ((Tarn.Choir.Measures.arm x) 0-(Tarn.Choir.Measures.arm x) 1)= -x from zero_sub x] -- notation parser
lemma Ray : D (basis i) (s1 a b i) Λ= if a=b then D (basis i) (fun x=>joined (K 2) (K i) (-x)) Λ else 0:=by
     by_cases he:a=b
     · rw[if_pos he]; refine GermD _ ?_; filter_upwards [(isOpen_ne_fun continuous_id continuous_const).mem_nhds (x:=Λ) (by intro h; have ht:=basis_norm (2:Axis); rw[h,norm_zero] at ht; exact zero_ne_one ht : Λ≠ (0:E4))] with x hx; rw [everyX _ _ _ x hx,if_pos he] -- neq via basis norms
     rw [if_neg he]; refine (GermD _ (g:=fun _=> (0:ℂ)) ?_).trans (by simp [D])
     filter_upwards [(isOpen_ne_fun continuous_id continuous_const).mem_nhds (x:=Λ) (by intro h; have ht:=basis_norm (2:Axis); rw[h,norm_zero] at ht; exact zero_ne_one ht : Λ≠ (0:E4))] with x hx; rw[everyX _ _ _ x hx,if_neg he]
-- actual algebra traces without gamma choice
local notation "P2"=> (2:Axis)
local notation "P3"=> (3:Axis)
local notation "u"=> (0:Axis)
local notation "v"=> (1:Axis)
local notation "A"=> gamma 2
local notation "B"=> gamma 3
local notation "C"=> (gamma 0 * gamma 1)
lemma center (i:Axis)(h1:i≠0)(h2:i≠1): C * gamma i= gamma i* C:=by rw [mul_assoc, Lat.clifford h2.symm,mul_neg,←mul_assoc,Lat.clifford h1.symm,neg_mul,mul_assoc,neg_neg]
lemma cor : C*C= -(1:Spike):=by
      rw [mul_assoc (gamma 0) (gamma 1),←mul_assoc (gamma 1),Lat.clifford (by decide : (1:Axis) ≠ 0),neg_mul, Matrix.mul_assoc, gamma_sq, mul_one,mul_neg, gamma_sq]
lemma payments : (K P2 * tube P2 * K P2*tube P2)= -(1:Bundle) ∧ K P2*tube P3 * K P3*tube P2 = -(1:Bundle) ∧ K P2 *tube P2 *K P3*tube P3= -(1:Bundle):=by
     have he: K P2=wave (A*C):=by simp [trio,Fin.ext_iff,mul_assoc] -- simp syntax
     have hT: K P3=wave (B*C):=by simp [trio, Fin.ext_iff,mul_assoc]
     have hP(i:Axis)(h:i≠0)(ht:i≠1) : (gamma i*C)*gamma i=C:=by rw [mul_assoc, center i h ht, ← mul_assoc,gamma_sq, one_mul]
     have hN:wave (-(1:Spike))= -(1:Bundle):=by rw [show wave (-(1:Spike))= -wave (1:Spike) from ?_, wave_one]; ext i j; simp only[wave,Matrix.kroneckerMap_apply,Matrix.neg_apply]; exact neg_mul _ _ -- order notation
     simp_rw [he,hT,tube, Lat.wave_mul,hP P2 (by decide) (by decide)]; -- yields C*C ?
     constructor
     · rw [mul_assoc C (_*_),hP P2 (by decide) (by decide), cor,hN]
     constructor
     · have hS:A*C*B*(B*C)*A= -(1:Spike):=by rw [← mul_assoc _ _ C, mul_assoc (A*C) B B,gamma_sq, mul_one,mul_assoc A C C,cor,mul_neg,mul_one,neg_mul, gamma_sq]
       rw[hS,hN]
     rw [mul_assoc C (_ *_),hP P3 (by decide) (by decide), cor, hN]
lemma sigmaW : (∑ i:Axis,D (basis i) (s1 a b i) Λ)= if a=b then (48:ℂ)*κ^2 else 0:=by
     simp_rw [Ray]; by_cases ht:a=b
     ·
       have h0: K u = 0:=by simp[trio, Lat.wave_zero]
       have h1: K v=0:=by simp[trio,Lat.wave_zero]
       have h2: cProp P2= (-(3:ℂ)* κ) • tube P2:=by unfold cProp fSing; rw [basis_eq,if_pos rfl]; rw [←add_smul]; refine congr_arg₂ HSMul.hSMul ?_ rfl; push_cast; ring
       have h3: cProp P3=κ • tube P3:=by unfold cProp fSing; rw [basis_eq,if_neg (by decide),mul_zero,Complex.ofReal_zero,zero_smul,add_zero]
       rw [if_pos ht, Fin.sum_univ_four]; simp_rw [if_pos ht,pCross]; obtain ⟨hh,hH,hT⟩:= payments; simp_rw [h0,h1, peaked,h2,h3]; simp only [mul_zero,zero_mul,Matrix.mul_smul,Matrix.smul_mul,hh,hH,hT]; simp only [Matrix.trace_add, Matrix.trace_neg, Matrix.trace_one,Matrix.trace_zero,Matrix.trace_smul,smul_eq_mul,smul_smul,Fintype.card_prod, Fintype.card_fin]; push_cast; ring -- simplify arith
     simp [ht]
end YM.Massive.Patria.Gall.Onyx.Gourd
#print axioms YM.Massive.Patria.Gall.Onyx.Gourd.sigmaW
