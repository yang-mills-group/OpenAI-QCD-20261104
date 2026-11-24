import YM.Gust.Ach
set_option autoImplicit false
set_option maxHeartbeats 520000
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter MeasureTheory Analysis Tarn Tarn.Choir Tarn.Choir.Strip UV Mater Kind Gala
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ComplexOrder Matrix InnerProductSpace Classical
variable {K: Choir}{C: Sequence}{P:Calibration C}{T:Pollens P K}(hK:K.Domestic)(hf: Foil P K T){m n k:ℕ}{x:Points m}{y:Points k}(a:Axis)
variable (Y:Kernel.Gram fun z w:Visitors T a n=> gate (backward hK z.val a++w.val))
local notation "F"=>Factory T n
local notation "L"=> polarM hK hf n
open Spiral.Word
variable (u:(Factory T n).Word)(v:(Factory T n).Word) (hu: Spiral.Word.Positive u a)(hv: Spiral.Word.Positive v a)
include hu
lemma asks: Clear (positions u) a:=⟨hu.1,fun i=>hu.2 _ (List.get_mem ..)⟩
omit hu
noncomputable abbrev liftW (hv:Spiral.Word.Positive v a):=(crane hK a Y (asks a v hv)) (fun i=> stint hK hf (tokens v i))
lemma tintP (v:(Factory T n).Token): Fees (stint hK hf ((Factory T n).reflectedToken a v)) (shadow hK T a n (stint hK hf v)) :=by
       refine Fees.hop (spinning hK hf (star v.2) _ _ (couture a)) (Fees.spin_meets hK (couture a) (walnut hK hf v.2 a))
lemma aligned (v:(Factory T n).Word) (u:(Factory T n).Word): Spiral.Word.reflect u a ++v = realize (Fin.append (fun i=> (F).reflectedToken a (tokens u i.rev)) (tokens v)) (crestM (positions u) (positions v) a):=by
      rw [reflectedPoint]
      conv_lhs=> lhs; arg 2; arg 1; rw[← List.ofFn_get u]
      rw [← UV.Free.Lyre.reversesV u.get,List.map_ofFn]
      let f:=fun i:Fin u.length=>(Ortho.move (Signed.reflect a) (positions u i.rev),(F).reflectedToken a (tokens u i.rev)); have he := List.ofFn_fin_append f v.get
      rw [List.ofFn_get] at he
      refine Eq.trans he.symm ?_; unfold realize; refine congr_arg _ ?_; funext i; cases i using Fin.addCases <;> simp [f, crestM,tokens,positions]
include hu hv
lemma quality: inner ℂ (liftW hK hf a Y u hu) (liftW hK hf a Y v hv) = (L).gram a u v:=by
       let x:=positions u; let y:=positions v; unfold Spiral.Table.gram; rw[aligned a v u,(L).readAt,starts]; unfold liftW; rw [smoothRP hK]; apply face_any; intro i; induction i using Fin.addCases with
       | left i=> simp only[Function.comp_apply,Fin.append_left]; exact Fees.swap (tintP hK hf a _)
       | right i=> simp only[Function.comp_apply,Fin.append_right]; exact Fees.older
omit hv hu
variable (n)
lemma reflectionP:(polarM hK hf n).RP:=by
       intro a m w hw c
       obtain ⟨Y⟩:= chamberR hK hf n a; let coP(i:Fin m):= liftW hK hf a Y (w i) (hw i)
       have h (i j:Fin m): inner ℂ (coP i) (coP j)=_:= quality hK hf a Y (w i) (w j) (hw i) (hw j)
       let V:= ∑ i,c i • coP i; have hp: 0 ≤ inner ℂ V V:=by rw [inner_self_eq_norm_sq_to_K]; positivity
       rw[show inner ℂ V V=∑ i, ∑ j : Fin m, star (c i)*c j*(polarM hK hf n).gram a (w i) (w j) from ?_] at hp; exact hp
       unfold V; rw [sum_inner]; apply Finset.sum_congr rfl; intro i _; rw [inner_sum]; apply Finset.sum_congr rfl; intro j _; rw[inner_smul_left,inner_smul_right,h]; exact (mul_assoc ..).symm
end YM.Massive.Gust
#print axioms YM.Massive.Gust.reflectionP
