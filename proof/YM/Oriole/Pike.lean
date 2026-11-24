import YM.Oriole.Slate
/-! Startup pivots at LevelQ β. signs and real weights ready.Volume allowances.L. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC Filter MeasureTheory RG
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d n:ℕ}(a b:Flavor 6)(g:Bool){c:Side}
open Poised.Display Poised.Stative Module Finset Revolve SourceRead Patria TorusPCAC.Geometry Cylinder
local notation "T"=> Lat.Fiber
local notation "G"=> pulp g
local notation "A"=> wave (claw g 0)
local notation "C"=> wave (pulp g)
local notation "V"=> wave (gamma 0)
open QCD.Entr.Goals
local notation "I"=> (0:Multi 8)
local notation "L"=> UV.first 0
open TorusPCAC.Ward Grass.Ward
variable (H:TaperHol)(q x y:ℂ)(X:Label 8)(P Y: Density c 6)(s:Bool)(p q': Multi 8)
local notation "w" q:arg p:arg => Nw H.T q p
local notation "kP"=> a
local notation "UP"=> rayC P a
local notation "RP"=> rayC P b
noncomputable abbrev poli (g:Bool):ℂ:=if g then 1 else -1
lemma Nug (i:Axis): Nw H.T I (0:Site c)=1∧ Nw H.T (UV.first i) (0:Site c)=0:=by
      rw [zeroN,N_one]; unfold Np; rw [show Lattice.lift (0:Site c)=0 from (by ext; simp [Lattice.lift]), show H.T.χ _=1 from H.T.near _ (fun j=>?_),Complex.ofReal_one,one_mul,show ap c 0=1 from (by simp [Cylinder.ap])]; simp
      norm_num [vector]
local notation "Y★"=> Canvas.foil P Y 1
local notation "B★"=> piece a b (uncoat Y★)
variable (hB:Plus (P 1))(hY:Y 1= PCAC.ore (0:Site c) s a b (pulp g) (P 1)) (hT:Tally H 0 X P Y)(hE:X=q • flame a b g 8 (by decide)+x • arbor a b g true+y • arbor a b g false)
include hB hY hT
lemma east (p q:Site c) : QCD.Run.cell B★ p q = if s then (if p=0 then -(C* QCD.Run.cell RP 0 q) else 0) else (if q=0 then -(QCD.Run.cell UP p 0*C) else 0):=by
     have ht: coef ∅ (Y 1)=0:=by rw[hY]; exact offMark _ _ _
     let Z:= P 1; let Lb:=(Stiffness.body P 1)⁻¹
     rw [hewn P Y hB hT.unit.self_of_nhds ht,hY]; have hv:(traceP (PCAC.ore (0:Site c) s a b G Z))= _ := quote s (localF (0:Site c) G a b) Z
     let k1(D:Sour (Modes c 6)) (z:ℂ):piece a b (z • D)=z • piece a b D:=rfl; cases s;
     · change QCD.Run.cell (piece _ _ (- Lb • (traceP (PCAC.ore 0 false _ _ _ _)))) p q=_; rw [hv]; simp only [Bool.false_eq_true,↓reduceIte]; rw [show piece a b (-Lb • _)=_ from k1 _ _, QCD.Run.cell_scale, LocalJ]; split; next ht=> subst q; change _ = -(QCD.Run.cell (Lb • _) _ _*_); rw [QCD.Run.cell_scale,Matrix.smul_mul,neg_smul]
       next _=>exact smul_zero _
     change QCD.Run.cell (piece _ _ (- Lb • traceP _)) p q = (if p=0 then _ else _); rw [hv]; simp only [↓reduceIte]; rw [show piece a b _=_ from k1 _ (-Lb),QCD.Run.cell_scale,LocalH]; split; next h=> subst p; change _ = -(_* QCD.Run.cell (Lb • _) _ _); rw [QCD.Run.cell_scale,Matrix.mul_smul, neg_smul]
     next _=> exact smul_zero _
include hE
lemma joy (t:Bool) : (if t then x else y) • A=∑ i:Site c,∑ j:Site c, (w (one_jet t 0) i * w (one_jet (!t) 0) j) • QCD.Run.cell B★ i j:=by
    let p:= one_jet t 0; let Z:=one_jet (!t) 0; let D:=juncoat X.val; have ht: qp a b p Z D=(if t then x else y) • A:=by unfold D; rw[hE]; exact Casing ..
    ext i j; rw [← ht]; simp_rw [Matrix.sum_apply]; exact script H P Y X hT ((p,i),a) ((Z,j),b) ((jet_value 0 t).le) -- Matrix sum_apply
lemma deepR : (if s then y else x) • A = (if s then -(C* Rod c H.T 0 RP) else -(Rv H.T 0 UP*C)) ∧ (if s then x else y) • A=0:=by
      have he:= joy a b g H q x y X P Y s hB hY hT hE true; have hp:= joy a b g H q x y X P Y s hB hY hT hE false; have hv(i j):= east a b g H X P Y s hB hY hT i j; simp_rw [hv] at he hp; have ht:=Nug (c:=c) H 0; cases s
      · constructor
        · rw [sum_comm] at he; simp only [Bool.false_eq_true,one_jet, Bool.not_true,↓reduceIte] at *; rw [he,sum_eq_single 0]; change _= -((∑ p:Site c,_)*C); rw [Matrix.sum_mul,← sum_neg_distrib]; refine sum_congr rfl fun i _=>?_ ; rw [ht.1,mul_one,if_pos rfl,smul_neg,Matrix.smul_mul]
          intro i _ h; simp only [if_neg h,smul_zero,sum_const_zero]; simp
        simp only [Bool.false_eq_true, one_jet,Bool.not_false,↓reduceIte] at *; rw[hp]; refine sum_eq_zero fun i _=>sum_eq_zero fun j _=>?_ ; split; next h=> rw[h, ht.2,mul_zero,zero_smul]
        next _=>exact smul_zero _
      · constructor
        · simp only [one_jet,Bool.not_false,Bool.false_eq_true,↓reduceIte] at hp; change y • A= -(C* ∑ i:Site c,_); rw [hp,sum_eq_single 0]; rw [Matrix.mul_sum,←sum_neg_distrib]; refine sum_congr rfl fun i _=>?_ ; rw [if_pos rfl,ht.1,one_mul,Matrix.mul_smul,smul_neg]
          intro i _ h; simp only[if_neg h,smul_zero,sum_const_zero]; simp
        simp only[one_jet,↓reduceIte,Bool.not_true,Bool.false_eq_true] at *; rw [he]; refine sum_eq_zero fun i _=>sum_eq_zero fun j _=>?_ ; split; next h=> rw[h,ht.2,zero_mul,zero_smul]
        next _=>exact smul_zero _
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.deepR
