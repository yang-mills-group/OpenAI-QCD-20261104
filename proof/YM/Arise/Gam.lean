import YM.Arise.Unit
/-! # Pullback from gradient proof.Resource into genuine Wick.Basis. -/
set_option autoImplicit false
noncomputable section
namespace YM.Arise.Range
open Function Lattice Finset Wilson Filter MeasureTheory Tensor Work.G06 RG
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical TensorProduct
open Labels Maxwell Analysis Maxwell.Wick
variable {r n m i j k d e:ℕ}
variable {G: Gauge}(p: Axis)(x y: E4)
variable {z:E4}
variable {F M:Type}[NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup M][NormedSpace ℝ M]
local notation "T₁"=> Probe
-- µ from Leg. Include gauge representation weights.S upper counts.S. port to all-n permutations.U.
section
noncomputable def runeV (a:Tube G d) : Probe G a.1.1.val:= dollar a.1.1.val a.1.2 a.2
open MvPolynomial
lemma gated (p : Tube G d)(U: Jet G): Labels.read U (rollK G d (X p))=(pub d G U p:ℂ):=by rw [← AlgHom.comp_apply,hillG,nestK,aeval_X]
lemma gate_p (p: Tube G d)(X: TaylorTower G) : probe X (Maxwell.reduceEq (rollK G d (MvPolynomial.X p)))=(↑(runeV p (X _)):ℂ):=by rw [Maxwell.jet_value,gated]; apply congr_arg Complex.ofReal; unfold pub runeV rootLeg; rw [match_leg]; unfold dollar; rw [constrain]; dsimp only [LinearMap.comp_apply,LinearMap.smul_apply]; exact (Nat.cast_smul_eq_nsmul ℝ ..).symm
lemma dollarView (p:Tube G d) : Maxwell.reduceEq (rollK G d (X p)) = symbol p.1.1.val (runeV p):=by apply Maxwell.equalPol; intro X; rw [gate_p, symbol_test]
open Next.Rank Next.Rank.Normal
-- single-site kernel points. c via conform true hidden. WickPol.S glaze Proof port schema D-IP.
variable {I : Type}
abbrev ClockG (G:Gauge) (d:I→ℕ):= (i:I)× Tube G (d i)
noncomputable def purse (d:I→ℕ)(p:ClockG G d): I × Maxwell.Slot G→₀ℂ:=
    ∑ i: Fin (legDim G p.2.1.1.val), (((runeV p.2 (Maxwell.frame G _ i)):ℝ):ℂ) • Finsupp.single (p.1,(⟨p.2.1.1.val,i⟩: Maxwell.Slot G)) (1:ℂ)
lemma pleasant (d:I→ℕ)(p: I)(v:Lily G (d p)): Normal.exchange (purse d) (MvPolynomial.rename (fun i=> (⟨p,i⟩:ClockG G d)) v)= rename (fun i=>(p,i)) (reduceEq (rollK G (d p) v)):=by
    induction v using MvPolynomial.induction_on with
    | C a=> simp [show rollK G (d p) (C a)=C a from AlgHom.commutes ..,show reduceEq (C a: Pol G)=C a from AlgHom.commutes ..]
    | add a b h hp=>simp only [map_add,h,hp]
    | mul_X a i h=> simp only [map_mul,h,dollarView i]; rw [rename_X,exchange_x]; congr 1
                    unfold purse symbol; rw [map_sum,map_sum]; apply Finset.sum_congr rfl; intro k _; rw [map_smul, Normal.glyph,Finsupp.linearCombination_single,one_smul,C_mul',map_smul, rename_X]
lemma resetLeg (p: Probe G j): p=∑ i: Fin (legDim G j), p (Maxwell.frame G j i) • coordinateLeg (⟨j,i⟩: Maxwell.Slot G):=by
    apply LinearMap.ext; intro x; conv_lhs=> rw [← (Maxwell.frame G j).sum_repr x]
    let V(i:Fin (legDim G j)): Shell G j→ₗ[ℝ]ℝ:= p (Maxwell.frame G j i) • (coordinateLeg (⟨j,i⟩: Maxwell.Slot G):Shell G j→ₗ[ℝ]ℝ)
    change p _= (∑ i,V i) x; rw [map_sum p,LinearMap.sum_apply _ V x]; apply Finset.sum_congr rfl; intro i _; rw [map_smul p]; exact mul_comm ((Maxwell.frame G j).repr x i) _

noncomputable def call (x:I→E4)(d:I→ℕ): Normal.Symmetric (ClockG G d) where
    cov i j:= if x i.1 = x j.1 then 0 else (legKernel (runeV i.2) (runeV j.2) (x i.1-x j.1):ℂ)
    symm i j:= by
       by_cases h:x i.1=x j.1; · simp [h]
       rw [if_neg h,if_neg (Ne.symm h), ← neg_sub (a:= x i.1) (b:=x j.1)]; exact congr_arg (fun x:ℝ=>(x:ℂ)) (Maxwell.exchange _ _ (show x i.1-x j.1∈away from sub_ne_zero.mpr h))
lemma centsV (x : Points n)(h:x∈conf n) (d:Fin n→ℕ): Normal.scope (purse (G:=G) d) (Normal.frameX h) = call (fun i=> x i) d :=by
     apply Normal.Symmetric.ext; funext i j; let C:=Normal.frameX (G:=G) h; change Finsupp.linearCombination ℂ (Finsupp.linearCombination ℂ C.cov (purse d i)) (purse d j) = _
     unfold purse; rw [map_sum]; simp only [map_sum,map_smul,Finsupp.linearCombination_single,one_smul,Finset.sum_apply,Pi.smul_apply,C,frameX]
     by_cases ht:x i.1=x j.1
     · rw [show (call _ _).cov _ _=0 from if_pos ht]; have h':i.1=j.1:=(show Injective x.ofLp from h) ht; simp only [h',↓reduceIte,smul_zero,sum_const_zero] -- let C coil
     rw [show (call (fun i=> x i) d).cov i j=(legKernel (runeV i.2) (runeV j.2) (x i.1 - x j.1):ℂ) from if_neg ht]; have hx:=sub_ne_zero.mpr ht
     let u:=i.2.1.1.val; let v:=j.2.1.1.val; let Λ:=pairing (G:=G) (j:=u) (l:=v) (show (x i.1-x j.1)∈away from hx)
     conv_rhs=> change (Λ (runeV i.2) (runeV j.2):ℂ); rw [resetLeg (runeV j.2),map_sum]
     rw [Complex.ofReal_sum]; apply Finset.sum_congr rfl; intro a _; simp only [map_smul, Complex.ofReal_mul, smul_eq_mul]; congr 1
     conv_rhs=> rw [resetLeg (runeV i.2),map_sum Λ]
     rw [LinearMap.sum_apply, Complex.ofReal_sum]; apply Finset.sum_congr rfl; intro b _; simp only [Λ, map_smul, LinearMap.smul_apply]; change (_:ℂ)*(if _ then _ else _) = ((↑((_:ℝ)*(_)):ℂ)); rw [if_neg (fun h:i.1=j.1=> ht (congr_arg _ h)),Complex.ofReal_mul]; rfl
-- subset injective tiles transport call. export Law to tests
variable (A:Fin n→I)
noncomputable def chairG (d:I→ℕ)(p:ClockG G (d∘A)): ClockG G d:=⟨A p.1,p.2⟩
lemma come (d:I→ℕ)(x:I→E4)(hx:points (x∘A)∈conf n)(a b: ClockG G (d∘A)): (call (x∘A) _).cov a b=(call x d).cov (chairG A d a) (chairG A d b):=rfl
set_option maxHeartbeats 500000 in
lemma highlight (x:I→ E4)(hx:points (x ∘ A)∈conf n)(d:I→ℕ)(p:(i:Fin n)→ Lily G (d (A i))) :
      Maxwell.Wick.moment G (points (x∘A)) (fun i =>Maxwell.reduceEq (rollK _ _ (p i)))= blend (call x d) 0 (∏ i,rename (fun y=>(⟨A i,y⟩:ClockG G d)) (p i)):=by
    let v:=points (x∘A); let f:=purse (G:=G) (d ∘ A); let h(i:Fin n):=rename (fun y=> (⟨i,y⟩:ClockG G (d∘ A))) (p i); let F:= (MvPolynomial.rename (R:=ℂ) (chairG (G:=G) A d)); let K(i:ClockG G (d∘A)) := Finsupp.single (chairG A d i) (1:ℂ)
    have he(i j: ClockG G (d∘A)) : (scope K (call x d)).cov i j=(call (x∘A) (d∘A)).cov i j:= (match_name (chairG (G:=G) A d) (call x d) i j).trans (come A d x hx i j).symm
    have ht: scope K (call x d)=call (x∘A) (d∘A):=Normal.Symmetric.ext (funext fun i=>funext fun j=>he i j)
    have hp0: (scope f (Normal.frameX hx))=scope K (call x d):=by rw [ht]; exact centsV v hx (d ∘ A)
    let U:=fun i:Fin n=> reduceEq (rollK G (d (A i)) (p i)); let W:=∏ i,h i
    have h1:(∏ i:Fin n,MvPolynomial.rename (fun y:Maxwell.Slot G=> (i,y)) (U i))= Normal.exchange f W:=by unfold W; rw [map_prod]; apply Finset.prod_congr rfl; intro i _; exact (pleasant (d∘A) _ (p i)).symm
    have h2:(∏ i:Fin n,rename (fun y=>(⟨A i,y⟩:ClockG G d)) (p i))= Normal.exchange K W:=by
        rw [← show F=Normal.exchange K from (Normal.labelled (chairG (G:=G) A d))]; unfold W; rw [map_prod]; apply Finset.prod_congr rfl; intro i _; exact (MvPolynomial.rename_rename (fun v=> (⟨i,v⟩:ClockG G (d ∘ A))) (chairG (G:=G) A d) (p i)).symm
    change moment G v U=_; rw [Wick_reads (p:=U) hx,h1,h2,wets, wets,hp0, show reads K 0=0 from funext fun i=> Finsupp.linearCombination_zero_apply .., show reads f 0=0 from funext fun i=> Finsupp.linearCombination_zero_apply ..]
end
end YM.Arise.Range
#print axioms YM.Arise.Range.highlight
