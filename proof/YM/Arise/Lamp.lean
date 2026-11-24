import YM.Arise.Parlance
import YM.Vest.Pair
/-! # Cumulative tilt comparison at actual end. Compression. Lens outputs relative neutral tags read. -/
set_option autoImplicit false
noncomputable section
namespace YM.Arise.Count
open Function Lattice Finset Wilson Filter MeasureTheory Tensor Work.G06 RG
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical TensorProduct
open Massive UV UV.Free QCD QCD.Grass QCD.Bera QCD.Cove QCD.Anomaly QCD.Creek Count Vest
open MassiveQCD.Sample.Quills
open MassiveQCD.Ribbon
open YM.Arise.Range YM.Arise.Bill
open MassiveQCD.Play MassiveQCD.Play.Chamber
variable {n m i j d k l:ℕ}
variable {I X Y B A C F D:Type}[Fintype I][Fintype X][Fintype Y][Fintype A][Fintype B][Fintype C][Fintype F][Fintype D]
section Fold
open MassiveQCD.FlareV
open Next.Rank Normal
noncomputable def frost (Q:Tone A X B Y)(x:B→ℝ): Tone A X Unit Y:=⟨Q.P*(Matrix.of fun i (_:Unit)=> (x i:ℂ)),Q.Q,Q.M,Q.V⟩
local notation "Oz"=> Oce.rose
local notation "Pl"=> Papers A (Patio X)
local notation "Pm"=> Papers C (Patio D)
lemma colder (Q:Tone A X B Y)(p: Pl) (x:B→ℝ) : Oz Y (fun _:Unit=>1) ((frost Q x).read p) = Oz Y x (Q.read p):=by
    have he(f:poly A)(i:Patio X): Oz Y (fun _:Unit=>1) ((frost Q x).read (outer f i))= Oz Y x (Q.read (outer f i)):=by
        rw [Tone.spree,Tone.spree, Oce.antiquity,Oce.antiquity]; unfold frost; dsimp only; congr 1
        let H:=spool (Q.P * Matrix.of fun i (_:Unit)=> (x i:ℂ)); change MvPolynomial.aeval (fun _:Unit=> (↑(1:ℝ):ℂ)) (exchange H (Normal.milk Q.Q f))=MvPolynomial.aeval (fun i:B=>(x i:ℂ)) (exchange (spool Q.P) _)
        rw [reads_val,reads_val]; congr 2; ext1 i; unfold reads; simp_rw [Finsupp.linearCombination_apply,Finsupp.sum]; let K:=(Matrix.of fun i:B=>(fun _:Unit=>(x i:ℂ))); let t:=spool Q.P i
        have hs(X:Type)[Fintype X](x:X→₀ℂ)(L:X→ℂ): (∑ i∈ x.support,x i • L i)=∑ i,x i • L i:= sum_subset (subset_univ _) fun i _ hi=> by rw [Finsupp.notMem_support_iff.mp hi,zero_smul]
        rw [show (∑ j∈ (H i).support,_)= _ from hs _ (H i) fun _=> (1:ℝ), show (∑ j∈ t.support,_)= _ from hs B t fun j=>(x j:ℂ)]; unfold H; simp only [Tone.spi,Finset.univ_unique,Finset.sum_singleton,Complex.ofReal_one,smul_eq_mul,mul_one,Matrix.mul_apply,Matrix.of_apply,t,Tone.spi]
    rw [p.as_sum,map_sum,map_sum,map_sum,map_sum]; apply Finset.sum_congr rfl; intro i _; rw [show MvPolynomial.monomial i (MvPolynomial.coeff i p)= outer (MvPolynomial.monomial i 1) (MvPolynomial.coeff i p) from ?_,he]; rw [outmono,one_smul]
variable (T: Tone A X B Y)(S:Tone B Y C D)
variable (P:I→Papers A (Patio X))(w:I→ℝ)
variable {Q:Finset I}(m:I→Finset X)(e:I→Finset A)
variable (ht:∀ i∈ Q,P i∈ Ledger (m i) (e i) n j)(hp:∀ i∈Q,∀ k∈ Q,i ≠ k →Disjoint (m i) (m k)∧(∀ a∈m i,∀ b∈m k,T.V a b=0)∧∀ a∈e i,∀ b∈e k,T.Q.cov a b=0)
local notation "Λ"=> switch (pivotV T P w) S.P S.Q S.M S.V
include ht hp
lemma earnsV (W:I→ℝ)(x:C→ℝ)(p:Finset I)(he:p⊆Q): give W p • Oz D x (Λ p)=give (W*w) p • cetacea (fun i:Finset I=> Oz D (fun _:Unit=>1) ((frost (T.after S) x).read (∏ j∈i,P j))) p:=by
    let R:=frost (T.after S) x; let f(i:Finset I):=Oz D (fun _:Unit=>1) (R.read (∏ j∈i,P j)); let X(i:Finset I):=S.read (parties (pivotV T P w) i); have hf i (h:i ⊆p): (Oz D x) (X i)=give w i • f i:=by
        unfold f X R; rw [lends T S P w m e ht hp i (h.trans he),colder]; exact map_smul (taxer C D x) (give w i) _
    let R':=fun i:Finset I=>Oz D x (Λ i)
    have hx : f ∅=1:=by unfold f; rw [prod_empty,R.noneW,map_one]
    have hp': R' p=cetacea (fun i=>give w i • f i) p:=by
        apply MassiveQCD.Play.Chamber.only (fun i=>give w i • f i) R' p (?_) (?_) _ (Subset.refl _)
        · intro i hi; unfold parties R'; simp_rw [← map_prod,←map_sum]; exact (congr_arg _ (Vest.Tuck.noticed S (pivotV T P w) i)).trans (hf i hi)
        unfold R' switch; rw [cetacea]; change _= _; simp only [card_empty,sturdy,map_zero]
    have ht : give w p • cetacea f p= cetacea (fun i=>give w i • f i) p:=by
        apply MassiveQCD.Play.Chamber.only (fun i=>give w i • f i) (fun i=>give w i • cetacea f i) p (?_) (?_) _ (Subset.refl _); intro i _; rw [Tuck.richens, MassiveQCD.Play.Chamber.carries _ _ hx]; rw [cet]; simp
    change give _ _ • R' p=give _ _ • cetacea f p; rw [hp',← ht,smul_smul, show give W p*give w p=give (W*w) p from by simp [give, prod_mul_distrib]]
end Fold
end YM.Arise.Count
#print axioms YM.Arise.Count.earnsV
