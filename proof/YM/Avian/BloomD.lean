import YM.Avian.Nest
/-! Coordinates receipts at growing sides. Local weighted startup input Priced. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall.Jewels
open Function Lattice RG Source Wilson Filter Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator Classical
open Cylinder QCD QCD.Lat QCD.Grass UV Patria Patria.Depth Patria.Exposure Patria.Hub Poised Poised.Plans Poised.Plans.Stamp Intag MassFields
open Lining Lining.Temper Tawny Cast Patria.Rolls Patria.Rolls.Attain Seals
variable {S:Scheme}{R:Side}{i N:ℕ}(A:Run S N R 6)(T:SourceRead.TaperHol)(sym:RawSym)(B:Bore 8)(hT:Rubric sym B)(F:PatchMix 8)(hf:OrderMix A T sym B (i:=0) F)
variable (x:ℂ)(Q:RawTensor x 8)
local notation "c"=> S.side R N
local notation "M★"=> S.side R 0
local notation "W'"=> A.density 0
local notation "Sχ"=> skyU A B F x Q
local notation "Yχ"=> vine A B F x Q
local notation "Vχ"=> divine A B F x Q
variable (hA:A.Actual)(hI:∀ t b i, Lat.Invariant (B t b i))(i j:Axis)(C:Axis→Axis→Label 10)(he:∀ i j, Tally T 0 (C i j) (A.density 0) (trolley A (vine A B F x Q i j) (shelV j) 0 0))
local notation "cR"=>path A B F x Q
local notation "Aχ"=>castG A B F x Q
variable (D:RawVec 10)(hD:∀ j: Axis,D.val j=∑ i:Axis,C i j)
-- pay uniform shape at S.Radius.Str tape. Permit generosity post.
variable (P:BudgetPoint)(n m:ℕ)(t a:ℝ)(hN:10 ≤ P.order)(hm:6 ≤ n)(hC:2 < m)(ht:0<t)(hQ:∀ i j:Axis, Tutor 0 P (Canvas.foil (A.density 0) ((path A B F x Q i j 0))) t n m a)
local notation "FK" i:arg j:arg=> Canvas.foil W' ((cR i j 0))
include hD he hf hA hT
lemma totals : Tally T 0 (D.val j) W' (castG A B F x Q j):=by
     let f(i:Axis):= stunt i ((cR i j 0)); have hx(i):Tally T 0 (C i j) W' (f i):=by unfold f; rw[← vert1 A T sym B hT F hf x Q hA]; exact he i j
     rw [hD,vert0 A T sym B hT F hf x Q hA]; change Tally T 0 _ _ (∑ i,f i); simp only[Fin.sum_univ_four]; exact Needle.totalY _ _ _ _ _ _ _ (Needle.totalY _ _ _ _ _ _ _ (Needle.totalY _ _ _ _ _ _ _ (hx 0) (hx 1)) (hx 2)) (hx 3)
include hQ hN hI hC hm ht
local notation "G"=>Canvas.foil W' (Aχ j)
open Pane BendR UV.Free KeysP Clifford
lemma nobledP (u v:Fiber)(j:Axis)(p:Flavor 6)(k l:Axis): let f:=Canvas.foil W' (Aχ j); Allow P Gpick f P.order ((4:ℝ)*(4*2^P.power*(a/t^2))) ∧ SungP f∧ river2 k l p u v Gpick f=0∧river1 k p u v f=0:=by -- t^ -2 replace
       intro f; let E:=Gpick; let g(i):= Canvas.foil W' (stunt i (cR i j 0)); have hs:P.order≥1:=by omega
       have hΨ(x:Cover): march x W'=W':=by rw [pier A hA (Nat.zero_le _)]; exact Depth.first A 0 (Nat.zero_le _) x
       have hunit:∀ᶠ V in 𝓝 (1:Grid M★), IsUnit (W' V):= (he 0 j).unit
       let b:=4*2^P.power*(a/t^2); have hy(i:Axis):Allow P E (g i) P.order b:= merve P E _ _ (allowance _ _ _ (hQ i j) ht (by omega) hC hs) hs i hΨ hunit -- args
       have hU: SungP f:=by
              apply treated _ _ (lived A hA); rw [vert0 A T sym B hT F hf x Q hA]; intro k U; rw[Finset.sum_apply,map_sum, Finset.sum_apply]; refine sum_congr rfl fun i _=>?_
              have hp(t:Cover): march t ((cR i j) 0)= ⇑((cR i j) (0+t)):= Depth.axial A hA (skyU A B F x Q i j) (shelS i j) (fun _ _=>hT.advances ..) t 0 (Nat.zero_le _)
              unfold stunt; let C₀:= ((cR i j) (0+step i)); let C₁:= ((cR i j) (0+-step i)); rw[hp,hp]; change slots 6 k ((↑(1/2:ℝ):ℂ) • (C₀ (Lattice.gauge k U) - C₁ (Lattice.gauge k U)))= (1/2:ℝ) • (C₀ U-C₁ U); rw [map_smul,map_sub,show slots _ _ _= _ from signs A B F x Q i j hI _ k U,show slots _ _ _= _ from signs A B F x Q i j hI _ k U]; rfl
       have hz:f=∑ i:Axis,g i:=by funext V; unfold f Canvas.foil; rw [vert0 A T sym B hT F hf x Q hA, Finset.sum_apply,mul_sum]; rw [Finset.sum_apply]
       have hN(i):river1 k p u v (g i)=0 ∧ river2 k l p u v Gpick (g i)=0:=by
            have h:= nixes ((cR i j) 0) E hs k l p u v i _ hunit hΨ (hQ i j).smooth; exact ⟨h.1,h.2.1⟩
       refine ⟨?_,hU,?_,?_⟩
       · rw [hz]; have h:= sumsG P E g univ (fun _=> b) (fun i _=>hy i) hs; simpa [b,Axis] using h
       · rw [hz,vote2_sum E hs _ _ _ _ _ g _ (fun i _=> (hy i).alive)]; exact sum_eq_zero fun i _=> (hN _).2
       rw[hz]; simp only[Fin.sum_univ_four,race1,fun i=>(hN i).1,add_zero]
end YM.Massive.Patria.Gall.Jewels
#print axioms YM.Massive.Patria.Gall.Jewels.nobledP
